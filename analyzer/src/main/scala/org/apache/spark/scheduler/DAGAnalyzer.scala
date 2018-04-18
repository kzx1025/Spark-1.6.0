package org.apache.spark.scheduler

import java.lang.reflect.Field
import java.util
import java.util.Properties
import java.util.concurrent.atomic.AtomicInteger

import cn.edu.hust.grid.deca._
import cn.edu.hust.grid.soot.Utils
import cn.edu.hust.grid.soot.optimize._
import org.apache.commons.lang.SerializationUtils
import org.apache.spark.rdd._
import org.apache.spark.{DecaContext, NarrowDependency, TaskContext}
import soot.jimple.internal.{JInvokeStmt, JSpecialInvokeExpr}
import soot.{SootClass, SootField}

import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.collection.mutable.Queue

/**
  * Created by iceke on 17/10/17.
  */
object DAGAnalyzer {

  private val nextJobId = new AtomicInteger(0)

  private val allPhasesMap = new mutable.HashMap[Phase, Stage]

  private var allPhases = List[Phase]()

  //sparkRDD最外层的类
  var maxOuterClassName: String = null

  //提交的应用类名
  var appName: String = null


  //存储由cacheRDD为终点构造的Phase,用原phase id查询
  val cachePhasesMap = new mutable.HashMap[Phase, java.util.List[CachePhase]]

  //存储某个phase中互相join的两个RDD
  val joinRDDFuncMap = new mutable.HashMap[String, (Phase, String)]

  //闭包对象
  var outerObject: Object = null

  var sootContext: Context = null


  protected val localProperties = new InheritableThreadLocal[Properties] {
    override protected def childValue(parent: Properties): Properties = {
      // Note: make a clone such that changes in the parent properties aren't reflected in
      // the those of the children threads, which has confusing semantics (SPARK-10563).
      SerializationUtils.clone(parent).asInstanceOf[Properties]
    }

    override protected def initialValue(): Properties = new Properties()
  }


  def formPhase[T, U](finalRDD: RDD[T],
                      func: (TaskContext, Iterator[T]) => U,
                      partitions: Seq[Int],
                      resultHandler: (Int, U) => Unit,
                      dc: DecaContext): mutable.Map[Int, java.util.List[(String, String)]] = {
    val properties = localProperties.get
    val jobId = nextJobId.getAndIncrement()
    val maxPartitions = finalRDD.partitions.length
    partitions.find(p => p >= maxPartitions || p < 0).foreach { p =>
      throw new IllegalArgumentException(
        "Attempting to access a non-existent partition: " + p + ". " +
          "Total number of partitions: " + maxPartitions)
    }
    val callSite = dc.getCallSite()
    val stageScheduler = new StageScheduler(dc)
    val partitions_2 = partitions.toArray[Int]
    val finalStage = stageScheduler.newResultStage(finalRDD.asInstanceOf[RDD[_]],
      func.asInstanceOf[(TaskContext, Iterator[_]) => _],
      partitions_2, jobId, callSite)


    val finalPhase = new Phase(finalStage.id, finalStage.rdd, List[Phase]())
    allPhasesMap(finalPhase) = finalStage
    allPhases = finalPhase +: allPhases

    //构建phase之间的父子关系
    handleStage(finalPhase, finalStage, stageScheduler)

    //allPhasesMap.foreach(println)

    for (phase <- allPhases.sortBy(_.id)) {
      //处理每个cacheRDD
      handleCacheRDDFromChain(phase)
    }
    sootContext = new Context(preload = false, classpath = System.getProperty("java.class.path"))
    val resultFuncTuple = getResultFunc(func)
    TransformCollection.clear()

    val allStageKeyValueTypeJsonMap = new mutable.HashMap[Int, java.util.List[(String, String)]].empty


    for (phase <- allPhases) {
      TimeRecorder.jobID = jobId
      sootContext = new Context(preload = false, classpath = System.getProperty("java.class.path"))
      val fusionStart = System.currentTimeMillis()
      val fusionClass = fuseIter(phase, resultFuncTuple)
      val fusionEnd = System.currentTimeMillis()
      TimeRecorder.fusionTime = fusionEnd - fusionStart
      TimeRecorder.stageID = fusionClass.getName
      //这个输出不能注释！！！！
      sootContext.writeOutput(fusionClass)
      ///**
      // if(fusionClass.getName.contains("ShuffleFunc0")) {
      val localNewSiteInfos = PointerAnalyzer.transform(sootContext, fusionClass, phase)

      //只处理shufflemapstage,或者resultstage前面有shufflemapstage的情况
      if (localNewSiteInfos.size() != 0 || phase.kind == "Result") {
        //如果有那么就只有一个 local shuffle 类型的 new site info
        var fieldInfoMap: mutable.Map[SootField, FieldInfo] = new mutable.HashMap[SootField, FieldInfo].empty
        if (localNewSiteInfos.size() != 0) {
          val shuffleLocalNewSiteInfos = localNewSiteInfos.filter(_.genericType == "shuffle")
          if (shuffleLocalNewSiteInfos.nonEmpty) {
            fieldInfoMap = shuffleLocalNewSiteInfos.get(0).fieldInfoMap
          }
        }
        if (fieldInfoMap.nonEmpty || phase.kind == "Result") {
          val optionInfoJsonList = new util.ArrayList[(String, String)]()
          phase.kind match {
            case "Shuffle" =>
              if (phase.getParents().nonEmpty) {
                val preStageId: Int = phase.id - 1
                val (optionName, typeInfo) = ("read", allStageKeyValueTypeJsonMap(preStageId).filter(_._1 == "write").head._2)
                optionInfoJsonList.add((optionName, typeInfo))
              }
              val stageKeyValueTypeInfoJson = KeyValueUtil.putKeyAndValueType(fieldInfoMap)
              val (optionName, typeInfo): (String, String) = ("write", stageKeyValueTypeInfoJson)
              optionInfoJsonList.add((optionName, typeInfo))
              allStageKeyValueTypeJsonMap(phase.id) = optionInfoJsonList
            case "Result" =>
              if (phase.getParents().nonEmpty) {
                val preStageId: Int = phase.id - 1
                val (optionName, typeInfo) = ("read", allStageKeyValueTypeJsonMap(preStageId).filter(_._1 == "write").head._2)
                optionInfoJsonList.add((optionName, typeInfo))
                allStageKeyValueTypeJsonMap(phase.id) = optionInfoJsonList
              }
            case other =>
              throw OptimizeException(s"unknown type $other")
          }
        }
      }


//      // println(sootContext.callGraph.toString)
//      //这时候sootContext已经是全量加载了
//      //裁剪需要拆解的类,排除掉原生类，Object类
//      val needTailorClasses: java.util.List[SootClass] = new util.ArrayList[SootClass]
//      for (localNewSiteInfo: LocalNewSiteInfo <- localNewSiteInfos) {
//        val fieldInfoMap = localNewSiteInfo.fieldInfoMap
//        val tempClasses = fieldInfoMap.filter(!_._2.specificClass.getName.equals("double")).filter(!_._2.specificClass.getName.equals("int"))
//          .filter(!_._2.specificClass.getName.equals("float")).filter(!_._2.specificClass.getName.equals("long")).filter(!_._2.specificClass.getName.equals("java.lang.Object"))
//          .map(s => s._2.specificClass).toList
//        needTailorClasses.addAll(tempClasses)
//        needTailorClasses.add(localNewSiteInfo.topClass)
//      }
//
//      val tailorStart = System.currentTimeMillis()
//      Tailor.transformClasses(sootContext, needTailorClasses)
//      val tailorEnd = System.currentTimeMillis()
//      TimeRecorder.tailorTime = tailorEnd - tailorStart
//
//      AutoLoad.record(sootContext)
//
//      val classifyStart = System.currentTimeMillis()
//      NewClassfier.transform(sootContext, localNewSiteInfos)
//      val classifyEnd = System.currentTimeMillis()
//      TimeRecorder.classifyTime = classifyEnd - classifyStart
//
//      val funcClass = PointerAnalyzer.finalFuncClass
//      Shifter.transform(localNewSiteInfos, funcClass, sootContext)
//
//      //  }
//      //**/
//      // sootContext.writeOutput()
//
//      val packStart = System.currentTimeMillis()
//      AutoLoad.packClasses(TimeRecorder.writeJimpleNum)
//      val packEnd = System.currentTimeMillis()
//      TimeRecorder.packTime = (packEnd - packStart)
//
//      val loadStart = System.currentTimeMillis()
//      Tailor.removeUnusedClasses(sootContext)
//      AutoLoad.loadClasses()
//      val loadEnd = System.currentTimeMillis()
//      TimeRecorder.loadClassTime = loadEnd - loadStart
//
      TimeRecorder.record()

    }
    allStageKeyValueTypeJsonMap
  }


  def clear(): Unit = {
    DAGAnalyzer.cachePhasesMap.clear()
    DAGAnalyzer.allPhasesMap.clear()

    DAGAnalyzer.allPhases = List[Phase]()

    DAGAnalyzer.joinRDDFuncMap.clear()

    DAGAnalyzer.outerObject = null
    DAGAnalyzer.sootContext = null
    IteratorFusion.filterFuncs.clear()
    IteratorFusion.flatMapFuncs.clear()
    IteratorFusion.mapValuesFuncs.clear()
    // ShuffleData.dataType = null

    Utils.deleteDirectory("sootOutput")

  }


  /**
    * 迭代器融合操作
    *
    * @param phase
    */
  def fuseIter(phase: Phase, resultFuncTuple: (String, ResultType)): SootClass = {

    var fusionClass: SootClass = null
    if (allPhasesMap(phase).isInstanceOf[ResultStage]) {
      phase.kind = "Result"

      if (cachePhasesMap.contains(phase)) {
        //这里需要划分为两个子Phase
        val cacheWritePhase = cachePhasesMap(phase).get(0)
        val cacheReadPhase = cachePhasesMap(phase).get(1)
        val cacheWriteFuncs = loadRDDFunc(cacheWritePhase, sootContext)
        val cacheReadFuncs = loadRDDFunc(cacheReadPhase, sootContext)

        if (cacheWritePhase.dataSource.equals("hadoop") || cacheReadPhase.dataSource.equals("hadoop")) {
          phase.dataSource = "hadoop"
        }
        //去除与cacheWrite重复的RDDFunc
        if (cacheReadFuncs.nonEmpty) {
          cacheReadFuncs.dequeue()
        }

        if (resultFuncTuple != null) {
          val resultFuncClass = sootContext.sootClass(resultFuncTuple._1)
          //sootContext.writeOutput(resultFuncClass)
          fusionClass = IteratorFusion.transformResultPhase(sootContext, resultFuncClass, phase,
            cacheWriteFuncs, cacheReadFuncs, resultFuncTuple._2)
        } else {
          //暂时无法处理的resultFunc
          fusionClass = IteratorFusion.transformResultPhase(sootContext, null, phase,
            cacheWriteFuncs, cacheReadFuncs, null)
        }


      } else {
        loadRDDFunc(phase, sootContext)
        if (resultFuncTuple != null) {
          val resultFuncClass = sootContext.sootClass(resultFuncTuple._1)
          fusionClass = IteratorFusion.transformResultPhase(sootContext, resultFuncClass, phase, resultFuncTuple._2)
        } else {
          //暂时无法处理的resultFunc
          fusionClass = IteratorFusion.transformResultPhase(sootContext, null, phase, null)
        }

      }

    } else {
      //ShuffleMapStage
      phase.kind = "Shuffle"
      //shuffleFunc暂不使用
      //val shuffleFunc = getFuncByShuffleStage(phase, sootContext)
      if (cachePhasesMap.contains(phase)) {
        //这里需要划分为两个子Phase
        val cacheWritePhase = cachePhasesMap(phase).get(0)
        val cacheReadPhase = cachePhasesMap(phase).get(1)
        val cacheWriteFuncs = loadRDDFunc(cacheWritePhase, sootContext)
        val cacheReadFuncs = loadRDDFunc(cacheReadPhase, sootContext)

        if (cacheWritePhase.dataSource.equals("hadoop") || cacheReadPhase.dataSource.equals("hadoop")) {
          phase.dataSource = "hadoop"
        }

        if (cacheReadFuncs.nonEmpty) {
          cacheReadFuncs.dequeue()
        }
        fusionClass = IteratorFusion.transformShufflePhase(sootContext, phase, cacheWriteFuncs, cacheReadFuncs)

      } else {
        loadRDDFunc(phase, sootContext)
        fusionClass = IteratorFusion.transformShufflePhase(sootContext, phase)
      }

    }
    sootContext.fusionClassList.clear()
    fusionClass
  }


  private def loadRDDFunc(phase: Phase, sootContext: Context): mutable.Queue[String] = {
    val rddStack = getRDDStack(phase)
    val fusionClassQueue: mutable.Queue[String] = mutable.Queue.empty[String]

    while (!rddStack.empty()) {
      val analyzeRDD = rddStack.pop()
      println("!!!!!rdd的create方式" + analyzeRDD.getCreationSite)
      val methodName = analyzeRDD.getCreationSite.split(" ")(0)

      analyzeRDD match {
        case _: MapPartitionsRDD[_, _] =>
          val funcName = getFuncByMapRDD(analyzeRDD, methodName)
          if (funcName != null) {
            if (methodName.equals("filter")) {
              IteratorFusion.filterFuncs.+=(funcName)
            }
            if (methodName.equals("mapValues")) {
              IteratorFusion.mapValuesFuncs.+=(funcName)
            }
            if (methodName.equals("flatMap")) {
              IteratorFusion.flatMapFuncs.add(funcName)
            }
            //            if (methodName.equals("mapPartitions") || methodName.equals("mapPartitionsWithIndex")) {
            //              IteratorFusion.mapPartitionsFuncs.add(funcName)
            //            }
            sootContext.loadClass(funcName, true)
            val tempClass = sootContext.sootClass(funcName)
            sootContext.fusionClassList.enqueue(funcName)
            fusionClassQueue.enqueue(funcName)
            if (maxOuterClassName == null) {
              if (!funcName.contains("SparkContext")) {
                val index = funcName.indexOf('$')
                val appClassName = funcName.substring(0, index)
                maxOuterClassName = appClassName
              }
            }

          }
        case _: HadoopRDD[_, _] =>
          //ignore
          val funcName = getFuncByHadoopRDD(analyzeRDD)
          phase.dataSource = "hadoop"
          println(funcName)
        case _: ShuffledRDD[_, _, _] =>
          //ResultStage前面一个阶段是ShuffleStage
          fusionClassQueue.enqueue(null)
        //暂不处理
        case _: CoGroupedRDD[_] =>
          println("!!!是goGroupedRDD,不作处理，重要的是goGroupRDD前面两个RDD的func处理")
          fusionClassQueue.enqueue(null)

        case _ =>
      }

    }
    fusionClassQueue
  }


  /**
    * 为cache的RDD生成新的Phase,将RDD链划分成两个部分
    * 衍生Phase的id等于原Phase的id
    *
    * @param phase
    */
  private def handleCacheRDDFromChain(phase: Phase): Unit = {
    var writeCachePhase: CachePhase = null
    var readCachePhase: CachePhase = null
    var tempRDD: RDD[_] = null

    val finalRDD = phase.finalRDD
    //广度遍历一个phase中的RDD链
    val rddsQueue: Queue[RDD[_]] = new Queue[RDD[_]]()
    rddsQueue.enqueue(finalRDD)

    while (rddsQueue.nonEmpty) {
      tempRDD = rddsQueue.dequeue()
      //判断该RDD是否被cache
      if (tempRDD.getStorageLevel.useMemory) {
        writeCachePhase = new CachePhase(phase.id, tempRDD, phase.getParents())
        writeCachePhase.isWriteCache = true
        readCachePhase = new CachePhase(phase.id, finalRDD, phase.getParents())
        readCachePhase.isWriteCache = false
        readCachePhase.startRDD = tempRDD
      }
      val narrowDependencies = tempRDD.dependencies.filter(_.isInstanceOf[NarrowDependency[_]])
      val narrowParents = narrowDependencies.map(_.rdd).toList

      for (t <- narrowParents) {
        rddsQueue.enqueue(t)
      }

    }
    if (writeCachePhase != null || readCachePhase != null) {
      writeCachePhase.startRDD = tempRDD
      val cachePhaseList = new util.ArrayList[CachePhase]()
      cachePhaseList.add(writeCachePhase)
      cachePhaseList.add(readCachePhase)

      cachePhasesMap(phase) = cachePhaseList
    }


  }


  private def getRDDStack(phase: Phase): util.Stack[RDD[_]] = {
    val rddStack = new util.Stack[RDD[_]]
    val finalRDD = phase.finalRDD
    val rddsQueue: Queue[RDD[_]] = new Queue[RDD[_]]()
    rddsQueue.enqueue(finalRDD)


    while (rddsQueue.nonEmpty) {
      val tempRDD = rddsQueue.dequeue()
      rddStack.push(tempRDD)
      if (phase.isInstanceOf[CachePhase] && phase.asInstanceOf[CachePhase].startRDD == tempRDD) {
        //startRDD 已经记录了这个stage最开始的rdd，如果相等了 说明遍历完了。
        //这之后cacheReadPhase已经去除了Cache的那个RDD,不会有cacheWrite重复
        return rddStack
      }
      //判断该RDD是否被cache

      val narrowDependencies = tempRDD.dependencies.filter(_.isInstanceOf[NarrowDependency[_]])
      val narrowParents = narrowDependencies.map(_.rdd).toList
      if (narrowParents.size > 1) {
        println("不是单线RDD链, 目测存在join操作")
      }
      if (tempRDD.isInstanceOf[CoGroupedRDD[_]] && narrowDependencies.size == 2) {
        println("CoGroupedRDD的父RDD只入队一个，另一个用全局map记录")
        val aRDD = narrowDependencies.get(0).rdd
        val bRDD = narrowDependencies.get(1).rdd
        if (aRDD.isInstanceOf[MapPartitionsRDD[_, _]]) {

          rddsQueue.enqueue(aRDD)
          val aFuncString = getFuncByMapRDD(aRDD, aRDD.getCreationSite.split(" ")(0))
          if (bRDD.isInstanceOf[MapPartitionsRDD[_, _]]) {
            val bFuncString = getFuncByMapRDD(bRDD, bRDD.getCreationSite.split(" ")(0))
            joinRDDFuncMap(aFuncString) = (phase, bFuncString)
          } else {
            joinRDDFuncMap(aFuncString) = (phase, null)

          }
        } else {
          rddsQueue.enqueue(bRDD)
          if (bRDD.isInstanceOf[MapPartitionsRDD[_, _]]) {
            val bFuncString = getFuncByMapRDD(bRDD, bRDD.getCreationSite.split(" ")(0))
            joinRDDFuncMap(bFuncString) = (phase, null)
          } else {
            println("两个都不是mapRDD，啥也不用做")
          }
        }

      } else if (narrowDependencies.size > 1) {
        throw OptimizeException("不是coGroupedRDD，有两个父RDD暂时不能处理！！！！！！！")
      } else {
        for (t <- narrowParents) {
          rddsQueue.enqueue(t)
        }
      }
    }


    rddStack
  }


  /**
    * 构建phase之间的父子关系
    *
    * @param phase
    * @param stage
    * @param dag
    */
  private def handleStage(phase: Phase, stage: Stage, dag: StageScheduler): Unit = {
    val missing = dag.getMissingParentStages(stage).sortBy(_.id)

    if (missing.nonEmpty) {
      for (parent <- missing) {
        val parentPhase = new Phase(parent.id, parent.rdd, List[Phase]())
        allPhasesMap(parentPhase) = parent
        allPhases = parentPhase +: allPhases

        //更新decaParentPhases
        var parentPhases = phase.getParents()
        parentPhases = parentPhase +: parentPhases
        phase.setParents(parentPhases)

        handleStage(parentPhase, parent, dag)
      }

    }

  }

  class ResultType() {}

  case class NoHandle() extends ResultType

  case class IsReduce() extends ResultType

  case class IsForEach() extends ResultType

  def getResultFunc[T, U](func: (TaskContext, Iterator[T]) => U): (String, ResultType) = {

    def getResultType: ResultType = {
      for (field <- func.getClass.getDeclaredFields) {
        if (field.asInstanceOf[Field].getName.equals("processPartition$1")) {
          return IsReduce()
        }
        if (field.asInstanceOf[Field].getName.equals("cleanedFunc$1")) {
          var fField = func.getClass.getDeclaredField("cleanedFunc$1")
          fField.setAccessible(true)
          val cleanedFunc = fField.get(func)
          if (cleanedFunc.getClass.getDeclaredFields.exists(_.getName.equals("cleanF$5"))) {
            return NoHandle()
          }
        }
      }
      NoHandle()
    }

    val resultType = getResultType
    resultType match {
      case _: IsReduce =>
        try {
          var funcField = func.getClass.getDeclaredField("processPartition$1")
          funcField.setAccessible(true)
          val processPartition = funcField.get(func)
          funcField = processPartition.getClass.getDeclaredField("cleanF$8")
          funcField.setAccessible(true)
          val cleanF = funcField.get(processPartition)
          val resultFuncName = cleanF.getClass.getName
          (resultFuncName, resultType)
        } catch {
          case _: Exception =>
            println("getResultFunc failed")
            null
        }
      case _: IsForEach =>
        try {
          var fField = func.getClass.getDeclaredField("cleanedFunc$1")
          fField.setAccessible(true)
          val cleanFunc = fField.get(func)
          fField = cleanFunc.getClass.getDeclaredField("cleanF$5")
          fField.setAccessible(true)
          val cleanF = fField.get(cleanFunc)
          val resultFuncName = cleanF.getClass.getName
          (resultFuncName, resultType)
        } catch {
          case _: Exception =>
            println("getResultFunc failed")
            null
        }
      case _: NoHandle =>
        null
      case _ =>
        null
    }


  }


  /**
    * 暂时只处理reduce算子，其他算子略过
    *
    * @param analyzeRDD
    * @return
    */
  private def getFuncByMapRDD(analyzeRDD: RDD[_], methodName: String): String = {
    var funcName: String = null
    val cleanedFName = "cleanedF"
    val cleanFName = "cleanF"

    def getFuncFromMethod(analyzeRDD: RDD[_], cleanFName: String, writeJimple: Boolean = false): String = {
      val actualRDD = analyzeRDD.asInstanceOf[MapPartitionsRDD[_, _]]
      var fField = actualRDD.getClass.getDeclaredField("f")
      fField.setAccessible(true)
      val f = fField.get(actualRDD)
      val fFields = f.getClass.getDeclaredFields
      if (writeJimple) {
        sootContext.loadClass(f.getClass.getName)
        val fSootClass = sootContext.sootClass(f.getClass.getName)
        sootContext.writeJimple(fSootClass)
      }
      for (field <- fFields) {
        if (field.getName.contains(cleanFName)) {
          fField = field
        }
      }
      fField.setAccessible(true)
      val cleanF = fField.get(f)
      funcName = cleanF.getClass.getName
      val cleanFields = cleanF.getClass.getDeclaredFields
      for (cleanField <- cleanFields) {
        if (cleanField.getName.contains("$outer")) {
          cleanField.setAccessible(true)
          val outerObject = cleanField.get(cleanF)
          this.outerObject = outerObject

        }
      }
      sootContext.writeJimple(sootContext.sootClass(funcName))
      funcName
    }

    methodName match {
      case "saveAsTextFile" =>
        null
      case "textFile" =>
        null
      case "retag" =>
        null
      case "treeAggregate" =>
        handleTreeAggregate(analyzeRDD)
      case "mean" =>
        getFuncFromMethod(analyzeRDD, cleanedFName)
      case "mapPartitions" =>
        getFuncFromMethod(analyzeRDD, cleanedFName)
        IteratorFusion.mapPartitionsFuncs.add(funcName)
        funcName
      case "mapPartitionsWithIndex" =>
        getFuncFromMethod(analyzeRDD, cleanedFName)
        IteratorFusion.mapPartitionsFuncs.add(funcName)
        funcName
      case _ =>
        getFuncFromMethod(analyzeRDD, cleanFName)
    }
    //        if (methodName.equals("saveAsTextFile")) {
    //          // 这些action算子暂时无法处理
    //          null
    //        } else if (methodName.equals("textFile")) {
    //          null
    //        } else if (methodName.equals("treeAggregate")) {
    //          //处理mllib的特殊算子
    //          handleTreeAggregate(analyzeRDD)
    //        } else if (methodName.equals("mean")) {
    //          //TODO 还没处理mean
    //          val actualRDD = analyzeRDD.asInstanceOf[MapPartitionsRDD[_, _]]
    //          var fField = actualRDD.getClass.getDeclaredField("f")
    //          fField.setAccessible(true)
    //          val f = fField.get(actualRDD)
    //          val fFields = f.getClass.getDeclaredFields
    //          for (field <- fFields) {
    //            if (field.getName.contains("cleanedF")) {
    //              fField = field
    //            }
    //          }
    //          fField.setAccessible(true)
    //          val cleanF = fField.get(f)
    //          funcName = cleanF.getClass.getName
    //          val cleanFields = cleanF.getClass.getDeclaredFields
    //          for (cleanField <- cleanFields) {
    //            if (cleanField.getName.contains("$outer")) {
    //              cleanField.setAccessible(true)
    //              val outerObject = cleanField.get(cleanF)
    //              this.outerObject = outerObject
    //
    //            }
    //          }
    //          sootContext.writeJimple(sootContext.sootClass(funcName))
    //          funcName
    //        } else if (methodName.equals("mapPartitions") || methodName.equals("mapPartitionsWithIndex")) {
    //          //TODO 暂时先不处理mapPartitions算子
    //          val actualRDD = analyzeRDD.asInstanceOf[MapPartitionsRDD[_, _]]
    //          var fField = actualRDD.getClass.getDeclaredField("f")
    //          fField.setAccessible(true)
    //          val f = fField.get(actualRDD)
    //          val fFields = f.getClass.getDeclaredFields
    //          for (field <- fFields) {
    //            if (field.getName.contains("cleanedF")) {
    //              fField = field
    //            }
    //          }
    //          fField.setAccessible(true)
    //          val cleanF = fField.get(f)
    //          funcName = cleanF.getClass.getName
    //          val cleanFields = cleanF.getClass.getDeclaredFields
    //          for (cleanField <- cleanFields) {
    //            if (cleanField.getName.contains("$outer")) {
    //              cleanField.setAccessible(true)
    //              val outerObject = cleanField.get(cleanF)
    //              this.outerObject = outerObject
    //
    //            }
    //          }
    //          sootContext.writeJimple(sootContext.sootClass(funcName))
    //          IteratorFusion.mapPartitionsFuncs.add(funcName)
    //          funcName
    //        } else if (methodName.equals("retag")) {
    //          //retag算子不作处理
    //          null
    //        } else {
    //          val actualRDD = analyzeRDD.asInstanceOf[MapPartitionsRDD[_, _]]
    //          var fField = actualRDD.getClass.getDeclaredField("f")
    //          fField.setAccessible(true)
    //          val f = fField.get(actualRDD)
    //          val fFields = f.getClass.getDeclaredFields
    //          for (field <- fFields) {
    //            if (field.getName.contains("cleanF")) {
    //              fField = field
    //            }
    //          }
    //          fField.setAccessible(true)
    //          val cleanF = fField.get(f)
    //          funcName = cleanF.getClass.getName
    //          val cleanFields = cleanF.getClass.getDeclaredFields
    //          for (cleanField <- cleanFields) {
    //            if (cleanField.getName.contains("$outer")) {
    //              cleanField.setAccessible(true)
    //              val outerObject = cleanField.get(cleanF)
    //              this.outerObject = outerObject
    //
    //            }
    //          }
    //          sootContext.writeJimple(sootContext.sootClass(funcName))
    //          funcName
    //        }
  }

  private def getFuncFromMapParitionWithIndex(funcName: String): String = {
    val fakeClass = sootContext.sootClass(funcName)
    val applyMethod = IteratorFusion.getApplyMethod(fakeClass, sootContext)
    var realFuncClass: String = null
    for (unit <- applyMethod.getActiveBody.getUnits) {
      if (unit.isInstanceOf[JInvokeStmt]) {
        val invokeStmt = unit.asInstanceOf[JInvokeStmt]
        if (invokeStmt.getInvokeExpr.isInstanceOf[JSpecialInvokeExpr]) {
          val invokeExpr = invokeStmt.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr]
          if (invokeExpr.getMethod.getName.equals("<init>")) {
            realFuncClass = invokeExpr.getBase.getType.toString
          }
        }

      }
    }
    realFuncClass
  }

  private def handleTreeAggregate(analyzeRDD: RDD[_]): String = {
    var funcName: String = null
    val actualRDD = analyzeRDD.asInstanceOf[MapPartitionsRDD[_, _]]
    var fField = actualRDD.getClass.getDeclaredField("f")
    fField.setAccessible(true)
    val f = fField.get(actualRDD)
    val fFields = f.getClass.getDeclaredFields
    for (field <- fFields) {
      if (field.getName.contains("cleanedF")) {
        fField = field
      } else if (field.getName.contains("cleanF")) {
        fField = field
        fField.setAccessible(true)
        val cleanF = fField.get(f)
        funcName = cleanF.getClass.getName
        val cleanFields = cleanF.getClass.getDeclaredFields
        for (cleanField <- cleanFields) {
          // 处理闭包
          if (cleanField.getName.contains("$outer")) {
            cleanField.setAccessible(true)
            val outerObject = cleanField.get(cleanF)
            this.outerObject = outerObject
          }
        }

        return funcName
      }
    }
    fField.setAccessible(true)
    val cleanF = fField.get(f)
    funcName = cleanF.getClass.getName
    val cleanFields = cleanF.getClass.getDeclaredFields
    var isAggregate: Boolean = false
    sootContext.writeJimple(sootContext.sootClass(funcName))
    for (field <- cleanFields) {
      //treeAggregate第一步
      if (field.getName.contains("aggregatePartition")) {
        fField = field
        isAggregate = true
      } else if (field.getName.contains("curNumPartition")) {
        fField = field
      }
    }
    if (!isAggregate) {
      //treeAggregate算子里的mapPartitionWithIndex的操作
      fField.setAccessible(true)
      val curNumPartion: Int = fField.get(cleanF).asInstanceOf[Int]
      val realFuncClassName = getFuncFromMapParitionWithIndex(funcName)
      this.outerObject = cleanF
      realFuncClassName

    } else {
      fField.setAccessible(true)
      val aggregate = fField.get(cleanF)
      val aggregateFuncName = aggregate.getClass.getName
      val aggregateFields = aggregate.getClass.getDeclaredFields
      var seqField: Field = null
      var combField: Field = null
      var outerField: Field = null
      for (field <- aggregateFields) {
        if (field.getName.contains("cleanSeqOp")) {
          seqField = field
        } else if (field.getName.contains("cleanCombOp")) {
          combField = field
        } else if (field.getName.contains("outer")) {
          outerField = field
        }
      }
      seqField.setAccessible(true)
      val seq = seqField.get(aggregate)
      val seqName = seq.getClass.getName
      combField.setAccessible(true)
      val comb = combField.get(aggregate)
      val combName = comb.getClass.getName
      outerField.setAccessible(true)
      val outer = outerField.get(aggregate)
      val outerFields = outer.getClass.getDeclaredFields

      var zeroValueField: Field = null
      for (field <- outerFields) {
        if (field.getName.contains("zeroValue")) {
          zeroValueField = field
        }
      }
      zeroValueField.setAccessible(true)
      val zeroValue = zeroValueField.get(outer)
      val zeroValueTypeName = zeroValue.getClass.getName
      MLDataProduce.typeName = zeroValueTypeName

      //这里不考虑combName
      val treeInfo = new TreeAggregateInfo(zeroValueTypeName, seqName, combName)
      IteratorFusion.treeAggregateMap.put(seqName, treeInfo)

      seqName
    }
  }

  private def getFuncByShuffleStage(phase: Phase, context: Context): ShuffleFunc = {
    val shuffleStage = allPhasesMap(phase).asInstanceOf[ShuffleMapStage]
    val dep = shuffleStage.shuffleDep
    val aggregator = dep.aggregator
    val xField = aggregator.getClass.getDeclaredField("x")
    xField.setAccessible(true)
    val x = xField.get(aggregator)
    val ss = x.getClass.getDeclaredFields
    val createCombinerField = x.getClass.getDeclaredField("createCombiner")
    val mergeValueField = x.getClass.getDeclaredField("mergeValue")
    val mergeCombinersField = x.getClass.getDeclaredField("mergeCombiners")
    createCombinerField.setAccessible(true)
    mergeValueField.setAccessible(true)
    mergeCombinersField.setAccessible(true)
    val createCombiner = createCombinerField.get(x)
    val mergeValue = mergeValueField.get(x)
    val mergeCombiners = mergeCombinersField.get(x)

    val createName = createCombiner.getClass.getName
    val mergeVName = mergeValue.getClass.getName
    val mergeCName = mergeCombiners.getClass.getName

    context.loadClass(createName, true)
    context.loadClass(mergeVName, true)
    context.loadClass(mergeCName, true)

    val createCombinerClass = context.sootClass(createName)
    val mergeValueClass = context.sootClass(mergeVName)
    val mergeCombinerClass = context.sootClass(mergeCName)

    new ShuffleFunc(createCombinerClass, mergeValueClass, mergeCombinerClass)
  }

  private def getFuncByHadoopRDD(analyzeRDD: RDD[_]): String = {
    val actualRDD = analyzeRDD.asInstanceOf[HadoopRDD[_, _]]
    val fField = actualRDD.getClass.getDeclaredFields
    null
  }


}
