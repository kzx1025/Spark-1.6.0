package cn.edu.hust.grid.soot.optimize

import java.io.File
import java.util

import cn.edu.hust.grid.deca.TimeRecorder
import cn.edu.hust.grid.deca.iter.ShuffleData
import cn.edu.hust.grid.soot.template.InvokeFunc
import org.apache.spark.scheduler.{DAGAnalyzer, Phase}
import soot.jimple._
import soot.jimple.internal._
import soot.jimple.spark.SparkTransformer
import soot.jimple.spark.geom.geomPA.GeomPointsTo
import soot.jimple.spark.pag.{AllocDotField, AllocNode, ArrayElement, Node}
import soot.jimple.spark.sets.{P2SetVisitor, PointsToSetInternal}
import soot.{Local, SootClass, SootField, Unit => SootUnit, _}

import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.collection.mutable.HashSet

/**
  * Created by iceke on 17/11/05.
  * 利用SPARK框架对funcClass进行指针分析，得到new Site
  */
object PointerAnalyzer extends Transformer {
  private var lbgfsNum = 0
  var finalFuncClass: SootClass = null
  //"cache" mean from cache
  //"shuffle" mean from shuffle
  val localFromShuffleOrCache = new util.HashMap[JimpleLocal,String]()

  def transform(context: Context, fusionClass: SootClass, phase: Phase): util.List[LocalNewSiteInfo] = {
    addInit(fusionClass, context)
    val invokeClass = addStaticMain(fusionClass, context, phase)
    // 必须要写，接下来的全量加载需要这两个文件
    context.writeOutput(invokeClass)
    context.writeOutput(fusionClass)

    //context.reset("cn.edu.hust.grid.soot.template.InvokeFunc$", "main", true)
    // context.reset("cn.edu.hust.grid.soot.demo.SparkJavaLR", "main", true)
    val loadClassStart = System.currentTimeMillis()
    val newContext = getNewContext()
    val loadClassEnd = System.currentTimeMillis()
    TimeRecorder.loadClassTime = loadClassEnd - loadClassStart
    newContext.writeOutput(newContext.sootClass(invokeClass.getName))
    newContext.writeOutput(newContext.sootClass(fusionClass.getName))
    newContext.writeOutput(newContext.sootClass("cn.edu.hust.grid.deca.iter.HadoopIterator"))
    newContext.writeOutput(newContext.sootClass("cn.edu.hust.grid.deca.iter.DecaShuffleIterator"))
    newContext.writeOutput(newContext.sootClass("cn.edu.hust.grid.deca.iter.DataSourceIterator"))

    //newContext.writeOutput(newContext.sootClass("ShuffleFunc0"))

    val pointerAnalyzeStart = System.currentTimeMillis()
    newContext.scene.setEntryPoints(EntryPoints.v().application())
    val map = new java.util.HashMap[String, String]()
    map.put("enabled", "true")
    map.put("set-impl", "hash")
    map.put("on-fly-cg", "true")
    map.put("propagator", "worklist")
    map.put("verbose", "true")
    map.put("geom-blocking", "true")
    map.put("geom-runs", "2")
    map.put("geom-encoding", "Geom")
    map.put("geom-worklist", "PQ")
    map.put("field-based", "false")
    map.put("geom-pta", "true")
    SparkTransformer.v.transform("", map)
    val pa = newContext.scene.getPointsToAnalysis
    DAGAnalyzer.sootContext = newContext

    val newSiteInfoList = handlePointer(fusionClass, pa, newContext)
    val pointerAnalyzeEnd = System.currentTimeMillis()
    TimeRecorder.pointerAnalysisTime = pointerAnalyzeEnd - pointerAnalyzeStart
    newSiteInfoList
  }


  private def handlePointer(fusionClass: SootClass, pa: PointsToAnalysis, context: Context): util.List[LocalNewSiteInfo] = {
    val funcClass = context.sootClass(fusionClass.getName)

    finalFuncClass = funcClass

    val applyMethod = IteratorFusion.getApplyMethod(funcClass, context)

    val localList = getWriteLocals(applyMethod)

    val newSiteInfoList = new util.ArrayList[LocalNewSiteInfo]()

    for (local <- localList) {
      val localNewSiteInfo = getLocalNewSiteInfo(local, pa, funcClass, context)
      lbgfsNum = 0
      if (localNewSiteInfo != null) {
        if(localFromShuffleOrCache(local) == "shuffle"){
          localNewSiteInfo.genericType = "shuffle"
        }else if(localFromShuffleOrCache(local) == "cache"){
          localNewSiteInfo.genericType = "cache"
        }else{
          localNewSiteInfo.genericType = "undefined"
        }
        newSiteInfoList.add(localNewSiteInfo)
      }
    }

    newSiteInfoList


  }

  private def getLocalNewSiteInfo(local: JimpleLocal, pa: PointsToAnalysis, funcClass: SootClass, context: Context): LocalNewSiteInfo = {
    val topClassType = local.getType

    val fieldSiteMap = new mutable.HashMap[SootField, SootSite]
    var localNewSite: SootSite = null


    var topClass = context.sootClass(topClassType.toString)

    val localQueue: util.Queue[PointsToSetInternal] = new util.LinkedList[PointsToSetInternal]()
    val pToSet = pa.asInstanceOf[GeomPointsTo].reachingObjects(local)
    if (pToSet.isEmpty) {
      return null
    }
    val set = pToSet.asInstanceOf[PointsToSetInternal]
    localQueue.offer(set)

    val setFieldMap = new mutable.HashMap[PointsToSetInternal, AllocDotField]()
    val fieldInfoMap = new mutable.HashMap[SootField, FieldInfo]()


    while (localQueue.nonEmpty) {
      val tempSet = localQueue.poll()
      if (tempSet.size() > 1) {
        println("the local set new Site is not one place!!!! ")
        // throw new OptimizeException("the local set new Site is not one place!!!! can not handle it")
      }


      tempSet.forall(new P2SetVisitor {
        override def visit(n: Node): Unit = {
          val allocNode = n.asInstanceOf[AllocNode]
          //TODO 这里因为不是唯一new Site，所以只能通过手动更改来过
          var allocField: AllocDotField = null
          if (setFieldMap.contains(tempSet)) {
            allocField = setFieldMap(tempSet)
          }
          if (tempSet.size() > 1 && verify(allocNode.getMethod, allocNode, allocField)) {
            //不符合规则直接返回
            return
          }

          println("!!!!!!!" + allocNode.toString)

          if (setFieldMap.contains(tempSet)) {
            val allocField = setFieldMap(tempSet)
            if (allocField != null) {
              val nodeInMethod = allocNode.getMethod
              val nodeInClass = nodeInMethod.getDeclaringClass
              val nodeNewUnit = findSiteUnit(allocNode)
              val nodeInitUnit = findInitUnit(nodeInMethod, nodeNewUnit)
              val sootField = allocField.getField.asInstanceOf[SootField]
              if (fieldSiteMap.contains(sootField)) {
                println("！！!!!！！！！！field的new Site筛选后也不止一个，建议添加筛选规则 " + sootField)
                //fieldSiteMap.remove(sootField)
                return
              }
              fieldSiteMap(sootField) = new SootSite(nodeInClass, nodeInMethod, nodeNewUnit, nodeInitUnit)

              val newExpr = nodeNewUnit.asInstanceOf[JAssignStmt].getRightOp
              var className: String = null
              var isArrayType: Boolean = false
              if (newExpr.isInstanceOf[JNewExpr]) {
                className = newExpr.asInstanceOf[JNewExpr].getBaseType.getClassName
              } else if (newExpr.isInstanceOf[JNewArrayExpr]) {
                className = newExpr.asInstanceOf[JNewArrayExpr].getBaseType.getArrayType.baseType.toString
                isArrayType = true
              } else {
                //TODO 高维数组
                throw OptimizeException("高维数组暂时处理不了")
              }
              val specificClass = context.sootClass(className)
              val fieldInfo = fieldInfoMap(allocField.getField.asInstanceOf[SootField])
              fieldInfo.specificClass = specificClass
              fieldInfo.isArray = isArrayType
            }
          } else {
            val localInMethod = allocNode.getMethod
            val localInClass = localInMethod.getDeclaringClass
            val localNewUnit = findSiteUnit(allocNode)
            val localNewExpr = localNewUnit.asInstanceOf[JAssignStmt].getRightOp
            var className: String = null
            var isArrayType: Boolean = false
            if (localNewExpr.isInstanceOf[JNewExpr]) {
              className = localNewExpr.asInstanceOf[JNewExpr].getBaseType.getClassName
            } else if (localNewExpr.isInstanceOf[JNewArrayExpr]) {
              className = localNewExpr.asInstanceOf[JNewArrayExpr].getBaseType.getArrayType.baseType.toString
              isArrayType = true
            } else {
              //TODO 高维数组
              throw OptimizeException("高维数组暂时处理不了")
            }
            val specificClass = context.sootClass(className)
            topClass = specificClass
            val localInitUnit = findInitUnit(localInMethod, localNewUnit)
            localNewSite = new SootSite(localInClass, localInMethod, localNewUnit, localInitUnit)
          }
          val primitiveList = List("int", "long", "double", "char", "boolean")
          val primitiveMap = mutable.HashMap("int" -> "java.lang.Integer",
            "long" -> "java.lang.Long",
            "double" -> "java.lang.Double",
            "char" -> "java.lang.Character",
            "boolean" -> "java.lang.Boolean")
          var primitiveFields: Option[Iterable[SootField]] = None
          if (allocNode.getType.toString.contains("scala.Tuple2$mc")) {
            val tupleSpecialClass = context.sootClass(allocNode.getType.toString)
            val tempPrimitiveFields: Iterable[SootField] = tupleSpecialClass.getFields.filter(field => primitiveList.contains(field.getType.toString))
            primitiveFields = if (tempPrimitiveFields.nonEmpty) Some(tempPrimitiveFields) else {
              None
            }
          }
          val allocFields: util.Set[AllocDotField] = allocNode.getFields
          for (field <- allocFields) {
            val sootField = field.getField.asInstanceOf[SootField]
            val newP2Set = pa.asInstanceOf[GeomPointsTo].reachingObjects(allocNode, sootField).asInstanceOf[PointsToSetInternal]
            //针对tuple2的特化 例如pagerank的处理，基本类型拿不到
            if (allocNode.getType.toString.contains("scala.Tuple2$mc") && primitiveFields.isDefined && newP2Set.size() == 0) {
              def emptyP2SetOperate(fieldName: String): Unit = {
                val _Field = primitiveFields.get.find(_.getName.contains(fieldName))
                if (_Field.isDefined) {
                  val uncertainClass = context.sootClass(_Field.get.getType.toString)
                  val fieldInfo = FieldInfo(uncertainClass, false, new util.ArrayList[FieldInfo]())
                  uncertainClass.getName match {
                    case "int" =>
                      fieldInfo.specificClass = context.sootClass(primitiveMap("int"))
                    case "long" =>
                      fieldInfo.specificClass = context.sootClass(primitiveMap("long"))
                    case "double" =>
                      fieldInfo.specificClass = context.sootClass(primitiveMap("double"))
                    case "char" =>
                      fieldInfo.specificClass = context.sootClass(primitiveMap("char"))
                    case "boolean" =>
                      fieldInfo.specificClass = context.sootClass(primitiveMap("boolean"))
                  }
                  if (setFieldMap.contains(tempSet)) {
                    //记录field之间的关系
                    val parentField = setFieldMap(tempSet)
                    val parentFieldInfo = fieldInfoMap(parentField.getField.asInstanceOf[SootField])
                    parentFieldInfo.childFieldInfos.add(fieldInfo)
                  }
                  fieldInfoMap(sootField) = fieldInfo
                }
              }

              field.getField.asInstanceOf[SootField].getName match {
                case "_1" =>
                  emptyP2SetOperate("_1")
                case "_2" =>
                  emptyP2SetOperate("_2")
              }
            }
            else if (newP2Set.size() != 0 && field.getField.isInstanceOf[SootField]) {
              //这里不确定具体的类型，需要通过local来判断其类型
              val uncertainClass = context.sootClass(sootField.getType.toString)
              val fieldInfo = new FieldInfo(uncertainClass, false, new util.ArrayList[FieldInfo]())
              //证明现在的field的父亲已经被记录
              if (setFieldMap.contains(tempSet)) {
                //记录field之间的关系
                val parentField = setFieldMap(tempSet)
                val parentFieldInfo = fieldInfoMap(parentField.getField.asInstanceOf[SootField])
                parentFieldInfo.childFieldInfos.add(fieldInfo)
              }

              println(field.toString)
              localQueue.offer(newP2Set)
              setFieldMap(newP2Set) = field
              fieldInfoMap(sootField) = fieldInfo
            } else if (newP2Set.size() != 0 && field.getField.isInstanceOf[ArrayElement]) {
              //如果写进缓存的是对象数组呢
              localQueue.offer(newP2Set)

            } else {
              println(field + " have no new Site, so don't record and handle it")
            }
          }
        }
      })

    }


    val localNewSiteInfo = new LocalNewSiteInfo(context, funcClass, local, topClass,
      "Double", localNewSite, fieldInfoMap, fieldSiteMap)

    localNewSiteInfo
  }


  private def getNewContext(): Context = {
    var newContext: Context = null
    if (DAGAnalyzer.maxOuterClassName.equals("cn.edu.hust.grid.example.SparkKMeans")) {
      newContext = new Context(mainClass = "cn.edu.hust.grid.soot.template.InvokeFunc$", entryMethod = "main", preload = false, excludePackages = List("polyglot.*",
        "org.jf.*", "breeze.linalg.operators.*", "breeze.linalg.support.*", "com.esotericsoftware.*", "jdk.internal.*", "soot.*", "org.apache.*", "org.apache.hadoop.*", "org.spark_project.*"),
        classpath = "sootOutput" + File.pathSeparator + System.getProperty("java.class.path"))
    } else if (DAGAnalyzer.maxOuterClassName.equals("cn.edu.hust.grid.example.SparkHdfsLR")) {
      newContext = new Context(mainClass = "cn.edu.hust.grid.soot.template.InvokeFunc$", entryMethod = "main", preload = false, excludePackages = List("polyglot.*",
        "org.jf.*", "breeze.linalg.support.*", "com.esotericsoftware.*", "jdk.internal.*", "soot.*", "org.apache.*", "org.apache.hadoop.*", "org.spark_project.*"),
        classpath = "sootOutput" + File.pathSeparator + System.getProperty("java.class.path"))
    } else if (DAGAnalyzer.maxOuterClassName.contains("cn.edu.hust.grid.example.mllib") || DAGAnalyzer.maxOuterClassName.contains("org.apache.spark.mllib.")) {
      if (DAGAnalyzer.appName.equals("PCAExample")) {
        newContext = new Context(mainClass = "cn.edu.hust.grid.soot.template.InvokeFunc$", entryMethod = "main",
          includeClasses = List("org.apache.spark.mllib.*"),
          preload = false,
          excludePackages = List("polyglot.*",
            "org.jf.*", "org.json4s.*", "breeze.linalg.operators.*", "java.lang.Class", "com.fasterxml.*", "com.google.*", "scala.reflect.internal.*", "javassist.*", "scala.tools.*", "scala.concurrent.*", "breeze.linalg.support.*", "com.esotericsoftware.*", "jdk.internal.*", "org.spark_project.*", "org.apache.*", "soot.*"),
          classpath = "sootOutput" + File.pathSeparator + System.getProperty("java.class.path"))
      } else {
        newContext = new Context(mainClass = "cn.edu.hust.grid.soot.template.InvokeFunc$", entryMethod = "main",
          includeClasses = List("org.apache.spark.mllib.*", "org.apache.spark.ml.*"),
          preload = false,
          excludePackages = List("polyglot.*",
            "org.jf.*", "breeze.linalg.*", "org.json4s.*", "com.fasterxml.*", "com.google.*", "scala.reflect.internal.*", "javassist.*", "scala.tools.*", "scala.concurrent.*", "breeze.linalg.support.*", "com.esotericsoftware.*", "jdk.internal.*", "org.spark_project.*", "org.apache.*", "soot.*"),
          classpath = "sootOutput" + File.pathSeparator + System.getProperty("java.class.path"))
      }
    } else {
      newContext = new Context(mainClass = "cn.edu.hust.grid.soot.template.InvokeFunc$", entryMethod = "main", preload = false, excludePackages = List("polyglot.*",
        "org.jf.*", "jdk.internal.*", "soot.*", "org.apache.*", "org.apache.hadoop.*", "com.esotericsoftware.*", "javassist.*", "com.google.*", "scala.concurrent.*", "scala.collection.parallel.*", "breeze.linalg.support.*", "org.spark_project.*"),
        classpath = "sootOutput" + File.pathSeparator + System.getProperty("java.class.path"))
    }
    newContext
  }

  private def verify(allocMethod: SootMethod, allocNode: AllocNode, allocField: AllocDotField): Boolean = {
    if (allocMethod == null) {
      return true
    }

    if (DAGAnalyzer.maxOuterClassName.equals("cn.edu.hust.grid.example.SparkKMeans") && (allocMethod.getName.contains("$mDc$sp") && allocNode.getNumber == 714
      || allocMethod.getName.equals("mkArray"))) {
      return false
    } else if (DAGAnalyzer.maxOuterClassName.equals("cn.edu.hust.grid.example.SparkPR")) {
      if (allocMethod.getName.contains("valueOf") || allocMethod.getName.contains("main")) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.maxOuterClassName.equals("cn.edu.hust.grid.example.SparkCC")) {
      if (allocMethod.getName.contains("valueOf") || allocMethod.getName.contains("main")) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.equals("StandardScalerExample")) {
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.contains("valueOf")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.contains("getZeroValue")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v()
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v()
      ) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.equals("LBFGSExample")) {
      //存在Tuple2覆盖问题 函待解决
      if (allocMethod.getName.equals("treeAggregate") || allocNode.getType.toString.contains("DenseVector")) {
        lbgfsNum += 1
      }
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.contains("valueOf") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.contains("getZeroValue") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.equals("treeAggregate") && lbgfsNum <= 2
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getReturnType.toString.contains("Integer")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocNode.getType.toString.contains("DenseVector") && lbgfsNum > 2
      ) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.equals("LinearRegressionWithSGDExample")) {
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocMethod.getReturnType.toString.contains("Integer")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocMethod.getName.equals("treeAggregate")) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.equals("LogisticRegressionWithLBFGSExample")) {
      //存在Tuple2覆盖问题
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.contains("valueOf") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && (allocMethod.getName.equals("getZeroValue"))
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("valueOf") && allocMethod.getReturnType.toString.contains("Integer") && allocField.getBase.getMethod.getName.equals("apply")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getBase.getMethod.getName.equals("apply") && allocMethod.getName.equals("treeAggregate")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getBase.getMethod.getName.equals("treeAggregate") && allocMethod.getName.equals("dense")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocField.getBase.getMethod.getName.equals("treeAggregate") && allocMethod.getName.equals("valueOf") && allocMethod.getReturnType.toString.contains("Double")) {
        return false
      } else {
        return true
      }

    } else if (DAGAnalyzer.appName.equals("SVMWithSGDExample")) {
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.contains("valueOf") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("apply")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("apply")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("apply")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.equals("treeAggregate")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocField.getBase.getMethod.getName.equals("apply") && allocMethod.getName.equals("valueOf") && allocMethod.getReturnType.toString.contains("Integer")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("dasdsa")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.equals("valueOf") && allocField.getBase.getMethod.getName.equals("treeAggregate") && allocMethod.getReturnType.toString.contains("Double")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getName.equals("valueOf") && allocField.getBase.getMethod.getName.equals("treeAggregate") && allocMethod.getReturnType.toString.contains("Long")) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.equals("NormalizerExample")) {
      if (allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].baseType == IntType.v()
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].baseType == DoubleType.v()) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.equals("PCAExample")) {
      if (allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.equals("treeAggregate")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocMethod.getReturnType.toString.contains("Long")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getReturnType.toString.contains("Double")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getReturnType.toString.contains("Integer")) {
        return false
      } else {
        return true
      }

    } else if (DAGAnalyzer.appName.contains("FPGrowthExample")) {
      if (allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("next") && allocMethod.getReturnType.toString.contains("String")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.equals("mkArray")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("valueOf") && allocField.getBase.getMethod.getDeclaringClass.getName.contains("HashMap")
      ) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.contains("DecisionTreeClassificationExample")) {
      if (allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("getTreeClassifyValue")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("DTStatsAggregator") && allocField.getField.asInstanceOf[SootField].getName.equals("impurityAggregator") && allocMethod.getName.equals("not")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocMethod.getName.equals("newArray")) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.contains("DecisionTreeRegressionExample")) {
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("getTreeClassifyValue")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("DTStatsAggregator") && allocField.getField.asInstanceOf[SootField].getName.equals("impurityAggregator") && allocMethod.getName.equals("not")) {
        return false
      } else {
        return true
      }

    } else if (DAGAnalyzer.appName.equals("ChiSqSelectorExample")) {
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("parseLibSVMRecord") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("parseLibSVMRecord") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocMethod.getName.equals("valueOf") && allocMethod.getReturnType.toString.contains("Long")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("getChiSqValue")) {
        return false
      } else {
        return true
      }
    } else if (DAGAnalyzer.appName.contains("RandomForestClassificationExample")) {
      if (allocField.getField.asInstanceOf[SootField].getName.equals("_2") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("parseLibSVMRecord") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == IntType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getName.equals("_3") && allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple3") && allocField.getBase.getMethod.getName.equals("parseLibSVMRecord") && allocMethod.getReturnType.isInstanceOf[ArrayType] && allocMethod.getReturnType.asInstanceOf[ArrayType].getElementType == DoubleType.v() && allocMethod.getName.equals("newArray")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("scala.Tuple2") && allocField.getField.asInstanceOf[SootField].getName.equals("_1") && allocMethod.getName.equals("getTreeClassifyValue")
        || allocField.getField.asInstanceOf[SootField].getDeclaringClass.getName.equals("DTStatsAggregator") && allocField.getField.asInstanceOf[SootField].getName.equals("impurityAggregator") && allocMethod.getName.equals("not")) {
        return false
      } else {
        return true
      }
    }


    if (allocMethod.getDeclaringClass.getName.contains("cn.edu.hust.grid.")
      || allocMethod.getDeclaringClass.getName.contains("Func")
      || allocMethod.getName.contains("valueOf")) {
      return false
    }

    return true
  }

  private def findInitUnit(nodeInMethod: SootMethod, nodeNewUnit: SootUnit): SootUnit = {
    val newLocal = nodeNewUnit.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    for (unit <- nodeInMethod.getActiveBody.getUnits) {
      if (unit.isInstanceOf[JInvokeStmt]) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        if (jInvokeStmt.getInvokeExpr.isInstanceOf[JSpecialInvokeExpr]) {
          val jSpecial = jInvokeStmt.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr]
          if (jSpecial.getBase.isInstanceOf[JimpleLocal]) {
            val base = jSpecial.getBase.asInstanceOf[JimpleLocal]
            val methodName = jSpecial.getMethod.getName
            if (base == newLocal && methodName.equals("<init>")) {
              return unit
            }
          }

        }

      }

    }
    null
  }

  private def findSiteUnit(allocNode: AllocNode): SootUnit = {
    val targetMethod = allocNode.getMethod
    val newExpr = allocNode.getNewExpr
    for (unit <- targetMethod.getActiveBody.getUnits) {
      if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp == newExpr) {
          return unit
        }
      }

    }
    null
  }

  private def getWriteLocals(applyMethod: SootMethod): java.util.List[JimpleLocal] = {
    var localList = new util.ArrayList[JimpleLocal]()
    var jumpFlag = true //由于我们获取一个writeLocal就能分析出shuffle的类型，所以获取到一个就退出
    var cacheLocalNum: Int = 0
    var shuffleLocalNum: Int = 0
    for (unit <- applyMethod.getActiveBody.getUnits if jumpFlag) {
      if (unit.isInstanceOf[JInvokeStmt]) {
        val invokeStmt = unit.asInstanceOf[JInvokeStmt]
        val methodName = invokeStmt.getInvokeExpr.getMethod.getName
        val className = invokeStmt.getInvokeExpr.getMethodRef.declaringClass().getName
        //由于我们现在只用分析write的类型 所以，不需要获取读cache的local
        if (methodName.equals("writeElement") && className.contains("DecaBlockManager$")) {
          if (invokeStmt.getInvokeExpr.getArg(0).isInstanceOf[JimpleLocal] && cacheLocalNum < 1) {
            val local = invokeStmt.getInvokeExpr.getArg(0).asInstanceOf[JimpleLocal]
            localList.add(local)
            localFromShuffleOrCache(local) = "cache"
            cacheLocalNum += 1
          }
        } else if (methodName.equals("writeElement") && className.contains("DecaShuffleManager$")) {
          if (invokeStmt.getInvokeExpr.getArg(0).isInstanceOf[JimpleLocal] && shuffleLocalNum < 1) {
            val local = invokeStmt.getInvokeExpr.getArg(0).asInstanceOf[JimpleLocal]
            localList.add(local)
            localFromShuffleOrCache(local) = "shuffle"
            shuffleLocalNum += 1
            ShuffleData.dataType  = local.getType.toString
          }
        }
      }
    }
    localList
  }


  private def addInit(fusionClass: SootClass, context: Context): Unit = {
    //find调用了外部类
    var outerFields = new HashSet[SootField]
    var rddField: SootField = null
    val addFields = new HashSet[SootField]
    val addFieldsMap = new mutable.HashMap[String, SootField]
    for (field <- fusionClass.getFields) {
      if (field.asInstanceOf[SootField].getName.contains("$outer")) {
        outerFields.add(field)
      } else if (field.asInstanceOf[SootField].getName.equals("rddId")) {
        rddField = field
      }
    }
    val applyMethod = IteratorFusion.getApplyMethod(fusionClass, context)
    val units = applyMethod.getActiveBody.getUnits
    var outerLocals = new HashSet[JimpleLocal]

    val loopMethodLocals = applyMethod.getActiveBody.getLocals
    val outerUnits = new HashSet[SootUnit]

    //获得本对象的引用
    var thisLocal: Local = null
    for (local <- loopMethodLocals) {
      if (local.getType.toString.equals(fusionClass.getName)) {
        thisLocal = local
      }
    }

    var isOuterMethod: Boolean = false

    for (unit <- units) {
      if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          if (outerFields.contains(jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].getField)) {
            outerLocals.add(jAssignStmt.getLeftOp.asInstanceOf[JimpleLocal])
            outerUnits.add(unit)
          }
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          if (jInstanceFieldRef.getBase.isInstanceOf[JimpleLocal]) {
            val baseLocal = jInstanceFieldRef.getBase.asInstanceOf[JimpleLocal]
            if (outerLocals.contains(baseLocal)) {
              val originField = jInstanceFieldRef.getField
              val realField = DAGAnalyzer.outerObject.getClass.getDeclaredField(originField.getName)
              realField.setAccessible(true)
              var fieldType: Type = null
              if (realField.getType.toString.equals("int")) {
                fieldType = IntType.v()
              } else if (realField.getType.toString.equals("double")) {
                fieldType = DoubleType.v()
              } else {
                val realSpecificObject = realField.get(DAGAnalyzer.outerObject)
                val realObjectClassName = realSpecificObject.getClass.getName
                context.loadClass(realObjectClassName)
                fieldType = context.sootClass(realObjectClassName).getType
              }
              val fieldName = originField.getName
              val fieldStatic = originField.isStatic
              val fieldModifiers = originField.getModifiers
              var newField: SootField = null
              if (!addFieldsMap.contains(fieldName)) {
                newField = new SootField(fieldName, fieldType, rddField.getModifiers)
                fusionClass.addField(newField)
                addFields.add(newField)
                addFieldsMap(fieldName) = newField
              } else {
                newField = addFieldsMap(fieldName)
              }
              jInstanceFieldRef.setFieldRef(newField.makeRef())
              jInstanceFieldRef.setBase(thisLocal)
            }
          }

          //TODO 有可能还有闭包的方法需要处理，这里只处理了field

        }

      } else if (unit.isInstanceOf[JInvokeStmt]) {
        val invokeStmt = unit.asInstanceOf[JInvokeStmt]
        //闭包方法不处理,直接不删除闭包
        isOuterMethod = true

      }
    }

    //去除关于outer的field和unit，local
    if (!isOuterMethod) {
      for (outerLocal <- outerLocals) {
        applyMethod.getActiveBody.getLocals.remove(outerLocal)
      }
      for (outerField <- outerFields) {
        fusionClass.removeField(outerField)
      }

      for (outerUnit <- outerUnits) {
        applyMethod.getActiveBody.getUnits.remove(outerUnit)
      }

    }
    val initMethod = FunctionProducer.getInitMethod(fusionClass)

    fusionClass.addMethod(initMethod)

  }


  private def addStaticMain(fusionClass: SootClass, context: Context, phase: Phase): SootClass = {
    val needNewFields = new util.ArrayList[SootField]()
    for (field <- fusionClass.getFields) {
      if (!field.getName.equals("serialVersionUID")) {
        needNewFields.add(field)
      }
    }

    context.loadClass(InvokeFunc.getClass.getName, true)
    val staticClass: SootClass = context.sootClass(InvokeFunc.getClass.getName)
    val mainMethod: SootMethod = staticClass.getMethodByName("main")

    val methodBody = mainMethod.getActiveBody
    var returnUnit: SootUnit = null
    for (unit <- methodBody.getUnits) {
      if (unit.isInstanceOf[ReturnVoidStmt]) {
        returnUnit = unit
      }
    }

    var index: Int = 2
    val initArgs = new util.ArrayList[JimpleLocal]()
    for (field <- needNewFields) {
      val fieldType = field.getType
      val local: JimpleLocal = new JimpleLocal(field.getName + index, fieldType)

      if (isOriginType(fieldType, context)) {
        val assignUnit = returnAssignUnit(fieldType, local, context)
        methodBody.getLocals.add(local)
        methodBody.getUnits.insertBefore(assignUnit, returnUnit)
      } else if (fieldType.isInstanceOf[ArrayType]) {
        // 数组就不处理了
        methodBody.getLocals.add(local)
        val assignment = new JAssignStmt(local, NullConstant.v())
        methodBody.getUnits.insertBefore(assignment, returnUnit)

      } else {
        var initMethod: SootMethod = null
        val fieldClassName = fieldType.toString
        val fieldClass = context.sootClass(fieldClassName)
        initMethod = findProperInit(fieldClass, context)
        //暂时只能处理一层构造器
        if (initMethod == null) {
          val assignment = new JAssignStmt(local, new JNewExpr(fieldClass.getType))
          methodBody.getLocals.add(local)
          methodBody.getUnits.insertBefore(assignment, returnUnit)
          // throw new OptimizeException("can not find init method from field")
        } else {
          //TODO 对field进行递归构造，未完成，需要通过反射得到闭包的具体类型
          val assignment = new JAssignStmt(local, new JNewExpr(fieldClass.getType))
          methodBody.getLocals.add(local)
          methodBody.getUnits.insertBefore(assignment, returnUnit)
        }

      }
      initArgs.add(local)
      index += 1
    }

    val funcLocal = new JimpleLocal("func", fusionClass.getType)
    val newFuncUnit = new JAssignStmt(funcLocal, new JNewExpr(fusionClass.getType))
    val initFuncUnit = new JInvokeStmt(new JSpecialInvokeExpr(funcLocal,
      fusionClass.getMethodByName("<init>").makeRef(), initArgs))

    //调用apply方法
    val applyArgs = new util.ArrayList[JimpleLocal]()
    val taskContextLocal = new JimpleLocal("taskContext",
      context.sootClass("org.apache.spark.scheduler.DecaTaskContext").getType)
    val idLocal = new JimpleLocal("id", IntType.v())
    var iterLocal: JimpleLocal = null
    var iterUnit: SootUnit = null
    var iterInitUnit: SootUnit = null

    var shuffleDataLocal: JimpleLocal = null
    var newShuffleDataUnit: SootUnit = null
    var iterDataUnit: SootUnit = null
    if (phase.dataSource.equals("hadoop")) {
      iterLocal = new JimpleLocal("iter", context.sootClass("cn.edu.hust.grid.deca.iter.HadoopIterator").getType)
      iterUnit = new JAssignStmt(iterLocal, new JNewExpr(context.sootClass("cn.edu.hust.grid.deca.iter.HadoopIterator").getType))
      iterInitUnit = new JInvokeStmt(new JSpecialInvokeExpr(iterLocal,
        context.sootClass("cn.edu.hust.grid.deca.iter.HadoopIterator").getMethodByName("<init>").makeRef(), new util.ArrayList()))
    } else if (phase.dataSource.equals("shuffle")) {
      iterLocal = new JimpleLocal("iter", context.sootClass("cn.edu.hust.grid.deca.iter.DecaShuffleIterator").getType)
      iterUnit = new JAssignStmt(iterLocal, new JNewExpr(context.sootClass("cn.edu.hust.grid.deca.iter.DecaShuffleIterator").getType))
      if (ShuffleData.dataType != null) {
        val shuffleDataClass = context.sootClass(ShuffleData.dataType)
        shuffleDataLocal = new JimpleLocal("shuffleData", shuffleDataClass.getType)
        newShuffleDataUnit = new JAssignStmt(shuffleDataLocal, new JNewExpr(shuffleDataClass.getType))
        val argList = new util.ArrayList[Value]()
        argList.add(shuffleDataLocal)
        iterDataUnit = new JInvokeStmt(new JVirtualInvokeExpr(iterLocal,
          context.sootClass("cn.edu.hust.grid.deca.iter.DecaShuffleIterator").getMethodByName("setElement").makeRef(), argList))
      }
      iterInitUnit = new JInvokeStmt(new JSpecialInvokeExpr(iterLocal,
        context.sootClass("cn.edu.hust.grid.deca.iter.DecaShuffleIterator").getMethodByName("<init>").makeRef(), new util.ArrayList()))
    }
    val taskContextUnit = new JAssignStmt(taskContextLocal, NullConstant.v())
    val idUnit = new JAssignStmt(idLocal, IntConstant.v(1))

    // add platform elem
    val platFormClass = context.sootClass("cn.edu.hust.grid.soot.optimize.Platform")
    val platformInvoke = new JInvokeStmt(new JStaticInvokeExpr(platFormClass.getMethodByName("putLong").makeRef(), util.Arrays.asList(NullConstant.v(), LongConstant.v(0), LongConstant.v(0))))

    applyArgs.add(taskContextLocal)
    applyArgs.add(idLocal)
    applyArgs.add(iterLocal)
    val applyMethod = IteratorFusion.getApplyMethod(fusionClass, context)
    val invokeApplyUnit = new JInvokeStmt(new JVirtualInvokeExpr(funcLocal, applyMethod.makeRef(), applyArgs))

    methodBody.getLocals.add(taskContextLocal)
    methodBody.getLocals.add(idLocal)
    methodBody.getLocals.add(iterLocal)
    methodBody.getLocals.add(funcLocal)
    if (phase.dataSource.equals("shuffle")) {
      methodBody.getLocals.add(shuffleDataLocal)
    }

    methodBody.getUnits.insertBefore(platformInvoke, returnUnit)

    methodBody.getUnits.insertBefore(newFuncUnit, returnUnit)
    methodBody.getUnits.insertBefore(initFuncUnit, returnUnit)

    methodBody.getUnits.insertBefore(taskContextUnit, returnUnit)
    methodBody.getUnits.insertBefore(idUnit, returnUnit)
    methodBody.getUnits.insertBefore(iterUnit, returnUnit)
    methodBody.getUnits.insertBefore(iterInitUnit, returnUnit)

    if (phase.dataSource.equals("shuffle")) {
      methodBody.getUnits.insertBefore(newShuffleDataUnit, returnUnit)
      methodBody.getUnits.insertBefore(iterDataUnit, returnUnit)

    }


    methodBody.getUnits.insertBefore(invokeApplyUnit, returnUnit)

    staticClass
  }


  private def findProperInit(fieldClass: SootClass, context: Context): SootMethod = {
    val methods = fieldClass.getMethods
    for (method <- methods) {
      val paramTypes = method.getParameterTypes
      var proper: Boolean = true
      for (paramType <- paramTypes) {
        if (paramType != IntType.v() && paramType != FloatType.v() && paramType != LongType.v()
          && paramType != DoubleType.v() && paramType != context.sootClass("java.lang.Object").getType) {
          proper = false
        }
      }
      if (proper) {
        return method
      }
    }
    null
  }

  private def isOriginType(valueType: Type, context: Context): Boolean = {
    if (valueType != IntType.v() && valueType != FloatType.v() && valueType != LongType.v()
      && valueType != DoubleType.v() && valueType != context.sootClass("java.lang.Object").getType) {
      false
    } else {
      true
    }

  }

  private def returnAssignUnit(valueType: Type, local: JimpleLocal, context: Context): SootUnit = {
    var assignStmt: SootUnit = null

    valueType match {
      case _: IntType =>
        assignStmt = new JAssignStmt(local, IntConstant.v(1))
      case _: FloatType =>
        assignStmt = new JAssignStmt(local, FloatConstant.v(1.0f))
      case _: LongType =>
        assignStmt = new JAssignStmt(local, LongConstant.v(1L))
      case _: DoubleType =>
        assignStmt = new JAssignStmt(local, DoubleConstant.v(1.0))
      case _ =>
        //默认为objectType
        //assignStmt = new JAssignStmt(local, new  RefType.v(context.sootClass("java.lang.Object")))
        assignStmt = new JAssignStmt(local, new JNewExpr(context.sootClass("java.lang.Object").getType))

    }

    assignStmt

  }

  override def transform(context: Context): Unit = {

  }

}
