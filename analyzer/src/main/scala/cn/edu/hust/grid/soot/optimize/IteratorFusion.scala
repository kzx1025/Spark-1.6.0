package cn.edu.hust.grid.soot.optimize

import java.util

import cn.edu.hust.grid.deca.{MLDataProduce, TreeAggregateInfo}
import cn.edu.hust.grid.soot.Utils
import cn.edu.hust.grid.soot.template.{CacheLoopTemplate, LoopTemplate, ShuffleCacheLoopTemplate, ShuffleLoopTemplate}
import org.apache.spark.scheduler.DAGAnalyzer.{IsForEach, IsReduce, ResultType}
import org.apache.spark.scheduler.{DAGAnalyzer, Phase}
import soot.jimple._
import soot.jimple.internal._
import soot.jimple.toolkits.scalar.LocalNameStandardizer
import soot.{IntType, Modifier, SootField, SootMethod, Type, Unit => SootUnit, _}

import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.collection.mutable.HashSet


/**
  * Created by iceke on 2017/10/21.
  * 用于将一个stage的所有的RDD方法融合在一个loop中
  * modified by iceke
  */
object IteratorFusion extends Transformer {

  val filterFuncs = new HashSet[String]
  val flatMapFuncs = new HashSet[String]
  val mapValuesFuncs = new HashSet[String]
  val mapPartitionsFuncs = new HashSet[String]
  //用于mllib， key为seqName
  val treeAggregateMap = new mutable.HashMap[String, TreeAggregateInfo]()

  var flatMapType: String = "seq"


  /**
    * 针对reduce方法
    *
    * @param reduceClass
    * @return
    */
  private def genReduceFunc(reduceClass: SootClass, resultClass: SootClass, context: Context): SootMethod = {
    if (resultClass == null || reduceClass == null) {
      return null
    }
    val methods = reduceClass.getMethods
    var applyMethod: SootMethod = null

    for (method <- methods) {
      if (method.getName.equals("apply") && method.getReturnType != context.sootClass("java.lang.Object").getType) {
        applyMethod = method
      }
    }
    var reduceFunc: SootMethod = null
    try {
      reduceFunc = SootHelper.cloneMethod(applyMethod, reduceClass, resultClass)
      reduceFunc.setName("resultMethod")
      reduceFunc
    } catch {
      case e: Exception => {
        println("can not get reduceFunc")
        null
      }
        null
    }
  }

  private def genTreeAggregateFunc(seqClass: SootClass, resultClass: SootClass, context: Context): SootMethod = {
    val methods = seqClass.getMethods
    var applyMethod: SootMethod = null

    //要先把seqClass的fields全部加进来
    for (field <- seqClass.getFields) {
      if (!field.getName.equals("serialVersionUID")) {
        resultClass.addField(Utils.cloneSootField(field))
      }
    }

    for (method <- methods) {
      if (method.getName.equals("apply") && method.getReturnType != context.sootClass("java.lang.Object").getType && method.getParameterCount == 2) {
        applyMethod = method
      }
    }

    val treeFunc = SootHelper.cloneMethod(applyMethod, seqClass, resultClass)
    treeFunc.setName("treeAggregate")
    treeFunc
  }

  private def modifyUnit(newClass: SootClass, oldClass: SootClass, op: Value, thisLocal: Local): Value = {
    if (op.isInstanceOf[JInstanceFieldRef]) {
      val field = op.asInstanceOf[JInstanceFieldRef].getField
      val fieldName = field.getName
      if (field.getDeclaringClass == oldClass) {
        val newFieldRef = newClass.getFieldByName(fieldName).makeRef()
        op.asInstanceOf[JInstanceFieldRef].setBase(thisLocal)
        op.asInstanceOf[JInstanceFieldRef].setFieldRef(newFieldRef)
      }
    } else if (op.isInstanceOf[JVirtualInvokeExpr]) {
      val jVirtualInvokeExpr = op.asInstanceOf[JVirtualInvokeExpr]
      if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldClass.getName)) {
        val invokeName = jVirtualInvokeExpr.getMethodRef.name()
        val oldMethod = oldClass.getMethodByName(invokeName)
        val newMethod = SootHelper.cloneMethod(oldMethod, oldClass, newClass)
        val newMethodRef = newMethod.makeRef()
        jVirtualInvokeExpr.setBase(thisLocal)
        jVirtualInvokeExpr.setMethodRef(newMethodRef)
      }
    }
    op
  }

  def getApplyMethod(sootClass: SootClass, context: Context): SootMethod = {
    val methodsIter = sootClass.getMethods.iterator()
    var resultMethod: SootMethod = null
    while (methodsIter.hasNext) {
      val method = methodsIter.next()
      val paramTypes = method.getParameterTypes
      val returnType = method.getReturnType
      if (method.getName.equals("apply") && (paramTypes.get(0) != context.sootClass("java.lang.Object").getType || returnType != context.sootClass("java.lang.Object").getType)) {
        resultMethod = method
      }
    }
    resultMethod
  }

  /**
    * 添加必要的方法--apply(object)，clinit，init方法
    *
    * @param resultClass
    * @param context
    */
  private def finishResultClass(resultClass: SootClass, context: Context): Unit = {

    //添加apply(object,object,object)方法
    val newLoopMethod = getApplyMethod(resultClass, context)
    val applyObjectMethod = FunctionProducer.getFunction3Apply(context, resultClass, newLoopMethod.getParameterTypes,
      newLoopMethod.getReturnType)
    val oldObjectApplyParams = new java.util.ArrayList[Type]()
    oldObjectApplyParams.add(context.sootClass("java.lang.Object").getType)
    if (resultClass.getMethodUnsafe("apply", oldObjectApplyParams,
      context.sootClass("java.lang.Object").getType) != null) {

      resultClass.removeMethod(resultClass.getMethod("apply", oldObjectApplyParams,
        context.sootClass("java.lang.Object").getType))
    }
    resultClass.addMethod(applyObjectMethod)

    //添加cinit方法
    val initMethod = FunctionProducer.getClInitMethod(context, resultClass)
    resultClass.addMethod(initMethod)
  }


  private def initResultClass(phase: Phase, context: Context): SootClass = {
    val funcClassName = phase.kind + "Func" + phase.id
    val newSootClass = new SootClass(funcClassName)
    newSootClass.setSuperclass(context.sootClass("scala.runtime.AbstractFunction3"))
    newSootClass.setModifiers(17)
    newSootClass.setInScene(true)
    newSootClass.addInterface(context.sootClass("scala.Serializable"))
    val rddIdField = new SootField("rddId", IntType.v(), Modifier.PUBLIC)
    val serField = new SootField("serialVersionUID", LongType.v(), 25)
    newSootClass.addField(rddIdField)
    newSootClass.addField(serField)

    //获得loop方法模板并添加到resultClass中
    var loopTemplateName: String = null
    if (DAGAnalyzer.cachePhasesMap.contains(phase)) {
      if (phase.kind.equals("Result")) {
        loopTemplateName = new CacheLoopTemplate(0).getClass.getName
      } else {
        //ShuffleStage
        loopTemplateName = new ShuffleCacheLoopTemplate(0).getClass.getName
      }
    } else {
      if (phase.kind.equals("Result")) {
        loopTemplateName = new LoopTemplate(0).getClass.getName
      } else {
        //ShuffleStage
        loopTemplateName = new ShuffleLoopTemplate(0).getClass.getName
      }
    }
    context.loadClass(loopTemplateName, true)
    val loopClass = context.sootClass(loopTemplateName)
    val loopMethod = loopClass.getMethodByName("loopFunc")
    val newLoopMethod = SootHelper.cloneMethod(loopMethod, loopClass, newSootClass)
    newLoopMethod.setName("apply")

    newSootClass.validate()

    newSootClass

  }


  /**
    * 融合无cache的SuhffleStage
    *
    * @param context
    * @param phase
    */
  def transformShufflePhase(context: Context, phase: Phase): SootClass = {

    val fusionFuncList = context.fusionClassList
    val resultClass: SootClass = initResultClass(phase, context)


    val newLoopMethod = getApplyMethod(resultClass, context)

    val loopMethodLocals = newLoopMethod.getActiveBody.getLocals

    //获得本对象的引用
    var thisLocal: Local = null
    for (local <- loopMethodLocals) {
      if (local.getType.toString.equals(resultClass.getName)) {
        thisLocal = local
      }
    }

    val loopMethodUnits = newLoopMethod.getActiveBody.getUnits
    var forStartUnit: SootUnit = null
    var forEndUnit: SootUnit = null
    var readValueUnit: SootUnit = null
    var lastIdentityUnit: SootUnit = null
    var castToIntUnit: SootUnit = null
    var writeElementUnit: SootUnit = null
    var returnUnit: SootUnit = null

    val unitBoxes = newLoopMethod.getActiveBody.getAllUnitBoxes
    val restartUnit = unitBoxes.get(1).getUnit


    for (unit <- loopMethodUnits) {
      unit match {
        case _: JIfStmt =>
          forStartUnit = unit.asInstanceOf[JIfStmt]
        case _: JGotoStmt =>
          forEndUnit = unit.asInstanceOf[JGotoStmt]
        case _: JAssignStmt =>
          val assignStmt = unit.asInstanceOf[JAssignStmt]
          if (assignStmt.containsInvokeExpr()) {
            if (assignStmt.getInvokeExpr.getMethod.getName.equals("next")) {
              readValueUnit = unit.asInstanceOf[JAssignStmt]
            }
          } else if (assignStmt.getRightOp.isInstanceOf[JCastExpr]) {
            castToIntUnit = unit
          }
        case _: JIdentityStmt =>
          lastIdentityUnit = unit

        case _: JReturnVoidStmt =>
          returnUnit = unit

        case _: JInvokeStmt =>
          val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
          if (jInvokeStmt.getInvokeExpr.getMethod.getName.equals("writeElement")) {
            writeElementUnit = unit
          }

        case _ =>

      }

    }
    var funcIndex = 0
    var currentUnit = readValueUnit
    var prevValueLocal = readValueUnit.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    for (funcClass <- fusionFuncList) {
      val fusionClass = context.sootClass(funcClass)
      if (IteratorFusion.treeAggregateMap.contains(funcClass)) {
        val treeAggregateInfo = treeAggregateMap(funcClass)
        val zeroValueClass = context.sootClass(treeAggregateInfo.zeroValueName)
        context.loadClass("cn.edu.hust.grid.deca.MLDataProduce")
        val mlDataProduceClass = context.sootClass("cn.edu.hust.grid.deca.MLDataProduce")
        val getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getZeroValue")
        val args = new util.ArrayList[Value]()
        //添加zeroValue 即初始值 在循环体外
        val zeroValueLocal = new JimpleLocal("zeroValue", zeroValueClass.getType)
        val zeroValueAssign = new JAssignStmt(zeroValueLocal, new JStaticInvokeExpr(getDataMethod.makeRef(), args))
        newLoopMethod.getActiveBody.getLocals.add(zeroValueLocal)
        newLoopMethod.getActiveBody.getUnits.insertAfter(zeroValueAssign, lastIdentityUnit)

        val seqClass = context.sootClass(treeAggregateInfo.seqName)
        val treeFunc = genTreeAggregateFunc(seqClass, resultClass, context)
        val seqParamType = treeFunc.getParameterType(1)

        val treeAggregateLocal = new JimpleLocal("treeAggregateLocal3", seqParamType)
        val treeParams = new util.ArrayList[Value]()
        treeParams.add(zeroValueLocal)
        treeParams.add(prevValueLocal)
        val treeAssignment = new JAssignStmt(treeAggregateLocal, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams))
        newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal)
        newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment, currentUnit)
        currentUnit = treeAssignment
        prevValueLocal = treeAggregateLocal
      } else {


        //给resultClass中增加fusionClass中的fields(默认不包含this引用)
        for (field <- fusionClass.getFields) {
          if (!field.getName.equals("serialVersionUID")) {
            resultClass.addField(Utils.cloneSootField(field))
          }
        }

        //TODO 融合构造器
        //TODO 添加apply中引用的方法

        //将当前fusionClass中的方法融入resultClass中
        val applyMethod = getApplyMethod(fusionClass, context)
        val methodBody = Utils.cloneSootBody(applyMethod.getActiveBody)

        //添加locals
        for (local <- methodBody.getLocals) {
          // 不添加thisLocal
          if (local.getType.toString.equals(fusionClass.getName)) {
            local.setType(resultClass.getType)
          }
          newLoopMethod.getActiveBody.getLocals.addLast(local)
        }

        //添加units

        val funcUnits = methodBody.getUnits

        //假设只有一个参数
        val methodParam = applyMethod.getParameterTypes.get(0)
        var filterResult: JimpleLocal = null
        var tempPrevLocal = prevValueLocal
        if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
          val tuple2Class = context.sootClass("scala.Tuple2")
          val tupleValue = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
          val tupleValueAssign = new JAssignStmt(tupleValue, new JVirtualInvokeExpr(prevValueLocal, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
          newLoopMethod.getActiveBody.getLocals.add(tupleValue)
          newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign, currentUnit)
          prevValueLocal = tupleValue
          currentUnit = tupleValueAssign
        }
        for (funcUnit <- funcUnits) {
          var needInsert = true
          funcUnit match {
            case _: JIdentityStmt =>

              val jIdentityStmt = funcUnit.asInstanceOf[JIdentityStmt]
              if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
                val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                val assignStmt = new JAssignStmt(toLocal, thisLocal)
                newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, lastIdentityUnit)
                needInsert = false
              }
              if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
                val paramRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
                if (paramRef.getType == methodParam) {
                  val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                  var assignStmt: SootUnit = null
                  if (paramRef.getType.isInstanceOf[PrimType]) {
                    assignStmt = new JAssignStmt(toLocal, DoubleConstant.v(1))
                  } else {
                    assignStmt = new JAssignStmt(toLocal, new JCastExpr(prevValueLocal, methodParam))
                  }
                  prevValueLocal = toLocal
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, currentUnit)
                  currentUnit = assignStmt
                  needInsert = false
                }
              }

            case _: JAssignStmt =>
              val jAssignStmt = funcUnit.asInstanceOf[JAssignStmt]
              val leftOp: Value = jAssignStmt.getRightOp
              val rightOp: Value = jAssignStmt.getLeftOp
              val newLeft = modifyUnit(resultClass, fusionClass, leftOp, thisLocal)
              val newRight = modifyUnit(resultClass, fusionClass, rightOp, thisLocal)

            case _: JInvokeStmt =>
              val jInvokeStmt = funcUnit.asInstanceOf[JInvokeStmt]
              val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
              if (invokeMethodRef.declaringClass().getName.equals(fusionClass.getName)) {
                val newInvokeMethodRef = resultClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
                jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
              }

            case _: JIfStmt =>
              //TODO if语句直接忽略，不影响指针分析结果, 但影响转换
              needInsert = false

            case _: JThrowStmt =>
              needInsert = false

            case _: JGotoStmt =>
              needInsert = false

            case _: JReturnStmt =>
              val jReturnStmt = funcUnit.asInstanceOf[JReturnStmt]
              if (jReturnStmt.getOp.isInstanceOf[Constant]) {
                //防止返回的值是常量 不能把它赋给jimpleLocal，需要设置一个临时变量
                val tempConstantLocal = new JimpleLocal("tempConstant", jReturnStmt.getOp.getType)
                val assignReturnUnit = new JAssignStmt(tempConstantLocal, jReturnStmt.getOp)
                newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal)
                newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit, currentUnit)
                currentUnit = assignReturnUnit

                if (!filterFuncs.contains(funcClass)) {
                  prevValueLocal = tempConstantLocal
                } else {
                  filterResult = tempConstantLocal
                }
              } else {
                val returnLocal = jReturnStmt.getOp.asInstanceOf[JimpleLocal]
                if (!filterFuncs.contains(funcClass)) {
                  prevValueLocal = returnLocal
                } else {
                  filterResult = returnLocal
                }
              }
              needInsert = false

            case _ =>

          }

          if (needInsert) {
            newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit, currentUnit)
            currentUnit = funcUnit
          }

        }
        if (filterFuncs.contains(funcClass)) {
          val conditionExpr = new JEqExpr(filterResult, IntConstant.v(0))
          val jGotoStmt = new JIfStmt(conditionExpr, Jimple.v().newStmtBox(restartUnit))
          newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt, currentUnit)
          currentUnit = jGotoStmt
        }

        if (mapValuesFuncs.contains(funcClass)) {
          prevValueLocal = tempPrevLocal
        }

        funcIndex += 1

      }
    }

    writeElementUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.setArg(0, prevValueLocal)
    newLoopMethod.getActiveBody.getUnits.remove(castToIntUnit)

    finishResultClass(resultClass, context)


    LocalNameStandardizer.v().transform(newLoopMethod.getActiveBody, "ji.lns")
    resultClass.setApplicationClass()

    resultClass

  }

  def transformShufflePhase(context: Context, phase: Phase,
                            writeCacheFuncs: mutable.Queue[String], readCacheFuncs: mutable.Queue[String]): SootClass = {
    //TODO 暂时未测试
    val resultClass: SootClass = initResultClass(phase, context)

    val newLoopMethod = getApplyMethod(resultClass, context)
    val loopMethodLocals = newLoopMethod.getActiveBody.getLocals

    //获得本对象的引用
    var thisLocal: Local = null
    for (local <- loopMethodLocals) {
      if (local.getType.toString.equals(resultClass.getName)) {
        thisLocal = local
      }
    }

    val loopMethodUnits = newLoopMethod.getActiveBody.getUnits

    val unitBoxList = newLoopMethod.getActiveBody.getUnitBoxes(true)

    val writeCacheStartUnit = unitBoxList.get(0).getUnit
    val returnUnit = unitBoxList.get(1).getUnit
    val readCacheStartUnit1 = unitBoxList.get(2).getUnit
    val readCacheStartUnit2 = unitBoxList.get(6).getUnit
    val commonStartUnit = loopMethodUnits.getPredOf(readCacheStartUnit1)

    //若cache存在直接读cache label1
    val ifGotoUnit1 = loopMethodUnits.getSuccOf(readCacheStartUnit1)
    val getNextUnit1 = loopMethodUnits.getSuccOf(ifGotoUnit1)
    val valueCastUnit1 = loopMethodUnits.getSuccOf(getNextUnit1)
    val shuffleManagerUnit1 = loopMethodUnits.getSuccOf(valueCastUnit1)
    val writeElementUnit1 = loopMethodUnits.getSuccOf(shuffleManagerUnit1)
    var preValueLocal1 = getNextUnit1.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    var currentUnit1: SootUnit = getNextUnit1


    //若cache不存在，读刚刚写的cache label4
    val ifGotoUnit2 = loopMethodUnits.getSuccOf(readCacheStartUnit2)
    val getNextUnit2 = loopMethodUnits.getSuccOf(ifGotoUnit2)
    val valueCastUnit2 = loopMethodUnits.getSuccOf(getNextUnit2)
    val shuffleManagerUnit2 = loopMethodUnits.getSuccOf(valueCastUnit2)
    val writeElementUnit2 = loopMethodUnits.getSuccOf(shuffleManagerUnit2)
    var preValueLocal2 = getNextUnit2.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    var currentUnit2: SootUnit = getNextUnit2


    //融合读取cache的unit
    for (funcClass <- readCacheFuncs) {
      //排除掉cogroup方法
      if (funcClass != null && !funcClass.contains("cogroup") && !funcClass.contains("join")) {
        //调用了treeAggregate的地方
        if (IteratorFusion.treeAggregateMap.contains(funcClass)) {
          println("!!!!mllib the zeroValue is " + MLDataProduce.typeName)
          val treeAggregateInfo = treeAggregateMap(funcClass)
          val zeroValueClass = context.sootClass(treeAggregateInfo.zeroValueName)
          context.loadClass("cn.edu.hust.grid.deca.MLDataProduce")
          val mlDataProduceClass = context.sootClass("cn.edu.hust.grid.deca.MLDataProduce")
          val getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getZeroValue")
          val args = new util.ArrayList[Value]()
          //添加zeroValue 即初始值 在循环体外
          val zeroValueLocal = new JimpleLocal("zeroValue", zeroValueClass.getType)
          val zeroValueAssign = new JAssignStmt(zeroValueLocal, new JStaticInvokeExpr(getDataMethod.makeRef(), args))
          newLoopMethod.getActiveBody.getLocals.add(zeroValueLocal)
          newLoopMethod.getActiveBody.getUnits.insertAfter(zeroValueAssign, commonStartUnit)

          val seqClass = context.sootClass(treeAggregateInfo.seqName)
          val treeFunc = genTreeAggregateFunc(seqClass, resultClass, context)
          val seqParamType = treeFunc.getParameterType(1)

          val treeAggregateLocal1 = new JimpleLocal("treeAggregateLocal1", seqParamType)
          val treeParams1 = new util.ArrayList[Value]()
          treeParams1.add(zeroValueLocal)
          treeParams1.add(preValueLocal1)
          val treeAssignment1 = new JAssignStmt(treeAggregateLocal1, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams1))
          newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal1)
          newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment1, currentUnit1)
          currentUnit1 = treeAssignment1
          preValueLocal1 = treeAggregateLocal1

          val treeAggregateLocal2 = new JimpleLocal("treeAggregateLocal2", seqParamType)
          val treeParams2 = new util.ArrayList[Value]()
          treeParams2.add(zeroValueLocal)
          treeParams2.add(preValueLocal2)
          val treeAssignment2 = new JAssignStmt(treeAggregateLocal2, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams2))
          newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal2)
          newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment2, currentUnit2)
          currentUnit2 = treeAssignment2
          preValueLocal2 = treeAggregateLocal2

        } else if (mapPartitionsFuncs.contains(funcClass)) {
          var getDataMethod: SootMethod = null
          if (DAGAnalyzer.appName.equals("ChiSqSelectorExample")) {
            val mlDataProduceClass = context.sootClass("org.apache.spark.mllib.SimulatePartitionData")
            getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getChiSqValue")
          } else {
            val mlDataProduceClass = context.sootClass("org.apache.spark.mllib.SimulatePartitionData")
            getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getTreeClassifyValue")
          }
          val partitionsLocal1 = new JimpleLocal("partitionsLocal1", getDataMethod.getReturnType)
          val params1 = new util.ArrayList[Value]()
          val partitionsAssignment1 = new JAssignStmt(partitionsLocal1, new JStaticInvokeExpr(getDataMethod.makeRef(), params1))
          newLoopMethod.getActiveBody.getLocals.add(partitionsLocal1)
          newLoopMethod.getActiveBody.getUnits.insertAfter(partitionsAssignment1, currentUnit1)
          currentUnit1 = partitionsAssignment1
          preValueLocal1 = partitionsLocal1

          val partitionsLocal2 = new JimpleLocal("partitionsLocal2", getDataMethod.getReturnType)
          val params2 = new util.ArrayList[Value]()
          val partitionsAssignment2 = new JAssignStmt(partitionsLocal2, new JStaticInvokeExpr(getDataMethod.makeRef(), params2))
          newLoopMethod.getActiveBody.getLocals.add(partitionsLocal2)
          newLoopMethod.getActiveBody.getUnits.insertAfter(partitionsAssignment2, currentUnit2)
          currentUnit2 = partitionsAssignment2
          preValueLocal2 = partitionsLocal2
        } else {

          val fusionClass = context.sootClass(funcClass)

          for (field <- fusionClass.getFields) {
            if (!field.getName.equals("serialVersionUID")) {
              resultClass.addField(Utils.cloneSootField(field))
            }
          }

          //TODO 融合构造器
          //TODO 添加apply中引用的方法
          val applyMethod = getApplyMethod(fusionClass, context)
          val methodBody = Utils.cloneSootBody(applyMethod.getActiveBody)
          //添加locals
          for (local <- methodBody.getLocals) {
            // 不添加thisLocal
            if (local.getType.toString.equals(fusionClass.getName)) {
              local.setType(resultClass.getType)
            }
            newLoopMethod.getActiveBody.getLocals.addLast(local)
          }
          //添加units
          val funcUnits = methodBody.getUnits
          //假设只有一个参数
          val methodParam = applyMethod.getParameterTypes.get(0)
          var filterResult1: JimpleLocal = null
          var filterResult2: JimpleLocal = null

          // 如果是mapValues算子
          var tempPrevLocal1 = preValueLocal1
          var tempPrevLocal2 = preValueLocal2
          if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
            val tuple2Class = context.sootClass("scala.Tuple2")
            val tupleValue1 = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
            val tupleValueAssign1 = new JAssignStmt(tupleValue1, new JVirtualInvokeExpr(preValueLocal1, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(tupleValue1)
            newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign1, currentUnit1)
            preValueLocal1 = tupleValue1
            currentUnit1 = tupleValueAssign1

            val tupleValue2 = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
            val tupleValueAssign2 = new JAssignStmt(tupleValue2, new JVirtualInvokeExpr(preValueLocal2, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(tupleValue2)
            newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign2, currentUnit2)

            preValueLocal2 = tupleValue2
            currentUnit2 = tupleValueAssign2

          }

          var flatMapFuncLocal: JimpleLocal = null

          var stopLoop: Boolean = false
          var flatMapStmt: SootUnit = null

          for (funcUnit <- funcUnits if !stopLoop) {
            var funcUnit2: SootUnit = null
            var needInsert = true
            funcUnit match {
              case _: JIdentityStmt =>

                val jIdentityStmt = funcUnit.asInstanceOf[JIdentityStmt]
                if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
                  val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                  val assignStmt1 = new JAssignStmt(toLocal, thisLocal)
                  val assignStmt2 = new JAssignStmt(toLocal, thisLocal)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt1, commonStartUnit)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt2, commonStartUnit)
                  needInsert = false
                }
                if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
                  val paramRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
                  if (paramRef.getType == methodParam) {
                    // TODO 这里toLocal是不是需要有2个？
                    val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                    var assignStmt1: SootUnit = null
                    if (paramRef.getType.isInstanceOf[PrimType]) {
                      assignStmt1 = new JAssignStmt(toLocal, DoubleConstant.v(1))
                    } else {
                      assignStmt1 = new JAssignStmt(toLocal, new JCastExpr(preValueLocal1, methodParam))
                    }
                    preValueLocal1 = toLocal
                    newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt1, currentUnit1)
                    currentUnit1 = assignStmt1

                    var assignStmt2: SootUnit = null
                    if (paramRef.getType.isInstanceOf[PrimType]) {
                      assignStmt2 = new JAssignStmt(toLocal, DoubleConstant.v(1))
                    } else {
                      assignStmt2 = new JAssignStmt(toLocal, new JCastExpr(preValueLocal2, methodParam))
                    }
                    preValueLocal2 = toLocal
                    newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt2, currentUnit2)
                    currentUnit2 = assignStmt2
                    needInsert = false
                  }
                }

              case _: JIfStmt =>
                //TODO if语句直接忽略，不影响指针分析结果, 但影响转换
                needInsert = false

              case _: JThrowStmt =>
                needInsert = false

              case _: JGotoStmt =>
                needInsert = false

              case _: JAssignStmt =>
                val jAssignStmt = funcUnit.asInstanceOf[JAssignStmt]
                val leftOp: Value = jAssignStmt.getRightOp
                val rightOp: Value = jAssignStmt.getLeftOp
                modifyUnit(resultClass, fusionClass, leftOp, thisLocal)
                modifyUnit(resultClass, fusionClass, rightOp, thisLocal)

                if (flatMapFuncs.contains(funcClass)) {
                  if (jAssignStmt.getRightOp.isInstanceOf[JInterfaceInvokeExpr]) {
                    val jInterfaceInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JInterfaceInvokeExpr]
                    val methodName = jInterfaceInvokeExpr.getMethod.getName
                    if (methodName.equals("map")) {
                      needInsert = false
                      stopLoop = true
                      flatMapStmt = funcUnit
                      flatMapType = "iterator"
                    }
                  }

                }
                funcUnit2 = jAssignStmt.clone().asInstanceOf[JAssignStmt]

              case _: JInvokeStmt =>
                val jInvokeStmt = funcUnit.asInstanceOf[JInvokeStmt]
                val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
                if (invokeMethodRef.declaringClass().getName.equals(fusionClass.getName)) {
                  val newInvokeMethodRef = resultClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
                  jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
                }
                val methodName = jInvokeStmt.getInvokeExpr.getMethod.getName
                val args = jInvokeStmt.getInvokeExpr.getArgs
                //找到init方法
                var argIndex = 0
                for (arg <- args) {
                  if (arg.getType == resultClass.getType && methodName.equals("<init>")) {
                    jInvokeStmt.getInvokeExpr.setArg(argIndex, NullConstant.v())
                    flatMapFuncLocal = jInvokeStmt.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr].getBase.asInstanceOf[JimpleLocal]
                    flatMapType = "iterator"
                  }
                  argIndex += 1
                }

                if (flatMapFuncs.contains(funcClass)) {
                  // 当有flatMap算子时，迭代融合需要处理掉函数对象
                  val methodName = jInvokeStmt.getInvokeExpr.getMethod.getName
                  val args = jInvokeStmt.getInvokeExpr.getArgs
                  //找到init方法
                  var argIndex = 0
                  for (arg <- args) {
                    if (arg.getType == resultClass.getType && methodName.equals("<init>")) {
                      jInvokeStmt.getInvokeExpr.setArg(argIndex, NullConstant.v())
                      flatMapFuncLocal = jInvokeStmt.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr].getBase.asInstanceOf[JimpleLocal]
                      flatMapType = "iterator"
                    }
                    argIndex += 1
                  }
                }
                funcUnit2 = jInvokeStmt.clone().asInstanceOf[JInvokeStmt]


              case _: JReturnStmt =>
                val jReturnStmt = funcUnit.asInstanceOf[JReturnStmt]
                if (jReturnStmt.getOp.isInstanceOf[Constant]) {
                  //防止返回的值是常量 不能把它赋给jimpleLocal，需要设置一个临时变量

                  val tempConstantLocal1 = new JimpleLocal("tempConstant1", jReturnStmt.getOp.getType)
                  val assignReturnUnit1 = new JAssignStmt(tempConstantLocal1, jReturnStmt.getOp)
                  val tempConstantLocal2 = new JimpleLocal("tempConstant2", jReturnStmt.getOp.getType)
                  val assignReturnUnit2 = new JAssignStmt(tempConstantLocal2, jReturnStmt.getOp)
                  newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal1)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit1, currentUnit1)
                  newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal2)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit2, currentUnit2)
                  currentUnit1 = assignReturnUnit1
                  currentUnit2 = assignReturnUnit2


                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal1 = tempConstantLocal1
                    preValueLocal2 = tempConstantLocal2
                  } else {
                    filterResult1 = tempConstantLocal1
                    filterResult2 = tempConstantLocal2
                  }

                  //throw OptimizeException("上一个返回的居然是常量")
                } else {
                  val returnLocal = jReturnStmt.getOp.asInstanceOf[JimpleLocal]
                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal1 = returnLocal
                    preValueLocal2 = returnLocal
                  } else {
                    filterResult1 = returnLocal
                    filterResult2 = returnLocal
                  }
                }

                needInsert = false


              case _ =>

            }

            if (needInsert) {
              newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit, currentUnit1)
              currentUnit1 = funcUnit

              newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit2, currentUnit2)
              currentUnit2 = funcUnit2
            }

          }

          if (filterFuncs.contains(funcClass)) {
            val conditionExpr1 = new JEqExpr(filterResult1, IntConstant.v(0))
            val jGotoStmt1 = new JIfStmt(conditionExpr1, Jimple.v().newStmtBox(readCacheStartUnit1))
            newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt1, currentUnit1)
            currentUnit1 = jGotoStmt1

            val conditionExpr2 = new JEqExpr(filterResult2, IntConstant.v(0))
            val jGotoStmt2 = new JIfStmt(conditionExpr2, Jimple.v().newStmtBox(readCacheStartUnit2))
            newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt2, currentUnit2)
            currentUnit2 = jGotoStmt2
          }

          if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
            preValueLocal1 = tempPrevLocal1
            preValueLocal2 = tempPrevLocal2
          }


          if (flatMapFuncs.contains(funcClass) && flatMapType.equals("iterator")) {
            val assignment = flatMapStmt.asInstanceOf[JAssignStmt]
            val invokeExpr = assignment.getRightOp.asInstanceOf[JInterfaceInvokeExpr]
            val methodName = invokeExpr.getMethod.getName
            //找到map方法
            if (methodName.equals("map")) {
              if (flatMapFuncLocal == null) {
                throw OptimizeException("flatMapLocal is null!!!!!!!!!!!!")
              }


              val flatMapFuncType = flatMapFuncLocal.getType
              val flatMapFuncClass = context.sootClass(flatMapFuncType.toString)
              val applyMethod = getApplyMethod(flatMapFuncClass, context)
              val resultType = applyMethod.getReturnType
              val getIterValueMethod = context.sootClass("cn.edu.hust.grid.deca.iter.ShuffleData").getMethodByName("getIntIterValue")
              val iterableLocal = invokeExpr.asInstanceOf[JInterfaceInvokeExpr].getBase

              val iterableValueLocal1 = new JimpleLocal("iterableValue1", IntType.v())
              val flatMapResultLocal1 = new JimpleLocal("flatMapResult1", resultType)
              val tempArgs1 = new util.ArrayList[Value]()
              tempArgs1.add(iterableLocal)
              val getNextValueUnit1 = new JAssignStmt(iterableValueLocal1, new JStaticInvokeExpr(getIterValueMethod.makeRef(), tempArgs1))
              val resultArgs1 = new util.ArrayList[Value]()
              resultArgs1.add(iterableValueLocal1)
              //改变这个函数调用语句
              val newJInvokeStmt1 = new JAssignStmt(flatMapResultLocal1, new JVirtualInvokeExpr(flatMapFuncLocal, applyMethod.makeRef(), resultArgs1))

              newLoopMethod.getActiveBody.getLocals.add(iterableValueLocal1)
              newLoopMethod.getActiveBody.getLocals.add(flatMapResultLocal1)

              newLoopMethod.getActiveBody.getUnits.insertAfter(getNextValueUnit1, currentUnit1)
              currentUnit1 = getNextValueUnit1
              newLoopMethod.getActiveBody.getUnits.insertAfter(newJInvokeStmt1, currentUnit1)
              currentUnit1 = newJInvokeStmt1
              preValueLocal1 = flatMapResultLocal1


              val iterableValueLocal2 = new JimpleLocal("iterableValue2", IntType.v())
              val flatMapResultLocal2 = new JimpleLocal("flatMapResult2", resultType)
              val tempArgs2 = new util.ArrayList[Value]()
              tempArgs2.add(iterableLocal)
              val getNextValueUnit2 = new JAssignStmt(iterableValueLocal2, new JStaticInvokeExpr(getIterValueMethod.makeRef(), tempArgs2))
              val resultArgs2 = new util.ArrayList[Value]()
              resultArgs2.add(iterableValueLocal2)
              //改变这个函数调用语句
              val newJInvokeStmt2 = new JAssignStmt(flatMapResultLocal2, new JVirtualInvokeExpr(flatMapFuncLocal, applyMethod.makeRef(), resultArgs2))

              newLoopMethod.getActiveBody.getLocals.add(iterableValueLocal2)
              newLoopMethod.getActiveBody.getLocals.add(flatMapResultLocal2)

              newLoopMethod.getActiveBody.getUnits.insertAfter(getNextValueUnit2, currentUnit2)
              currentUnit2 = getNextValueUnit2
              newLoopMethod.getActiveBody.getUnits.insertAfter(newJInvokeStmt2, currentUnit2)
              currentUnit2 = newJInvokeStmt2
              preValueLocal2 = flatMapResultLocal2

            }

          } else if (flatMapFuncs.contains(funcClass) && flatMapType.equals("seq")) {
            //flatMap中是arrayOps，map等集合结构
            val getIterValueMethod = context.sootClass("cn.edu.hust.grid.deca.iter.ShuffleData").getMethodByName("getSeqValue")

            val arrayOpValue1 = new JimpleLocal("singleResult1", context.sootClass("java.lang.Object").getType)
            val opArgs1 = new util.ArrayList[Value]()
            opArgs1.add(preValueLocal1)
            val opAssignment1 = new JAssignStmt(arrayOpValue1, new JStaticInvokeExpr(getIterValueMethod.makeRef(), opArgs1))

            val arrayOpValue2 = new JimpleLocal("singleResult2", context.sootClass("java.lang.Object").getType)
            val opArgs2 = new util.ArrayList[Value]()
            opArgs2.add(preValueLocal2)
            val opAssignment2 = new JAssignStmt(arrayOpValue2, new JStaticInvokeExpr(getIterValueMethod.makeRef(), opArgs2))

            newLoopMethod.getActiveBody.getLocals.add(arrayOpValue1)
            newLoopMethod.getActiveBody.getLocals.add(arrayOpValue2)

            newLoopMethod.getActiveBody.getUnits.insertAfter(opAssignment1, currentUnit1)
            currentUnit1 = opAssignment1
            preValueLocal1 = arrayOpValue1
            newLoopMethod.getActiveBody.getUnits.insertAfter(opAssignment2, currentUnit2)
            currentUnit2 = opAssignment2
            preValueLocal2 = arrayOpValue2
          }


          //TODO 仅仅适用于pagerank的join，并不通用，以后实现通用,合成(Int,(Iterable(Int),Double)),直接凭空new出数据
          if (DAGAnalyzer.joinRDDFuncMap.contains(funcClass)) {
            val tupleClass = context.sootClass("scala.Tuple2")
            val shuffleDataClass = context.sootClass("cn.edu.hust.grid.deca.iter.ShuffleData")
            val readTupleMethod = shuffleDataClass.getMethodByNameUnsafe("getTupleFromPR")
            val joinLocal1 = new JimpleLocal("joinResult1", tupleClass.getType)
            val newUnit1 = new JAssignStmt(joinLocal1, new JStaticInvokeExpr(readTupleMethod.makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(joinLocal1)
            newLoopMethod.getActiveBody.getUnits.insertAfter(newUnit1, currentUnit1)
            currentUnit1 = newUnit1
            preValueLocal1 = joinLocal1


            val joinLocal2 = new JimpleLocal("joinResult2", tupleClass.getType)
            val newUnit2 = new JAssignStmt(joinLocal2, new JStaticInvokeExpr(readTupleMethod.makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(joinLocal2)
            newLoopMethod.getActiveBody.getUnits.insertAfter(newUnit2, currentUnit2)
            currentUnit2 = newUnit2
            preValueLocal2 = joinLocal2

          }
        }
      }

    }

    writeElementUnit1.asInstanceOf[JInvokeStmt].getInvokeExpr.setArg(0, preValueLocal1)
    writeElementUnit2.asInstanceOf[JInvokeStmt].getInvokeExpr.setArg(0, preValueLocal2)


    //若cache不存在，写cache label2
    val ifGotoUnit3 = loopMethodUnits.getSuccOf(writeCacheStartUnit)
    val getNextUnit3 = loopMethodUnits.getSuccOf(ifGotoUnit3)
    val valueCastUnit3 = loopMethodUnits.getSuccOf(getNextUnit3)
    val blockManagerUnit3 = loopMethodUnits.getSuccOf(valueCastUnit3)
    val writeElementUnit3 = loopMethodUnits.getSuccOf(blockManagerUnit3)
    var preValueLocal3 = getNextUnit3.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    var currentUnit3: SootUnit = getNextUnit3

    //融合写cache的unit
    for (funcClass <- writeCacheFuncs) {
      if (funcClass != null && !funcClass.contains("cogroup") && !funcClass.contains("join")) {
        if (IteratorFusion.treeAggregateMap.contains(funcClass)) {
          val treeAggregateInfo = treeAggregateMap(funcClass)
          val zeroValueClass = context.sootClass(treeAggregateInfo.zeroValueName)
          context.loadClass("cn.edu.hust.grid.deca.MLDataProduce")
          val mlDataProduceClass = context.sootClass("cn.edu.hust.grid.deca.MLDataProduce")
          val getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getZeroValue")
          val args = new util.ArrayList[Value]()
          //添加zeroValue 即初始值 在循环体外
          val zeroValueLocal = new JimpleLocal("zeroValue", zeroValueClass.getType)
          val zeroValueAssign = new JAssignStmt(zeroValueLocal, new JStaticInvokeExpr(getDataMethod.makeRef(), args))
          newLoopMethod.getActiveBody.getLocals.add(zeroValueLocal)
          newLoopMethod.getActiveBody.getUnits.insertAfter(zeroValueAssign, commonStartUnit)

          val seqClass = context.sootClass(treeAggregateInfo.seqName)
          val treeFunc = genTreeAggregateFunc(seqClass, resultClass, context)
          val seqParamType = treeFunc.getParameterType(1)

          val treeAggregateLocal3 = new JimpleLocal("treeAggregateLocal3", seqParamType)
          val treeParams3 = new util.ArrayList[Value]()
          treeParams3.add(zeroValueLocal)
          treeParams3.add(preValueLocal3)
          val treeAssignment3 = new JAssignStmt(treeAggregateLocal3, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams3))
          newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal3)
          newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment3, currentUnit3)
          currentUnit3 = treeAssignment3
          preValueLocal3 = treeAggregateLocal3
        } else {
          val fusionClass = context.sootClass(funcClass)

          for (field <- fusionClass.getFields) {
            if (!field.getName.equals("serialVersionUID")) {
              resultClass.addField(Utils.cloneSootField(field))
            }
          }

          //TODO 融合构造器
          //TODO 添加apply中引用的方法
          val applyMethod = getApplyMethod(fusionClass, context)
          val methodBody = Utils.cloneSootBody(applyMethod.getActiveBody)
          //添加locals
          for (local <- methodBody.getLocals) {
            // 不添加thisLocal
            if (local.getType.toString.equals(fusionClass.getName)) {
              local.setType(resultClass.getType)
            }
            newLoopMethod.getActiveBody.getLocals.addLast(local)
          }
          //添加units
          val funcUnits = methodBody.getUnits
          //假设只有一个参数
          val methodParam = applyMethod.getParameterTypes.get(0)
          var filterResult3: JimpleLocal = null


          // 如果是mapValues算子
          var tempPrevLocal3 = preValueLocal3
          if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
            val tuple2Class = context.sootClass("scala.Tuple2")
            val tupleValue3 = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
            val tupleValueAssign3 = new JAssignStmt(tupleValue3, new JVirtualInvokeExpr(preValueLocal3, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(tupleValue3)
            newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign3, currentUnit3)
            preValueLocal3 = tupleValue3
            currentUnit3 = tupleValueAssign3
          }

          for (funcUnit <- funcUnits) {
            var needInsert = true
            funcUnit match {
              case _: JIdentityStmt =>

                val jIdentityStmt = funcUnit.asInstanceOf[JIdentityStmt]
                if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
                  val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                  val assignStmt = new JAssignStmt(toLocal, thisLocal)

                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, commonStartUnit)
                  needInsert = false
                }
                if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
                  val paramRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
                  if (paramRef.getType == methodParam) {
                    val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                    var assignStmt: SootUnit = null
                    if (paramRef.getType.isInstanceOf[PrimType]) {
                      assignStmt = new JAssignStmt(toLocal, DoubleConstant.v(1))
                    } else {
                      assignStmt = new JAssignStmt(toLocal, new JCastExpr(preValueLocal3, methodParam))
                    }
                    //TODO filter存在隐患
                    preValueLocal3 = toLocal
                    newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, currentUnit3)
                    currentUnit3 = assignStmt
                    needInsert = false
                  }
                }

              case _: JAssignStmt =>
                val jAssignStmt = funcUnit.asInstanceOf[JAssignStmt]
                val leftOp: Value = jAssignStmt.getRightOp
                val rightOp: Value = jAssignStmt.getLeftOp
                modifyUnit(resultClass, fusionClass, leftOp, thisLocal)
                modifyUnit(resultClass, fusionClass, rightOp, thisLocal)

              case _: JInvokeStmt =>
                val jInvokeStmt = funcUnit.asInstanceOf[JInvokeStmt]
                val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
                if (invokeMethodRef.declaringClass().getName.equals(fusionClass.getName)) {
                  val newInvokeMethodRef = resultClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
                  jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
                }

              case _: JIfStmt =>
                //TODO if语句直接忽略，不影响指针分析结果, 但影响转换
                needInsert = false

              case _: JThrowStmt =>
                needInsert = false

              case _: JGotoStmt =>
                needInsert = false

              case _: JReturnStmt =>
                val jReturnStmt = funcUnit.asInstanceOf[JReturnStmt]

                if (jReturnStmt.getOp.isInstanceOf[Constant]) {
                  //防止返回的值是常量 不能把它赋给jimpleLocal，需要设置一个临时变量
                  val tempConstantLocal3 = new JimpleLocal("tempConstant3", jReturnStmt.getOp.getType)
                  val assignReturnUnit3 = new JAssignStmt(tempConstantLocal3, jReturnStmt.getOp)
                  newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal3)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit3, currentUnit3)
                  currentUnit3 = assignReturnUnit3

                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal3 = tempConstantLocal3
                  } else {
                    filterResult3 = tempConstantLocal3
                  }
                  //throw OptimizeException("上一个返回的居然是常量")
                } else {
                  val returnLocal = jReturnStmt.getOp.asInstanceOf[JimpleLocal]
                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal3 = returnLocal
                  } else {
                    filterResult3 = returnLocal
                  }
                }
                needInsert = false

              case _ =>

            }

            if (needInsert) {
              newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit, currentUnit3)
              currentUnit3 = funcUnit
            }
          }

          if (filterFuncs.contains(funcClass)) {
            val conditionExpr3 = new JEqExpr(filterResult3, IntConstant.v(0))
            val jGotoStmt3 = new JIfStmt(conditionExpr3, Jimple.v().newStmtBox(writeCacheStartUnit))
            newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt3, currentUnit3)
            currentUnit3 = jGotoStmt3
          }

          if (mapValuesFuncs.contains(funcClass)) {
            preValueLocal3 = tempPrevLocal3
          }

        }
      }
    }
    writeElementUnit3.asInstanceOf[JInvokeStmt].getInvokeExpr.setArg(0, preValueLocal3)
    newLoopMethod.getActiveBody.getUnits.remove(valueCastUnit1)
    newLoopMethod.getActiveBody.getUnits.remove(valueCastUnit2)
    newLoopMethod.getActiveBody.getUnits.remove(valueCastUnit3)


    finishResultClass(resultClass, context)

    LocalNameStandardizer.v().transform(newLoopMethod.getActiveBody, "ji.lns")
    resultClass.setApplicationClass()

    resultClass
  }


  /**
    * 针对无cache的ResultStage进行迭代的融合
    * 当前只能处理reduce api
    * 因为其他action api已知，后续加起来难度不大
    *
    * @param context
    * @param resultFuncClass
    */
  def transformResultPhase(context: Context, resultFuncClass: SootClass, phase: Phase, resultFuncType: ResultType): SootClass = {
    val fusionFuncList = context.fusionClassList
    val resultClass: SootClass = initResultClass(phase, context)

    val newLoopMethod = getApplyMethod(resultClass, context)

    val loopMethodLocals = newLoopMethod.getActiveBody.getLocals

    //获得本对象的引用
    var thisLocal: Local = null
    for (local <- loopMethodLocals) {
      if (local.getType.toString.equals(resultClass.getName)) {
        thisLocal = local
      }
    }

    val loopMethodUnits = newLoopMethod.getActiveBody.getUnits
    var forStartUnit: SootUnit = null
    var forEndUnit: SootUnit = null
    var readValueUnit: SootUnit = null
    var unBoxValueUnit: SootUnit = null
    var lastIdentityUnit: SootUnit = null
    var returnResultUnit: SootUnit = null
    var sumUnit: SootUnit = null

    val unitBoxes = newLoopMethod.getActiveBody.getAllUnitBoxes
    val restartUnit = unitBoxes.get(1).getUnit

    for (unit <- loopMethodUnits) {
      unit match {
        case _: JIfStmt =>
          forStartUnit = unit.asInstanceOf[JIfStmt]
        case _: JGotoStmt =>
          forEndUnit = unit.asInstanceOf[JGotoStmt]
        case _: JAssignStmt =>
          val assignStmt = unit.asInstanceOf[JAssignStmt]
          if (assignStmt.containsInvokeExpr()) {
            if (assignStmt.getInvokeExpr.getMethod.getName.equals("next")) {
              readValueUnit = unit.asInstanceOf[JAssignStmt]
            } else if (assignStmt.getInvokeExpr.getMethod.getName.equals("unboxToInt")) {
              unBoxValueUnit = unit.asInstanceOf[JAssignStmt]
              sumUnit = loopMethodUnits.getSuccOf(unBoxValueUnit)
            }
          }
        case _: JIdentityStmt =>
          lastIdentityUnit = unit

        case _: JReturnStmt =>
          returnResultUnit = unit

        case _ =>

      }

    }
    var funcIndex = 0
    var currentUnit = readValueUnit
    var prevValueLocal = readValueUnit.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    for (funcClass <- fusionFuncList) {
      println("handle fusion of the funcClass:" + funcClass)
      val fusionClass = context.sootClass(funcClass)

      //给resultClass中增加fusionClass中的fields(默认不包含this引用)
      for (field <- fusionClass.getFields) {
        if (!field.getName.equals("serialVersionUID")) {
          resultClass.addField(Utils.cloneSootField(field))
        }
      }

      //TODO 融合构造器
      //TODO 添加apply中引用的方法

      //将当前fusionClass中的方法融入resultClass中
      val applyMethod = getApplyMethod(fusionClass, context)
      val methodBody = Utils.cloneSootBody(applyMethod.getActiveBody)

      //添加locals
      for (local <- methodBody.getLocals) {
        // 不添加thisLocal
        if (local.getType.toString.equals(fusionClass.getName)) {
          local.setType(resultClass.getType)
        }
        newLoopMethod.getActiveBody.getLocals.addLast(local)
      }

      //添加units

      val funcUnits = methodBody.getUnits

      //假设只有一个参数
      val methodParam = applyMethod.getParameterTypes.get(0)
      var filterResult: JimpleLocal = null
      // 如果是mapValues算子
      var tempPrevLocal = prevValueLocal
      if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
        val tuple2Class = context.sootClass("scala.Tuple2")
        val tupleValue = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
        val tupleValueAssign = new JAssignStmt(tupleValue, new JVirtualInvokeExpr(prevValueLocal, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
        newLoopMethod.getActiveBody.getLocals.add(tupleValue)
        newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign, currentUnit)
        prevValueLocal = tupleValue
        currentUnit = tupleValueAssign
      }
      for (funcUnit <- funcUnits) {
        var needInsert = true
        funcUnit match {
          case _: JIdentityStmt =>

            val jIdentityStmt = funcUnit.asInstanceOf[JIdentityStmt]
            if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
              val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
              val assignStmt = new JAssignStmt(toLocal, thisLocal)
              newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, lastIdentityUnit)
              needInsert = false
            }
            if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
              val paramRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
              if (paramRef.getType == methodParam) {
                val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                var assignStmt: SootUnit = null
                if (paramRef.getType.isInstanceOf[PrimType]) {
                  assignStmt = new JAssignStmt(toLocal, DoubleConstant.v(1))
                } else {
                  assignStmt = new JAssignStmt(toLocal, new JCastExpr(prevValueLocal, methodParam))
                }
                prevValueLocal = toLocal
                newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, currentUnit)
                currentUnit = assignStmt
                needInsert = false
              }
            }

          case _: JAssignStmt =>
            val jAssignStmt = funcUnit.asInstanceOf[JAssignStmt]
            val leftOp: Value = jAssignStmt.getRightOp
            val rightOp: Value = jAssignStmt.getLeftOp
            val newLeft = modifyUnit(resultClass, fusionClass, leftOp, thisLocal)
            val newRight = modifyUnit(resultClass, fusionClass, rightOp, thisLocal)

          case _: JInvokeStmt =>
            val jInvokeStmt = funcUnit.asInstanceOf[JInvokeStmt]
            val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
            if (invokeMethodRef.declaringClass().getName.equals(fusionClass.getName)) {
              val newInvokeMethodRef = resultClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
              jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
            }

          case _: JIfStmt =>
            //TODO if语句直接忽略，不影响指针分析结果, 但影响转换
            needInsert = false

          case _: JThrowStmt =>
            needInsert = false

          case _: JGotoStmt =>
            needInsert = false

          case _: JReturnStmt =>
            val jReturnStmt = funcUnit.asInstanceOf[JReturnStmt]
            if (jReturnStmt.getOp.isInstanceOf[Constant]) {
              //防止返回的值是常量 不能把它赋给jimpleLocal，需要设置一个临时变量
              val tempConstantLocal = new JimpleLocal("tempConstant", jReturnStmt.getOp.getType)
              val assignReturnUnit = new JAssignStmt(tempConstantLocal, jReturnStmt.getOp)
              newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal)
              newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit, currentUnit)
              currentUnit = assignReturnUnit

              if (!filterFuncs.contains(funcClass)) {
                prevValueLocal = tempConstantLocal
              } else {
                filterResult = tempConstantLocal
              }
            } else {
              val returnLocal = jReturnStmt.getOp.asInstanceOf[JimpleLocal]
              if (!filterFuncs.contains(funcClass)) {
                prevValueLocal = returnLocal
              } else {
                filterResult = returnLocal
              }
            }

            needInsert = false

          case _ =>

        }

        if (needInsert) {
          newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit, currentUnit)
          currentUnit = funcUnit
        }

      }

      if (filterFuncs.contains(funcClass)) {
        val conditionExpr = new JEqExpr(filterResult, IntConstant.v(0))
        val jGotoStmt = new JIfStmt(conditionExpr, Jimple.v().newStmtBox(restartUnit))
        newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt, currentUnit)
        currentUnit = jGotoStmt
      }

      if (mapValuesFuncs.contains(funcClass)) {
        prevValueLocal = tempPrevLocal
      }

      funcIndex += 1

    }


    //融合result方法(reduce的func)
    val reduceFunc = genReduceFunc(resultFuncClass, resultClass, context)

    resultFuncType match {
      case _: IsReduce =>
        if (reduceFunc != null) {
          val returnType = reduceFunc.getReturnType
          newLoopMethod.setReturnType(returnType)

          val returnLocal = new JimpleLocal("finalResult", returnType)
          newLoopMethod.getActiveBody.getLocals.add(returnLocal)
          val reduceFuncArgs = new util.ArrayList[Value]()
          reduceFuncArgs.add(returnLocal)
          reduceFuncArgs.add(prevValueLocal)
          sumUnit.asInstanceOf[JAssignStmt].setLeftOp(returnLocal)
          sumUnit.asInstanceOf[JAssignStmt].setRightOp(new JVirtualInvokeExpr(thisLocal, reduceFunc.makeRef(), reduceFuncArgs))
          returnResultUnit.asInstanceOf[JReturnStmt].setOp(returnLocal)
        } else {
          newLoopMethod.getActiveBody.getUnits.remove(sumUnit)
        }
      case _: IsForEach =>
        if (reduceFunc != null) {
          val returnType = reduceFunc.getReturnType
          newLoopMethod.setReturnType(returnType)
          val returnLocal = new JimpleLocal("finalResult", returnType)
          newLoopMethod.getActiveBody.getLocals.add(returnLocal)
          val reduceFuncArgs = new util.ArrayList[Value]()
          reduceFuncArgs.add(prevValueLocal)
          sumUnit.asInstanceOf[JAssignStmt].setLeftOp(returnLocal)
          sumUnit.asInstanceOf[JAssignStmt].setRightOp(new JVirtualInvokeExpr(thisLocal, reduceFunc.makeRef(), reduceFuncArgs))
          returnResultUnit.asInstanceOf[JReturnStmt].setOp(returnLocal)
        } else {
          newLoopMethod.getActiveBody.getUnits.remove(sumUnit)
        }
      case _ =>
        newLoopMethod.getActiveBody.getUnits.remove(sumUnit)

    }


    newLoopMethod.getActiveBody.getUnits.remove(unBoxValueUnit)

    finishResultClass(resultClass, context)


    LocalNameStandardizer.v().transform(newLoopMethod.getActiveBody, "ji.lns")
    resultClass.setApplicationClass()

    resultClass
  }

  /**
    * 处理包含cache的ResultPhase
    *
    */
  def transformResultPhase(context: Context, resultFuncClass: SootClass, phase: Phase,
                           writeCacheFuncs: mutable.Queue[String], readCacheFuncs: mutable.Queue[String], resultFuncType: ResultType): SootClass = {

    val resultClass: SootClass = initResultClass(phase, context)

    val newLoopMethod = getApplyMethod(resultClass, context)
    val loopMethodLocals = newLoopMethod.getActiveBody.getLocals

    //获得本对象的引用
    var thisLocal: Local = null
    for (local <- loopMethodLocals) {
      if (local.getType.toString.equals(resultClass.getName)) {
        thisLocal = local
      }
    }

    val loopMethodUnits = newLoopMethod.getActiveBody.getUnits

    val unitBoxList = newLoopMethod.getActiveBody.getUnitBoxes(true)

    val writeCacheStartUnit = unitBoxList.get(0).getUnit
    val returnResultUnit = unitBoxList.get(1).getUnit
    val readCacheStartUnit1 = unitBoxList.get(2).getUnit
    val readCacheStartUnit2 = unitBoxList.get(6).getUnit

    val commonStartUnit = loopMethodUnits.getPredOf(readCacheStartUnit1)

    //若cache存在直接读cache label1
    val ifGotoUnit1 = loopMethodUnits.getSuccOf(readCacheStartUnit1)
    val getNextUnit1 = loopMethodUnits.getSuccOf(ifGotoUnit1)
    val valueCastUnit1 = loopMethodUnits.getSuccOf(getNextUnit1)
    val mergeValueUnit1 = loopMethodUnits.getSuccOf(valueCastUnit1)
    var preValueLocal1 = getNextUnit1.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    var currentUnit1: SootUnit = getNextUnit1


    //若cache不存在，读刚刚写的cache label4
    val ifGotoUnit2 = loopMethodUnits.getSuccOf(readCacheStartUnit2)
    val getNextUnit2 = loopMethodUnits.getSuccOf(ifGotoUnit2)
    val valueCastUnit2 = loopMethodUnits.getSuccOf(getNextUnit2)
    val mergeValueUnit2 = loopMethodUnits.getSuccOf(valueCastUnit2)
    var preValueLocal2 = getNextUnit2.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    var currentUnit2: SootUnit = getNextUnit2


    //融合读取cache的unit
    for (funcClass <- readCacheFuncs) {
      if (funcClass != null) {
        //调用了treeAggregate的地方
        if (IteratorFusion.treeAggregateMap.contains(funcClass)) {
          println("!!!!mllib the zeroValue is " + MLDataProduce.typeName)
          val treeAggregateInfo = treeAggregateMap(funcClass)
          val zeroValueClass = context.sootClass(treeAggregateInfo.zeroValueName)
          context.loadClass("cn.edu.hust.grid.deca.MLDataProduce")
          val mlDataProduceClass = context.sootClass("cn.edu.hust.grid.deca.MLDataProduce")
          val getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getZeroValue")
          val args = new util.ArrayList[Value]()
          //添加zeroValue 即初始值 在循环体外
          val zeroValueLocal = new JimpleLocal("zeroValue", zeroValueClass.getType)
          val zeroValueAssign = new JAssignStmt(zeroValueLocal, new JStaticInvokeExpr(getDataMethod.makeRef(), args))
          newLoopMethod.getActiveBody.getLocals.add(zeroValueLocal)
          newLoopMethod.getActiveBody.getUnits.insertAfter(zeroValueAssign, commonStartUnit)

          val seqClass = context.sootClass(treeAggregateInfo.seqName)
          val treeFunc = genTreeAggregateFunc(seqClass, resultClass, context)
          val seqParamType = treeFunc.getParameterType(1)

          val treeAggregateLocal1 = new JimpleLocal("treeAggregateLocal1", seqParamType)
          val treeParams1 = new util.ArrayList[Value]()
          treeParams1.add(zeroValueLocal)
          treeParams1.add(preValueLocal1)
          val treeAssignment1 = new JAssignStmt(treeAggregateLocal1, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams1))
          newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal1)
          newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment1, currentUnit1)
          currentUnit1 = treeAssignment1
          preValueLocal1 = treeAggregateLocal1

          val treeAggregateLocal2 = new JimpleLocal("treeAggregateLocal2", seqParamType)
          val treeParams2 = new util.ArrayList[Value]()
          treeParams2.add(zeroValueLocal)
          treeParams2.add(preValueLocal2)
          val treeAssignment2 = new JAssignStmt(treeAggregateLocal2, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams2))
          newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal2)
          newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment2, currentUnit2)
          currentUnit2 = treeAssignment2
          preValueLocal2 = treeAggregateLocal2

        } else {
          //!!!非treeAggregate的情况
          val fusionClass = context.sootClass(funcClass)

          for (field <- fusionClass.getFields) {
            if (!field.getName.equals("serialVersionUID")) {
              resultClass.addField(Utils.cloneSootField(field))
            }
          }

          //TODO 融合构造器
          //TODO 添加apply中引用的方法
          val applyMethod = getApplyMethod(fusionClass, context)
          val methodBody = Utils.cloneSootBody(applyMethod.getActiveBody)
          //添加locals
          for (local <- methodBody.getLocals) {
            // 不添加thisLocal
            if (local.getType.toString.equals(fusionClass.getName)) {
              local.setType(resultClass.getType)
            }
            newLoopMethod.getActiveBody.getLocals.addLast(local)
          }
          //添加units
          val funcUnits = methodBody.getUnits
          //假设只有一个参数
          val methodParam = applyMethod.getParameterTypes.get(0)
          var filterResult1: JimpleLocal = null
          var filterResult2: JimpleLocal = null
          // 如果是mapValues算子
          var tempPrevLocal1 = preValueLocal1
          var tempPrevLocal2 = preValueLocal2
          if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
            val tuple2Class = context.sootClass("scala.Tuple2")
            val tupleValue1 = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
            val tupleValueAssign1 = new JAssignStmt(tupleValue1, new JVirtualInvokeExpr(preValueLocal1, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(tupleValue1)
            newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign1, currentUnit1)
            preValueLocal1 = tupleValue1
            currentUnit1 = tupleValueAssign1

            val tupleValue2 = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
            val tupleValueAssign2 = new JAssignStmt(tupleValue2, new JVirtualInvokeExpr(preValueLocal2, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(tupleValue2)
            newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign2, currentUnit2)

            preValueLocal2 = tupleValue2
            currentUnit2 = tupleValueAssign2

          }

          for (funcUnit <- funcUnits) {
            var funcUnit2: SootUnit = null
            var needInsert = true
            funcUnit match {
              case _: JIdentityStmt =>

                val jIdentityStmt = funcUnit.asInstanceOf[JIdentityStmt]
                if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
                  val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                  val assignStmt1 = new JAssignStmt(toLocal, thisLocal)
                  val assignStmt2 = new JAssignStmt(toLocal, thisLocal)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt1, commonStartUnit)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt2, commonStartUnit)
                  needInsert = false
                }
                if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
                  val paramRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
                  if (paramRef.getType == methodParam) {
                    val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                    var assignStmt1: SootUnit = null
                    //防止参数是原生类型
                    if (paramRef.getType.isInstanceOf[PrimType]) {
                      assignStmt1 = new JAssignStmt(toLocal, DoubleConstant.v(1))
                    } else {
                      assignStmt1 = new JAssignStmt(toLocal, new JCastExpr(preValueLocal1, methodParam))
                    }
                    preValueLocal1 = toLocal
                    newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt1, currentUnit1)
                    currentUnit1 = assignStmt1
                    var assignStmt2: SootUnit = null
                    if (paramRef.getType.isInstanceOf[PrimType]) {
                      assignStmt2 = new JAssignStmt(toLocal, DoubleConstant.v(1))
                    } else {
                      assignStmt2 = new JAssignStmt(toLocal, new JCastExpr(preValueLocal2, methodParam))
                    }
                    preValueLocal2 = toLocal
                    newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt2, currentUnit2)
                    currentUnit2 = assignStmt2
                    needInsert = false
                  }
                }

              case _: JAssignStmt =>
                val jAssignStmt = funcUnit.asInstanceOf[JAssignStmt]
                val leftOp: Value = jAssignStmt.getRightOp
                val rightOp: Value = jAssignStmt.getLeftOp
                modifyUnit(resultClass, fusionClass, leftOp, thisLocal)
                modifyUnit(resultClass, fusionClass, rightOp, thisLocal)
                funcUnit2 = jAssignStmt.clone().asInstanceOf[JAssignStmt]

              case _: JInvokeStmt =>
                val jInvokeStmt = funcUnit.asInstanceOf[JInvokeStmt]
                val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
                if (invokeMethodRef.declaringClass().getName.equals(fusionClass.getName)) {
                  val newInvokeMethodRef = resultClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
                  jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
                }
                val methodName = jInvokeStmt.getInvokeExpr.getMethod.getName
                val args = jInvokeStmt.getInvokeExpr.getArgs
                //找到init方法 将函数对象置为空
                var argIndex = 0
                for (arg <- args) {
                  if (arg.getType == resultClass.getType && methodName.equals("<init>")) {
                    jInvokeStmt.getInvokeExpr.setArg(argIndex, NullConstant.v())
                  }
                  argIndex += 1
                }
                funcUnit2 = jInvokeStmt.clone().asInstanceOf[JInvokeStmt]

              case _: JIfStmt =>
                //TODO if语句直接忽略，不影响指针分析结果, 但影响转换
                needInsert = false

              case _: JThrowStmt =>
                needInsert = false

              case _: JGotoStmt =>
                needInsert = false

              case _: JReturnStmt =>
                val jReturnStmt = funcUnit.asInstanceOf[JReturnStmt]
                if (jReturnStmt.getOp.isInstanceOf[Constant]) {
                  //防止返回的值是常量 不能把它赋给jimpleLocal，需要设置一个临时变量

                  val tempConstantLocal1 = new JimpleLocal("tempConstant1", jReturnStmt.getOp.getType)
                  val assignReturnUnit1 = new JAssignStmt(tempConstantLocal1, jReturnStmt.getOp)
                  val tempConstantLocal2 = new JimpleLocal("tempConstant2", jReturnStmt.getOp.getType)
                  val assignReturnUnit2 = new JAssignStmt(tempConstantLocal2, jReturnStmt.getOp)
                  newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal1)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit1, currentUnit1)
                  newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal2)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit2, currentUnit2)
                  currentUnit1 = assignReturnUnit1
                  currentUnit2 = assignReturnUnit2


                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal1 = tempConstantLocal1
                    preValueLocal2 = tempConstantLocal2
                  } else {
                    filterResult1 = tempConstantLocal1
                    filterResult2 = tempConstantLocal2
                  }

                  //throw OptimizeException("上一个返回的居然是常量")
                } else {
                  val returnLocal = jReturnStmt.getOp.asInstanceOf[JimpleLocal]
                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal1 = returnLocal
                    preValueLocal2 = returnLocal
                  } else {
                    filterResult1 = returnLocal
                    filterResult2 = returnLocal
                  }
                }
                needInsert = false

              case _ =>

            }

            if (needInsert) {
              newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit, currentUnit1)
              currentUnit1 = funcUnit

              newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit2, currentUnit2)
              currentUnit2 = funcUnit2
            }
          }

          if (filterFuncs.contains(funcClass)) {
            val conditionExpr1 = new JEqExpr(filterResult1, IntConstant.v(0))
            val jGotoStmt1 = new JIfStmt(conditionExpr1, Jimple.v().newStmtBox(readCacheStartUnit1))
            newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt1, currentUnit1)
            currentUnit1 = jGotoStmt1

            val conditionExpr2 = new JEqExpr(filterResult2, IntConstant.v(0))
            val jGotoStmt2 = new JIfStmt(conditionExpr2, Jimple.v().newStmtBox(readCacheStartUnit2))
            newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt2, currentUnit2)
            currentUnit2 = jGotoStmt2
          }

          if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
            preValueLocal1 = tempPrevLocal1
            preValueLocal2 = tempPrevLocal2
          }

        }
      }
    }


    //若cache不存在，写cache label2
    val ifGotoUnit3 = loopMethodUnits.getSuccOf(writeCacheStartUnit)
    val getNextUnit3 = loopMethodUnits.getSuccOf(ifGotoUnit3)
    val valueCastUnit3 = loopMethodUnits.getSuccOf(getNextUnit3)
    val mergeValueUnit3 = loopMethodUnits.getSuccOf(valueCastUnit3)
    val writeBlockUnit = loopMethodUnits.getSuccOf(mergeValueUnit3)
    var preValueLocal3 = getNextUnit3.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
    var currentUnit3: SootUnit = getNextUnit3
    //融合写cache的unit
    for (funcClass <- writeCacheFuncs) {
      if (funcClass != null) {
        //调用了treeAggregate的地方
        if (IteratorFusion.treeAggregateMap.contains(funcClass)) {
          val treeAggregateInfo = treeAggregateMap(funcClass)
          val zeroValueClass = context.sootClass(treeAggregateInfo.zeroValueName)
          context.loadClass("cn.edu.hust.grid.deca.MLDataProduce")
          val mlDataProduceClass = context.sootClass("cn.edu.hust.grid.deca.MLDataProduce")
          val getDataMethod = mlDataProduceClass.getMethodByNameUnsafe("getZeroValue")
          val args = new util.ArrayList[Value]()
          //添加zeroValue 即初始值 在循环体外
          val zeroValueLocal = new JimpleLocal("zeroValue", zeroValueClass.getType)
          val zeroValueAssign = new JAssignStmt(zeroValueLocal, new JStaticInvokeExpr(getDataMethod.makeRef(), args))
          newLoopMethod.getActiveBody.getLocals.add(zeroValueLocal)
          newLoopMethod.getActiveBody.getUnits.insertAfter(zeroValueAssign, commonStartUnit)

          val seqClass = context.sootClass(treeAggregateInfo.seqName)
          val treeFunc = genTreeAggregateFunc(seqClass, resultClass, context)
          val seqParamType = treeFunc.getParameterType(1)

          val treeAggregateLocal3 = new JimpleLocal("treeAggregateLocal3", seqParamType)
          val treeParams3 = new util.ArrayList[Value]()
          treeParams3.add(zeroValueLocal)
          treeParams3.add(preValueLocal3)
          val treeAssignment3 = new JAssignStmt(treeAggregateLocal3, new JVirtualInvokeExpr(thisLocal, treeFunc.makeRef(), treeParams3))
          newLoopMethod.getActiveBody.getLocals.add(treeAggregateLocal3)
          newLoopMethod.getActiveBody.getUnits.insertAfter(treeAssignment3, currentUnit3)
          currentUnit3 = treeAssignment3
          preValueLocal3 = treeAggregateLocal3
        } else {
          val fusionClass = context.sootClass(funcClass)

          for (field <- fusionClass.getFields) {
            if (!field.getName.equals("serialVersionUID")) {
              resultClass.addField(Utils.cloneSootField(field))
            }
          }

          //TODO 融合构造器
          //TODO 添加apply中引用的方法
          val applyMethod = getApplyMethod(fusionClass, context)
          val methodBody = Utils.cloneSootBody(applyMethod.getActiveBody)
          //添加locals
          for (local <- methodBody.getLocals) {
            // 不添加thisLocal
            if (local.getType.toString.equals(fusionClass.getName)) {
              local.setType(resultClass.getType)
            }
            newLoopMethod.getActiveBody.getLocals.addLast(local)
          }
          //添加units
          val funcUnits = methodBody.getUnits
          //假设只有一个参数
          val methodParam = applyMethod.getParameterTypes.get(0)
          var filterResult3: JimpleLocal = null

          // 如果是mapValues算子
          var tempPrevLocal3 = preValueLocal3
          if (IteratorFusion.mapValuesFuncs.contains(funcClass)) {
            val tuple2Class = context.sootClass("scala.Tuple2")
            val tupleValue3 = new JimpleLocal("tupleValue", context.sootClass("java.lang.Object").getType)
            val tupleValueAssign3 = new JAssignStmt(tupleValue3, new JVirtualInvokeExpr(preValueLocal3, tuple2Class.getMethodByNameUnsafe("_2").makeRef(), new util.ArrayList[Value]()))
            newLoopMethod.getActiveBody.getLocals.add(tupleValue3)
            newLoopMethod.getActiveBody.getUnits.insertAfter(tupleValueAssign3, currentUnit3)
            preValueLocal3 = tupleValue3
            currentUnit3 = tupleValueAssign3
          }

          for (funcUnit <- funcUnits) {
            var needInsert = true
            funcUnit match {
              case _: JIdentityStmt =>

                val jIdentityStmt = funcUnit.asInstanceOf[JIdentityStmt]
                if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
                  val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                  val assignStmt = new JAssignStmt(toLocal, thisLocal)

                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, commonStartUnit)
                  needInsert = false
                }
                if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
                  val paramRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
                  if (paramRef.getType == methodParam) {
                    val toLocal = jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal]
                    var assignStmt: SootUnit = null
                    if (paramRef.getType.isInstanceOf[PrimType]) {
                      assignStmt = new JAssignStmt(toLocal, DoubleConstant.v(1))
                    } else {
                      assignStmt = new JAssignStmt(toLocal, new JCastExpr(preValueLocal3, methodParam))
                    }
                    preValueLocal3 = toLocal
                    newLoopMethod.getActiveBody.getUnits.insertAfter(assignStmt, currentUnit3)
                    currentUnit3 = assignStmt
                    needInsert = false
                  }
                }

              case _: JAssignStmt =>
                val jAssignStmt = funcUnit.asInstanceOf[JAssignStmt]
                val leftOp: Value = jAssignStmt.getRightOp
                val rightOp: Value = jAssignStmt.getLeftOp
                modifyUnit(resultClass, fusionClass, leftOp, thisLocal)
                modifyUnit(resultClass, fusionClass, rightOp, thisLocal)

              case _: JInvokeStmt =>
                val jInvokeStmt = funcUnit.asInstanceOf[JInvokeStmt]
                val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
                if (invokeMethodRef.declaringClass().getName.equals(fusionClass.getName)) {
                  val newInvokeMethodRef = resultClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
                  jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
                }
                val methodName = jInvokeStmt.getInvokeExpr.getMethod.getName
                val args = jInvokeStmt.getInvokeExpr.getArgs
                //找到init方法 将函数对象置为空
                var argIndex = 0
                for (arg <- args) {
                  if (arg.getType == resultClass.getType && methodName.equals("<init>")) {
                    jInvokeStmt.getInvokeExpr.setArg(argIndex, NullConstant.v())
                  }
                  argIndex += 1
                }

              case _: JIfStmt =>
                //TODO if语句直接忽略，不影响指针分析结果, 但影响转换
                needInsert = false

              case _: JThrowStmt =>
                needInsert = false

              case _: JGotoStmt =>
                needInsert = false

              case _: JReturnStmt =>
                val jReturnStmt = funcUnit.asInstanceOf[JReturnStmt]
                if (jReturnStmt.getOp.isInstanceOf[Constant]) {
                  //防止返回的值是常量 不能把它赋给jimpleLocal，需要设置一个临时变量
                  val tempConstantLocal3 = new JimpleLocal("tempConstant3", jReturnStmt.getOp.getType)
                  val assignReturnUnit3 = new JAssignStmt(tempConstantLocal3, jReturnStmt.getOp)
                  newLoopMethod.getActiveBody.getLocals.add(tempConstantLocal3)
                  newLoopMethod.getActiveBody.getUnits.insertAfter(assignReturnUnit3, currentUnit3)
                  currentUnit3 = assignReturnUnit3

                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal3 = tempConstantLocal3
                  } else {
                    filterResult3 = tempConstantLocal3
                  }
                  //throw OptimizeException("上一个返回的居然是常量")
                } else {
                  val returnLocal = jReturnStmt.getOp.asInstanceOf[JimpleLocal]
                  if (!filterFuncs.contains(funcClass)) {
                    preValueLocal3 = returnLocal
                  } else {
                    filterResult3 = returnLocal
                  }
                }
                needInsert = false

              case _ =>

            }

            if (needInsert) {
              newLoopMethod.getActiveBody.getUnits.insertAfter(funcUnit, currentUnit3)
              currentUnit3 = funcUnit
            }
          }

          if (filterFuncs.contains(funcClass)) {
            val conditionExpr3 = new JEqExpr(filterResult3, IntConstant.v(0))
            val jGotoStmt3 = new JIfStmt(conditionExpr3, Jimple.v().newStmtBox(writeCacheStartUnit))
            newLoopMethod.getActiveBody.getUnits.insertAfter(jGotoStmt3, currentUnit3)
            currentUnit3 = jGotoStmt3
          }

          if (mapValuesFuncs.contains(funcClass)) {
            preValueLocal3 = tempPrevLocal3
          }

        }
      }
    }
    val reduceFunc = genReduceFunc(resultFuncClass, resultClass, context)
    resultFuncType match {
      case _: IsReduce =>
        //融合result方法(reduce的func)
        if (reduceFunc != null) {
          val returnType = reduceFunc.getReturnType
          newLoopMethod.setReturnType(returnType)
          val returnLocal = new JimpleLocal("finalResult", returnType)
          newLoopMethod.getActiveBody.getLocals.add(returnLocal)
          val reduceFuncArgs1 = new util.ArrayList[Value]()
          reduceFuncArgs1.add(returnLocal)
          reduceFuncArgs1.add(preValueLocal1)
          mergeValueUnit1.asInstanceOf[JAssignStmt].setLeftOp(returnLocal)
          mergeValueUnit1.asInstanceOf[JAssignStmt].setRightOp(new JVirtualInvokeExpr(thisLocal, reduceFunc.makeRef(), reduceFuncArgs1))

          val reduceFuncArgs2 = new util.ArrayList[Value]()
          reduceFuncArgs2.add(returnLocal)
          reduceFuncArgs2.add(preValueLocal2)
          mergeValueUnit2.asInstanceOf[JAssignStmt].setLeftOp(returnLocal)
          mergeValueUnit2.asInstanceOf[JAssignStmt].setRightOp(new JVirtualInvokeExpr(thisLocal, reduceFunc.makeRef(), reduceFuncArgs2))
          returnResultUnit.asInstanceOf[JReturnStmt].setOp(returnLocal)
        }
        else {
          newLoopMethod.getActiveBody.getUnits.remove(mergeValueUnit1)
          newLoopMethod.getActiveBody.getUnits.remove(mergeValueUnit2)
        }
      case _: IsForEach =>
        if (reduceFunc != null) {
          //TODO
        } else {
          newLoopMethod.getActiveBody.getUnits.remove(mergeValueUnit1)
          newLoopMethod.getActiveBody.getUnits.remove(mergeValueUnit2)
        }
      case _ =>
        newLoopMethod.getActiveBody.getUnits.remove(mergeValueUnit1)
        newLoopMethod.getActiveBody.getUnits.remove(mergeValueUnit2)

    }

    newLoopMethod.getActiveBody.getUnits.remove(valueCastUnit1)
    newLoopMethod.getActiveBody.getUnits.remove(valueCastUnit2)
    newLoopMethod.getActiveBody.getUnits.remove(valueCastUnit3)

    //把写入cacheBlock的变量替换掉
    if (preValueLocal3.getType.isInstanceOf[PrimType]) {
      writeBlockUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.setArg(0, NullConstant.v())
    } else {
      writeBlockUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.setArg(0, preValueLocal3)
    }

    finishResultClass(resultClass, context)

    LocalNameStandardizer.v().transform(newLoopMethod.getActiveBody, "ji.lns")
    resultClass.setApplicationClass()

    resultClass
  }


  override def transform(context: Context): Unit = {
    println("lalala")
  }
}


