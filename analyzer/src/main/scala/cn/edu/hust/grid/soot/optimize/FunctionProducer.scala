package cn.edu.hust.grid.soot.optimize

import java.util

import soot.dava.internal.javaRep.DStaticFieldRef
import soot.jimple._
import soot.jimple.internal._
import soot.{Body, Local, SootClass, SootMethod, Type, Value, VoidType}
import soot.{Unit => SootUnit, _}
import scala.collection.JavaConversions._

/**
  *  Created by iceke on 17/11/01.
  *  生成相应的method；方法类
  */
object FunctionProducer {
  /**
    * 这个apply方法可能最后不返回具体的值，所以要做具体的判断
    *
    * @param context
    * @param declareClass
    * @param realParams
    * @param realReturnType
    * @return
    */
  def getFunction3Apply(context: Context, declareClass: SootClass, realParams: util.List[Type], realReturnType: Type): SootMethod = {
    val parameterTypes = new util.ArrayList[Type]()

    //添加三个参数
    parameterTypes.add(context.sootClass("java.lang.Object").getType)
    parameterTypes.add(context.sootClass("java.lang.Object").getType)
    parameterTypes.add(context.sootClass("java.lang.Object").getType)

    val returnType: Type = context.sootClass("java.lang.Object").getType

    val method = new SootMethod("apply", parameterTypes, returnType, 4177)
    // method.setDeclaringClass(declareClass)

    val local0 = Jimple.v().newLocal("r0", declareClass.getType)
    val local1 = Jimple.v().newLocal("r1", context.sootClass("java.lang.Object").getType)
    val local2 = Jimple.v().newLocal("r2", context.sootClass("java.lang.Object").getType)
    val local3 = Jimple.v().newLocal("r3", context.sootClass("java.lang.Object").getType)
    val local4 = Jimple.v().newLocal("$r4", realParams.get(0))
    val local5 = Jimple.v().newLocal("$r5", realParams.get(1))
    val local6 = Jimple.v().newLocal("$r6", realParams.get(2))
    var local7: Local = null
    if (!realReturnType.isInstanceOf[VoidType]) {
      local7 = Jimple.v().newLocal("$r7", realReturnType)
    }

    val unit0 = new JIdentityStmt(local0, new ThisRef(declareClass.getType))
    val unit1 = new JIdentityStmt(local1, new ParameterRef(context.sootClass("java.lang.Object").getType, 0))
    val unit2 = new JIdentityStmt(local2, new ParameterRef(context.sootClass("java.lang.Object").getType, 1))
    val unit3 = new JIdentityStmt(local3, new ParameterRef(context.sootClass("java.lang.Object").getType, 2))
    val unit4 = new JAssignStmt(local4, new JCastExpr(local1, realParams.get(0)))
    val unBoxMethod = context.sootClass("scala.runtime.BoxesRunTime").getMethodByName("unboxToInt")
    val unBoxArgs = new util.ArrayList[Value]()
    unBoxArgs.add(local2)
    val unit5 = new JAssignStmt(local5, new JStaticInvokeExpr(unBoxMethod.makeRef(), unBoxArgs))
    val unit6 = new JAssignStmt(local6, new JCastExpr(local3, realParams.get(2)))
    //base methodRef
    val argsList = new util.ArrayList[Value]()
    argsList.add(local4)
    argsList.add(local5)
    argsList.add(local6)
    var unit7: SootUnit = null
    var unit8: SootUnit = null
    if (realReturnType.isInstanceOf[VoidType]) {
      unit7 = new JInvokeStmt(new JVirtualInvokeExpr(local0,
        declareClass.getMethod("apply", realParams, realReturnType).makeRef(), argsList))
      unit8 = new JReturnVoidStmt()
    } else {
      unit7 = new JAssignStmt(local7,
        new JVirtualInvokeExpr(local0, declareClass.getMethod("apply", realParams, realReturnType).makeRef(), argsList))
      unit8 = new JReturnStmt(local7)
    }

    //开始添加locals和units
    val methodBody = new JimpleBody()
    methodBody.getLocals.addLast(local0)
    methodBody.getLocals.addLast(local1)
    methodBody.getLocals.addLast(local2)
    methodBody.getLocals.addLast(local3)
    methodBody.getLocals.addLast(local4)
    methodBody.getLocals.addLast(local5)
    methodBody.getLocals.addLast(local6)
    if (!realReturnType.isInstanceOf[VoidType]) {
      methodBody.getLocals.addLast(local7)
    }
    methodBody.getUnits.addLast(unit0)
    methodBody.getUnits.addLast(unit1)
    methodBody.getUnits.addLast(unit2)
    methodBody.getUnits.addLast(unit3)
    methodBody.getUnits.addLast(unit4)
    methodBody.getUnits.addLast(unit5)
    methodBody.getUnits.addLast(unit6)
    methodBody.getUnits.addLast(unit7)
    methodBody.getUnits.addLast(unit8)

    methodBody.setMethod(method)

    method.setActiveBody(methodBody)


    method

  }

  def getClInitMethod(context: Context, sootClass: SootClass): SootMethod = {
    val serField = sootClass.getFieldByName("serialVersionUID")
    println(serField.isStatic)
    val method = new SootMethod("<clinit>", null, VoidType.v(), 9)
    val serRef = new DStaticFieldRef(serField.makeRef(), sootClass.getName)
    val unit1 = new JAssignStmt(serRef, LongConstant.v(0L))
    val unit2 = new JReturnVoidStmt()
    val methodBody = new JimpleBody()
    methodBody.getUnits.addLast(unit1)
    methodBody.getUnits.addLast(unit2)
    methodBody.setMethod(method)
    method.setActiveBody(methodBody)

    method

  }

  def getInitMethod(fusionClass: SootClass): SootMethod = {
    val needInitFields = new util.ArrayList[SootField]()
    for(field <- fusionClass.getFields){
      if(!field.getName.equals("serialVersionUID")){
        needInitFields.add(field)
      }
    }

    val parameterTypes = new util.ArrayList[Type]()
    val locals = new util.ArrayList[JimpleLocal]()
    val identityUnits = new util.ArrayList[SootUnit]()
    val assignUnits = new util.ArrayList[SootUnit]()
    val thisLocal = Jimple.v().newLocal("r0", fusionClass.getType)
    val thisUnit = new JIdentityStmt(thisLocal, new ThisRef(fusionClass.getType))
    var index: Int = 0
    for(field <- needInitFields){
      parameterTypes.add(field.getType)
      val local = new JimpleLocal("r" + (index+1), field.getType)
      locals.add(local)
      val setParamUnit = new JIdentityStmt(local, new ParameterRef(field.getType, index))
      val setFieldUnit = new JAssignStmt(new JInstanceFieldRef(thisLocal, field.makeRef()), local)
      identityUnits.add(setParamUnit)
      assignUnits.add(setFieldUnit)
      index += 1
    }

    val initMethod = new SootMethod("<init>", parameterTypes,VoidType.v(), 1)
    val methodBody = new JimpleBody()

    methodBody.getLocals.add(thisLocal)
    methodBody.getUnits.add(thisUnit)

    for(local <- locals){
      methodBody.getLocals.add(local)
    }

    for(unit <- identityUnits){
      methodBody.getUnits.add(unit)
    }

    for(unit <- assignUnits){
      methodBody.getUnits.add(unit)
    }

    val returnUnit = new JReturnVoidStmt()
    methodBody.getUnits.add(returnUnit)

    methodBody.setMethod(initMethod)
    initMethod.setActiveBody(methodBody)

    initMethod
  }

}
