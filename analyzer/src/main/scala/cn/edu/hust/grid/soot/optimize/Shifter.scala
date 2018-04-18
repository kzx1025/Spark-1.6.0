package cn.edu.hust.grid.soot.optimize

import java.util
import java.util.{ArrayList, Arrays}

import cn.edu.hust.grid.deca.TimeRecorder
import cn.edu.hust.grid.soot.Utils
import cn.edu.hust.grid.soot.optimize.Shifter.{covertNameString, covertTypeString}
import cn.edu.hust.grid.soot.optimize.SplitClass.dynamicLoad

import scala.collection.JavaConversions._
import soot.jimple._
import soot._
import soot.jimple.internal._
import soot.jimple.spark.sets.PointsToSetInternal
import soot.SootMethodRefImpl._

import scala.collection.mutable
import scala.Unit

/** 转换成deca的类*/
object Shifter extends Transformer {


  def getRelationType(classType: Type,originDecaMap:util.HashMap[SootClass,SootClass],context: Context):Type={
    if(classType.isInstanceOf[RefType]){
      val sc=classType.asInstanceOf[RefType].getSootClass
      if(originDecaMap.containsKey(sc)){
        originDecaMap.get(sc).getType
      }else{
        sc.getType
      }
    }else if(classType.isInstanceOf[ArrayType]){
      val ca= createArrayDeca(classType,context)
      if(ca==null){
        classType
      }else{
        ca.getType
      }
    }else{
      classType
    }
  }
  def getRelationTypeString(classType: Type,context: Context):Type={
    if(classType.isInstanceOf[RefType]){
      val sc=classType.asInstanceOf[RefType].getSootClass
      if(TransformCollection.originDecaMapStrng.containsKey(sc.toString)){
        TransformCollection.originDecaMapStrng.get(sc.toString).getType
      }else{
        sc.getType
      }
    }else if(classType.isInstanceOf[ArrayType]){
      val ca= createArrayDeca(classType,context)
      if(ca==null){
        classType
      }else{
        ca.getType
      }
    }else{
      classType
    }
  }
  /**
    * 这个是那个先生成临时类再转换的
    * @param localNewSiteInfoList
    * @param context
    */

  def transform(localNewSiteInfoList:util.List[LocalNewSiteInfo],fusionClass:SootClass,context: Context): Unit ={
    context.options.set_allow_phantom_refs(false)
    println("start tranform the method and class")
    //用于存储这个phase用的deca类，之前phase已经有的就不重复写了
    val decaClasses=new util.HashSet[SootClass]()
    val  decomposeStart=System.currentTimeMillis()
    for(localInfo<-localNewSiteInfoList) {
      val topClass = localInfo.topClass
      val topSite = localInfo.localNewSite
      val fieldInfoMap = localInfo.fieldInfoMap
      val fieldNewSiteMap = localInfo.fieldsNewSiteMap
      //第一步吧

      //首先创建一个Map,存储老方法和temp类里面的方法，然后再建一个从temp里面方法到deca类方法的map
      val originTempMethodMap = new util.HashMap[SootMethod, SootMethod]()
      val tempDecaMethodMap = new util.HashMap[SootMethod, SootMethod]()
      val originDecaMethodMap = new util.HashMap[SootMethod, SootMethod]()
      //此处加方法转换集合，如果转换过，就不用转了，怎么说呢，就是把新方法加进去吧
      val transformedMethods = new util.HashSet[SootMethod]()
      val originTempMap = new util.HashMap[SootClass, SootClass]()
      val result = modifyFieldTypeOfSootClass(topClass, fieldInfoMap, originTempMap, originTempMethodMap, context)

      //创建一个map，key为类，然后value为对应的deca类，比如spTemp对应spTempDeca，而且denseVector也对应spTempDeca
      val originDecaMap = new util.HashMap[SootClass, SootClass]()


      val decaOriginMap = new util.HashMap[SootClass, SootClass]()

      val r = createDecaClass(result, originDecaMap, originTempMap, decaOriginMap, tempDecaMethodMap, context)
      originDecaMap.values().map(s=>decaClasses.add(s))

      //这个map直接用来做映射
      for (kv <- originTempMethodMap) {
        val originMethod = kv._1
        val tempMethod = kv._2
        if (tempDecaMethodMap.containsKey(kv._2)) {
          originDecaMethodMap.put(originMethod, tempDecaMethodMap.get(tempMethod))
        }
      }
      for (kv <- tempDecaMethodMap) {
        originDecaMethodMap.put(kv._1, kv._2)
      }


      for (kv <- originTempMap) {
        originDecaMap.put(kv._1, originDecaMap.get(kv._2))
      }
      /**
        * 就在此处更改newSite,那首先就是更改topClass的newSIte，之后就是每个field的newSite
        */
      val decaSet = new util.HashSet[String]()
      originDecaMap.keySet().map(k => decaSet.add(k.toString))
      originDecaMap.values().map(k => if (k != null) {
        decaSet.add(k.toString)
      })
      if (originDecaMap.values().size() == 1 && originDecaMap.values().contains(null)) {
        return
      }


      originTempMap.keySet().map(k => decaSet.add(k.toString))
      originTempMap.values().map(v => decaSet.add(v.toString))


      {
        //        topSite.method.setReturnType(getRelationType(topSite.method.getReturnType,originDecaMap,context))

        val body = topSite.method.getActiveBody
        val newUnit = topSite.newUnit.asInstanceOf[JAssignStmt]
        val initUnit = topSite.initUnit.asInstanceOf[JInvokeStmt]
        //这里 dataPoint和dataPointTemp 怎么对应呢，可以再加一个对应temp的。。。只能这么做了
        newUnit.setRightOp(Jimple.v().newNewExpr(getRelationType(topClass.getType, originDecaMap, context).asInstanceOf[RefType]))
        newUnit.getLeftOp.asInstanceOf[JimpleLocal].setType(getRelationType(topClass.getType, originDecaMap, context))
        if (initUnit != null) {
          val specialInvoke = initUnit.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr]
          val baseLocal = specialInvoke.getBase.asInstanceOf[JimpleLocal]
          val argsType = specialInvoke.getArgs.map(arg => getRelationType(arg.getType, originDecaMap, context))
          val funCl = getRelationType(result.getType, originDecaMap, context).asInstanceOf[RefType].getSootClass
          val methodName = covertName(specialInvoke.getMethod, originTempMap, funCl, context)
          val oldMethod = specialInvoke.getMethod
          val oldTypes = oldMethod.getParameterTypes
          val oldReturn = oldMethod.getReturnType
          val meRef = createMethodForFuncClass(oldMethod, funCl, argsType, originDecaMap, originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef()
          if (body.getUnits.contains(initUnit)) {
            body.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(baseLocal, meRef, specialInvoke.getArgs)), initUnit)
            body.getUnits.remove(initUnit)
          }
        }
      }
      {
        /**
          * 接下来给fieldNewSiteInfo
          */
        //TODO 这个newSite替换有点问题，因为次序好像反了
        for (fielNewSiteInfo <- fieldNewSiteMap) {
          val fieldInfo = fielNewSiteInfo._1
          val newSiteInfo = fielNewSiteInfo._2
          //          newSiteInfo.method.setReturnType(getRelationType(newSiteInfo.method.getReturnType,originDecaMap,context))
          val body = newSiteInfo.method.getActiveBody
          val units = body.getUnits
          val newUnit = newSiteInfo.newUnit.asInstanceOf[JAssignStmt]

          val leftLocal = newUnit.getLeftOp.asInstanceOf[JimpleLocal]
          val isArr = leftLocal.getType match {
            case a: ArrayType => true
            case _ => false
          }


          //这个是字段所在的类，不是实例类型
          val relateDeca = originDecaMap.get(fieldInfo.getDeclaringClass)
          val fieldName = fieldInfo.getName
          if (relateDeca != null && relateDeca.getFieldByNameUnsafe(fieldName) != null) {
            val relateField = relateDeca.getFieldByName(fieldName)
            val fieldClass = relateField.getType.asInstanceOf[RefType].getSootClass
            val relateGetFieldMethod = relateDeca.getMethodByName("get" + fieldName)
            val relateInitFieldMethod = relateDeca.getMethodByName("set" + fieldName)

            //寻找用到这个字段的
            var curUnit = newSiteInfo.newUnit
            val lastUnit = units.getLast
            var hasUnit = true
            while (units.contains(curUnit) && hasUnit && (!(curUnit.isInstanceOf[JInvokeStmt] && curUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JSpecialInvokeExpr]
              && curUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.asInstanceOf[JSpecialInvokeExpr].getArgs.contains(leftLocal)))) {
              if (curUnit.equals(lastUnit)) {
                hasUnit = false
              } else {
                curUnit = units.getSuccOf(curUnit)
              }

            }
            val find = if (curUnit.isInstanceOf[JInvokeStmt] && curUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JSpecialInvokeExpr]
              && curUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.asInstanceOf[JSpecialInvokeExpr].getArgs.contains(leftLocal)) {
              true
            } else {
              false
            }
            //这里的local就是他的爹
            if (find) {
              val parentInstance = curUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.asInstanceOf[JSpecialInvokeExpr].getBase.asInstanceOf[JimpleLocal]
              //左local赋值
              leftLocal.setType(fieldClass.getType)
              //pareInstance.initFieldAddress
              units.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(parentInstance, relateInitFieldMethod.makeRef())), newUnit)
              // leftLocal=pareInstace.getField
              units.insertBefore(Jimple.v().newAssignStmt(leftLocal, Jimple.v().newVirtualInvokeExpr(parentInstance, relateGetFieldMethod.makeRef())), newUnit)


              units.remove(newUnit)

              if (!isArr) {
                val initUnit = newSiteInfo.initUnit.asInstanceOf[JInvokeStmt]

                val specialInvoke = initUnit.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr]
                val baseLocal = specialInvoke.getBase.asInstanceOf[JimpleLocal]
                val argsType = specialInvoke.getArgs.map(arg => getRelationType(arg.getType, originDecaMap, context))
                val relateDeca = getRelationType(specialInvoke.getMethod.getDeclaringClass.getType, originDecaMap, context).asInstanceOf[RefType].getSootClass

                val methodName = covertName(specialInvoke.getMethod, originTempMap, relateDeca, context)
                val oldMethod = specialInvoke.getMethod
                val methodRef = createMethodForFuncClass(oldMethod, relateDeca, argsType, originDecaMap, originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef()
                //            val methodRef = getRelationType(specialInvoke.getMethod.getDeclaringClass.getType, originDecaMap, context).asInstanceOf[RefType].getSootClass.getMethod(methodName, argsType).makeRef()

                body.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(baseLocal, methodRef, specialInvoke.getArgs)), initUnit)

              }
            } else {
              //这说明，可能不在这个类里面，那就直接开始new，然后init
              if (units.contains(newUnit)) {
                units.insertBefore(Jimple.v().newAssignStmt(leftLocal, Jimple.v().newNewExpr(fieldClass.getType)), newUnit)

                /**
                  * 初始化
                  */
                if (newSiteInfo.initUnit != null) {

                  val initUnit = newSiteInfo.initUnit.asInstanceOf[JInvokeStmt]
                  val initExpr = initUnit.getInvokeExpr.asInstanceOf[JSpecialInvokeExpr]
                  val initArgs = initExpr.getArgs
                  val baseLocal = initExpr.getBase.asInstanceOf[JimpleLocal]
                  val decaCl = getRelationType(baseLocal.getType, originDecaMap, context).asInstanceOf[RefType].getSootClass
                  val methodRef = createMethodForFuncClass(initExpr.getMethod, decaCl, initArgs.map(arg => getRelationType(arg.getType, originDecaMap, context)), originDecaMap,
                    originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef()
                  units.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(baseLocal, methodRef, initArgs)), initUnit)
                  units.remove(newUnit)
                  units.remove(initUnit)


                }
                //TODO 基于decaArray的初始化
                else {
                  //decaArray的初始化


                }
              }


            }

            //此处加一些？
            val fieldOriginType = fieldInfo.getType
            if (fieldOriginType.isInstanceOf[RefType]) {
              val fieldRelateSc = fieldOriginType.asInstanceOf[RefType].getSootClass
              if (!fieldRelateSc.getName.equals("java.lang.Object")) {
                val relateSc = newSiteInfo.newUnit.asInstanceOf[AssignStmt].getRightOp.asInstanceOf[JNewExpr].getType.asInstanceOf[RefType].getSootClass
                originDecaMap.put(fieldRelateSc, originDecaMap.get(relateSc))
              }
            }
          }
        }

      }
      // context.writeJimple(context.sootClass("breeze.linalg.DenseVector$"))

      //把集合加到全局
      originDecaMap.map(kv => TransformCollection.originDecaMapStrng.put(kv._1.toString, kv._2))
      originTempMap.map(kv => TransformCollection.originTempMapStrng.put(kv._1.toString, kv._2))
      originDecaMap.map(kv=>TransformCollection.tempOriginMapString.put(kv._2,kv._1.toString))
      decaOriginMap.map(kv => TransformCollection.decaOriginMapStrng.put(kv._1, kv._2))
      decaSet.map(dc => TransformCollection.decaSetStrng.add(dc))
      originDecaMethodMap.map(kv => TransformCollection.originDecaMethodMapStrng.put(kv._1.getSubSignature, kv._2))
      transformedMethods.map(kv => TransformCollection.transformedMethodsStrng.add(kv.getSubSignature))
      tempDecaMethodMap.map(kv => TransformCollection.tempDecaMethodMapStrng.put(kv._1.getSubSignature, kv._2))

    }
    val decomposeEnd=System.currentTimeMillis()
    TimeRecorder.decomposeTime=decomposeEnd-decomposeStart

      /**
        * 转换funcClass
        */


      val transformStart=System.currentTimeMillis()
      val funcClass=fusionClass
      funcClass.getFields.map(field=>field.setType(getRelationTypeString(field.getType,context)))

      val methods=new util.ArrayList[SootMethod]()
      funcClass.getMethods.map(m=>methods.add(m))
      val toRemoveMethods=new util.HashSet[SootMethod]()
      for(method<-methods){
        val cm=createMethodForFuncClassString(method,funcClass,method.getParameterTypes.map(t=>getRelationTypeString(t,context)),context)
        if(!cm.getSubSignature.equals(method.getSubSignature)){
          toRemoveMethods.add(method)
        }
      }
      for(method<-toRemoveMethods){
        funcClass.removeMethod(method)
      }

    val transformEnd=System.currentTimeMillis()
    TimeRecorder.transformTime=transformEnd-transformStart
    TimeRecorder.localNewSiteInfoSize=localNewSiteInfoList.size()

    //下面是写jimple
    val writeStart=System.currentTimeMillis()
    context.writeJimple(funcClass)

    var writeFailedNum=0
    for(dc<-decaClasses){
      if(dc!=null){
        try {
          context.writeJimple(dc)
        }catch {
          case e:Exception=>{
            println("****writeJimpleWrong:"+dc.toString)
            writeFailedNum+=1
          }
        }
      }
    }
    val primTypes=new util.HashSet[String]()
    primTypes.add("double")
    primTypes.add("int")
    primTypes.add("long")
    primTypes.add("float")
    primTypes.add("byte")
    primTypes.add("char")
    primTypes.add("boolean")
    primTypes.add("short")
    var allWriteNum=decaClasses.size()+1
    for(t<-primTypes){
      if(context.scene.getSootClassUnsafe(t+"ArrayDeca")!=null){
        if(!TransformCollection.usedArrayDecaStrng.contains(t+"ArrayDeca")) {
          context.writeJimple(context.sootClass(t + "ArrayDeca"))
          allWriteNum+=1
          TransformCollection.usedArrayDecaStrng.add(t+"ArrayDeca")
        }
      }
    }
    val writeEnd=System.currentTimeMillis()

    if(allWriteNum==writeFailedNum){
      TimeRecorder.writeJimpleTime=(writeEnd-writeStart)*2
    }else{
      TimeRecorder.writeJimpleTime=(writeEnd-writeStart)*(allWriteNum/(allWriteNum-writeFailedNum))

    }
    TimeRecorder.writeJimpleNum=allWriteNum
    context.options.set_allow_phantom_refs(true)
    println("tranform completed!!!")


  }


  def containsBySet(decaSet:util.HashSet[String],types:util.List[Type]):Boolean={

    for(ty<-types) {
      if (ty.isInstanceOf[RefType]) {
        val tyClass=ty.asInstanceOf[RefType].getSootClass.toString
        if (decaSet.contains(tyClass))
          return true
      }
    }
    false
  }

  def getNewSootClass(oldMethod:SootMethod,funcClass:SootClass,originDecaMap:util.HashMap[SootClass,SootClass]):SootClass={
    val oldSootClass=oldMethod.getDeclaringClass
    //首先判断是哪的方法吧
    if(originDecaMap.containsKey(oldSootClass)){
      originDecaMap.get(oldSootClass)
    }else if(originDecaMap.values().contains(oldSootClass)){
      oldSootClass
    }
    else{
      funcClass
    }
  }
  def getNewSootClassString(oldMethod:SootMethod,funcClass:SootClass):SootClass={
    val oldSootClass=oldMethod.getDeclaringClass

    //首先判断是哪的方法吧
    if(TransformCollection.originDecaMapStrng.containsKey(oldSootClass.toString)){
      TransformCollection.originDecaMapStrng.get(oldSootClass.toString)
    }else if(TransformCollection.originDecaMapStrng.values().contains(oldSootClass)){
      oldSootClass
    }
    else{
      funcClass
    }
  }

  def  getActualInvoke(baseClass:SootClass,oldMthod:SootMethod,decaOriginMap:util.HashMap[SootClass,SootClass]):SootMethod={

    val methodName=oldMthod.getName
    val methodParameterType=oldMthod.getParameterTypes
    val methodReturnType=oldMthod.getReturnType
    var parentClass=baseClass
    //如果是deca，就转为普通类来找
    if(decaOriginMap.containsKey(baseClass)){
      if(oldMthod.getDeclaringClass.toString.equals(baseClass.toString)){
        return oldMthod
      }
      parentClass=decaOriginMap.get(baseClass)
    }
    while (parentClass!=null){
      if(parentClass.getMethodUnsafe(methodName,methodParameterType,methodReturnType)!=null){
        return parentClass.getMethodUnsafe(methodName,methodParameterType,methodReturnType)
      }
      if(parentClass.toString.equals("java.lang.Object")){
        return null
      }
      parentClass=parentClass.getSuperclass
    }
    null
  }
  def  getActualInvokeString(baseClass:SootClass,oldMthod:SootMethod,context: Context):SootMethod={

    val methodName=oldMthod.getName
    val methodParameterType=oldMthod.getParameterTypes
    val methodReturnType=oldMthod.getReturnType
    var parentClass=baseClass
    //如果是deca，就转为普通类来找
    if(TransformCollection.decaOriginMapStrng.containsKey(baseClass)){
      if(oldMthod.getDeclaringClass.toString.equals(baseClass.toString)){
        return oldMthod
      }
      parentClass=TransformCollection.decaOriginMapStrng.get(baseClass)
    }
    while (parentClass!=null){
      if(parentClass.getMethodUnsafe(methodName,methodParameterType,methodReturnType)!=null){
        return parentClass.getMethodUnsafe(methodName,methodParameterType,methodReturnType)
      }
      if(parentClass.toString.equals("java.lang.Object")){
        return null
      }
      if(TransformCollection.tempOriginMapString.containsKey(parentClass)){
        parentClass=context.sootClass(TransformCollection.tempOriginMapString.get(parentClass))
      }else{
        parentClass=parentClass.getSuperclass
      }
    }
    null
  }
  def  getInterfaceInvoke(baseClass:SootClass,methodName:String,methodParameters:util.List[Type],returnType:Type,decaOriginMap:util.HashMap[SootClass,SootClass]):SootMethod={


    var parentClass=baseClass
    //如果是deca，就转为普通类来找
    if(decaOriginMap.containsKey(baseClass)){
      parentClass=decaOriginMap.get(baseClass)
    }
    while (parentClass!=null){
      if(parentClass.getMethodUnsafe(methodName,methodParameters,returnType)!=null){
        return parentClass.getMethodUnsafe(methodName,methodParameters,returnType)
      }
      if(parentClass.toString.equals("java.lang.Object")){
        return null
      }
      parentClass=parentClass.getSuperclass
    }
    null
  }
  def  getInterfaceInvokeString(baseClass:SootClass,methodName:String,methodParameters:util.List[Type],returnType:Type,context: Context):SootMethod={


    var parentClass=baseClass
    //如果是deca，就转为普通类来找
    if(TransformCollection.decaOriginMapStrng.containsKey(baseClass)){
      parentClass=TransformCollection.decaOriginMapStrng.get(baseClass)
    }
    while (parentClass!=null){
      if(parentClass.getMethodUnsafe(methodName,methodParameters,returnType)!=null){
        return parentClass.getMethodUnsafe(methodName,methodParameters,returnType)
      }
      if(parentClass.toString.equals("java.lang.Object")){
        return null
      }
      if(TransformCollection.tempOriginMapString.containsKey(parentClass)){
        parentClass=context.sootClass(TransformCollection.tempOriginMapString.get(parentClass))
      }else{
        parentClass=parentClass.getSuperclass
      }    }
    null
  }


  def createEmptyMethod(methodName:String,paratypes:util.List[Type],rety:Type,sootClass:SootClass):SootMethod={
    if(sootClass.getMethodUnsafe(methodName,paratypes,rety)!=null){
      return sootClass.getMethod(methodName,paratypes,rety)
    }
    val method=new  SootMethod(methodName,paratypes,rety,Modifier.PUBLIC)
    sootClass.addMethod(method)
    val body=new JimpleBody(method)
    method.setActiveBody(body)

    val locals=body.getLocals
    val units=body.getUnits
    val iden=new JimpleLocal("iden",sootClass.getType)
    locals.add(iden)
    units.add(new JIdentityStmt(iden,Jimple.v().newThisRef(sootClass.getType)))
    var index=0
    if(paratypes!=null) {
      for (t <- paratypes) {
        val l = new JimpleLocal("p" + index, t)
        locals.add(l)
        units.add(Jimple.v().newIdentityStmt(l, Jimple.v().newParameterRef(t, index)))
        index += 1
      }
    }
    method

  }
  def createEmptyBody(method:SootMethod,sootClass: SootClass):SootMethod={

    val body=new JimpleBody(method)
    method.setActiveBody(body)

    val locals=body.getLocals
    val units=body.getUnits
    val iden=new JimpleLocal("iden",sootClass.getType)
    locals.add(iden)
    units.add(new JIdentityStmt(iden,Jimple.v().newThisRef(sootClass.getType)))
    var index=0
    for(t<-method.getParameterTypes){
      val l=new JimpleLocal("p"+index,t)
      locals.add(l)
      units.add(Jimple.v().newIdentityStmt(l,Jimple.v().newParameterRef(t,index)))
      index+=1
    }
    method

  }
  def createMethodForFuncClassString(oldMethod:SootMethod,funcClass:SootClass,realParaTypes:util.List[Type],context: Context): SootMethod = {


    val originDecaMap=TransformCollection.originDecaMapStrng
    val decaSet=TransformCollection.decaSetStrng
    val originDecaMethodMap=TransformCollection.originDecaMethodMapStrng
    val transformedMethods=TransformCollection.transformedMethodsStrng

    //首先判断是哪的方法吧
    val newSootClass = getNewSootClassString(oldMethod, funcClass)
    var isExist = false
    //这里的SIGNATURES是一样的么，会因为参数传入而改变么
    if (newSootClass.getMethodUnsafe(covertNameString(oldMethod, newSootClass, context), realParaTypes
      , covertTypeString(oldMethod.getReturnType, context)) != null) {
      val nMethod = newSootClass.getMethodUnsafe(covertNameString(oldMethod, newSootClass, context), realParaTypes
        , covertTypeString(oldMethod.getReturnType, context))
      isExist = true
      if (TransformCollection.transformedMethodsStrng.size() != 0 && TransformCollection.transformedMethodsStrng.contains(nMethod.getSubSignature))
        return newSootClass.getMethodUnsafe(covertNameString(oldMethod, newSootClass, context), realParaTypes
          , covertTypeString(oldMethod.getReturnType, context))
    }


    val pa = context.scene.getPointsToAnalysis

    val newMethod = if (!isExist) {
      new SootMethod(covertNameString(oldMethod, newSootClass, context), realParaTypes
        , covertTypeString(oldMethod.getReturnType, context),
        oldMethod.getModifiers, oldMethod.getExceptions)
    } else {
      newSootClass.getMethodUnsafe(covertNameString(oldMethod, newSootClass, context), realParaTypes
        , covertTypeString(oldMethod.getReturnType, context))
    }
    newMethod.setDeclaringClass(newSootClass)
    transformedMethods.add(newMethod.getSubSignature)


    if (!oldMethod.hasActiveBody) {
      return newMethod
    }
    if (!isExist){
      val localMethodBody = oldMethod.getActiveBody
      newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
      newSootClass.addMethod(newMethod)
    }
    val newMethodBody = newMethod.retrieveActiveBody()
    val newLocals=newMethodBody.getLocals

    /**
      * 设置对应类型
      */
    var flag=true

    var lastLocal:Local=null
    var curLocal:Local=null
    for(local<-oldMethod.getActiveBody.getLocals){
      if(!flag){
        curLocal=newLocals.getSuccOf(lastLocal)
      }else{
        flag=false
        curLocal=newLocals.getFirst
      }
      val pts=pa.reachingObjects(local).possibleTypes()
      var ty=local.getType
      if(ty.isInstanceOf[RefType]) {

        if (pts.size() == 1) {
          ty = pts.toArray.apply(0).asInstanceOf[Type]
        }
      }
      curLocal.setType(getRelationTypeString(ty,context))
      lastLocal=curLocal

    }



    var randIndex=0

    for (unit <- newMethodBody.getUnits.snapshotIterator()) {
      //      if(oldMethod.getName.equals("apply")&&oldMethod.getReturnType.toString.equals("breeze.linalg.Vector")){
      //        print()
      //      }
      if (unit.isInstanceOf[JIdentityStmt]) {
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
//          jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal].setType(newSootClass.getType)
          jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
        }else if(jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]){
          val ty=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getType
          val index=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getIndex
          jIdentityStmt.setRightOp(Jimple.v().newParameterRef(realParaTypes.get(index),index))
          jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal].setType(realParaTypes.get(index))

        }
      }
      else if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]


          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          var findMethodException=false
          try {
            val method = jVirtualInvokeExpr.getMethod

            if(findMethodException==false) {
              val returnType = method.getReturnType
              val methodClass = method.getDeclaringClass
              if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
                //这里加一句吧
                val decaMethod = if (originDecaMethodMap.containsKey(method.getSubSignature)) {
                  originDecaMethodMap.get(method.getSubSignature)
                } else {
                  method
                }
                val actualMethod = getActualInvokeString(baseClass, decaMethod,context)
                if (actualMethod == null) {
                  if (baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                    jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                  }
                  else {
                    jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                  }

                } else {
                  val newMethodRef = createMethodForFuncClassString(actualMethod, funcClass,realTypes, context).makeRef()
                  jVirtualInvokeExpr.setMethodRef(newMethodRef)
                }
              }
            }

          }catch {
            case e:Exception=>{
              val base=jVirtualInvokeExpr.getBase
              println("****did not find method  "+unit.toString())
              findMethodException=true


            }
          }


        } else if (jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]


          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          val method=jVirtualInvokeExpr.getMethod
          val returnType=method.getReturnType
          val methodClass=method.getDeclaringClass
          if(decaSet.contains(methodClass.toString)||containsBySet(decaSet,realTypes)||decaSet.contains(baseClass.toString)||decaSet.contains(returnType.toString)){
            //这里加一句吧
            val decaMethod=if(originDecaMethodMap.containsKey(method.getSubSignature)){
              originDecaMethodMap.get(method.getSubSignature)
            }else{
              method
            }
            val actualMethod=getActualInvokeString(baseClass,decaMethod,context)
            if(actualMethod==null){
              if(baseClass.getMethodUnsafe(method.getName,jVirtualInvokeExpr.getArgs.map(arg=>arg.getType),returnType)==null) {
                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
              }
              else {
                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
              }
            }else {

              val newMethodRef = createMethodForFuncClassString(actualMethod, funcClass, realTypes, context).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }

          }

        }
        else  if (jAssignStmt.getRightOp.isInstanceOf[JStaticInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JStaticInvokeExpr]

          try {
            val method = jVirtualInvokeExpr.getMethod
            //附加一些东西
            val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
            val returnType=method.getReturnType
            val methodClass=method.getDeclaringClass

            /**
              *
              */
            if(decaSet.contains(methodClass.toString)||containsBySet(decaSet,realTypes)||decaSet.contains(returnType.toString)){
              //这里加一句吧
              val decaMethod=if(originDecaMethodMap.containsKey(method.getSubSignature)){
                originDecaMethodMap.get(method.getSubSignature)
              }else{
                method
              }
              val newMethodRef = createMethodForFuncClassString(decaMethod,funcClass,realTypes,context).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }
          }catch {
            case e:Exception=>{
            }
          }

        }
        else if (jAssignStmt.getLeftOp.isInstanceOf[JStaticInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JStaticInvokeExpr]
          //判断下这个方法是不是父类方法
          val method=jVirtualInvokeExpr.getMethod
          //附加一些东西
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          val returnType=method.getReturnType
          val methodClass=method.getDeclaringClass

          if(decaSet.contains(methodClass.toString)||containsBySet(decaSet,realTypes)||decaSet.contains(returnType.toString)){
            //这里加一句吧
            val decaMethod=if(originDecaMethodMap.containsKey(method.getSubSignature)){
              originDecaMethodMap.get(method.getSubSignature)
            }else{
              method
            }
            val newMethodRef = createMethodForFuncClassString(decaMethod,funcClass,realTypes,context).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        }
        //右边是接口方法
        else if(jAssignStmt.getRightOp.isInstanceOf[JInterfaceInvokeExpr]){

          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JInterfaceInvokeExpr]
          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          try {
            val methodRef=jVirtualInvokeExpr.getMethodRef


            val returnType = methodRef.returnType()
            val methodClass = methodRef.declaringClass()
            if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
              val methodName=methodRef.name()
              val methodParameters=methodRef.parameterTypes()

              val actualMethod = getInterfaceInvokeString(baseClass,methodName,methodParameters,returnType,context)
              if (actualMethod == null) {
//                println("*******************"+methodClass.getShortName+methodName)
                if (baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                  jAssignStmt.setRightOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createEmptyMethod(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                }
                else {
                  jAssignStmt.setRightOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                }
              } else {
                jAssignStmt.setRightOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createMethodForFuncClassString(actualMethod, funcClass, realTypes, context).makeRef(), jVirtualInvokeExpr.getArgs))
                //              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, context).makeRef()
                //              jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }
            }
          }catch {
            case e:Exception=> {
              println("****")
            }

          }

        }
        else if(jAssignStmt.getLeftOp.isInstanceOf[JInterfaceInvokeExpr]){
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JInterfaceInvokeExpr]
          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          try {
            val methodRef=jVirtualInvokeExpr.getMethodRef


            val returnType = methodRef.returnType()
            val methodClass = methodRef.declaringClass()
            if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
              val methodName=methodRef.name()
              val methodParameters=methodRef.parameterTypes()

              val actualMethod = getInterfaceInvokeString(baseClass,methodName,methodParameters,returnType,context)
              if (actualMethod == null) {
                println("*******************"+methodClass.getShortName+methodName)
                if (baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                  jAssignStmt.setLeftOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createEmptyMethod(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                }
                else {
                  jAssignStmt.setLeftOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                }
              } else {
                jAssignStmt.setLeftOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createMethodForFuncClassString(actualMethod, funcClass, realTypes, context).makeRef(), jVirtualInvokeExpr.getArgs))
                //              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, context).makeRef()
                //              jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }
            }
          }catch {
            case e:Exception =>{
              println("****")
            }

          }
        }

        /** 这里要改下字段方法，比如set和get */
        //这里要注意了，如果是funcClass，是没有getset字段方法
        else if (jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
          /**
            * 思路是先找到声明field的类，如果是可以转成deca类，就找deca类里面的方法调用替换掉，如果不是，就不替换
            */
          val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]
          val fieldDeclareClass=jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef].getFieldRef.declaringClass()
          if (decaSet.contains(fieldDeclareClass.toString)) {
            val decaClass=if(originDecaMap.containsKey(fieldDeclareClass.toString)){
              originDecaMap.get(fieldDeclareClass.toString)
            }else{
              fieldDeclareClass
            }
            val putMethod = decaClass.getMethodByNameUnsafe("set" + jInstanceFieldRef.getFieldRef.name())
            if(putMethod!=null) {
              val fieldType = jInstanceFieldRef.getType
              if (fieldType.isInstanceOf[PrimType]) {
                val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef(), jAssignStmt.getRightOp))
                newMethodBody.getUnits.insertBefore(nUnit, unit)
              } else {
                val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef()))
                newMethodBody.getUnits.insertBefore(nUnit, unit)
              }
              newMethodBody.getUnits.remove(unit)
            }

          }else{
            if(fieldDeclareClass.getName.equals(funcClass.getName)){
              if(fieldDeclareClass.getFieldByNameUnsafe(jInstanceFieldRef.getFieldRef.name())!=null){
                jInstanceFieldRef.setFieldRef(fieldDeclareClass.getFieldByName(jInstanceFieldRef.getFieldRef.name()).makeRef())
              }
            }
          }
        } else if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          val fieldDeclareClass=jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].getFieldRef.declaringClass()
          if (decaSet.contains(fieldDeclareClass.toString)) {
            val decaClass=if(originDecaMap.containsKey(fieldDeclareClass.toString)){
              originDecaMap.get(fieldDeclareClass.toString)
            }else{
              fieldDeclareClass
            }
            val getMethod = decaClass.getMethodByNameUnsafe("get" + jInstanceFieldRef.getFieldRef.name())
            if(getMethod!=null) {
              jAssignStmt.setRightOp(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, getMethod.makeRef()))
            }
          }else{
            if(fieldDeclareClass.getName.equals(funcClass.getName)){
              if(fieldDeclareClass.getFieldByNameUnsafe(jInstanceFieldRef.getFieldRef.name())!=null){
                jInstanceFieldRef.setFieldRef(fieldDeclareClass.getFieldByName(jInstanceFieldRef.getFieldRef.name()).makeRef())
              }
            }

          }
        }
        /**
          *这里是对数组local操作
          */
        //如何把arr类型的local调用set方法放进去呢
        else if(jAssignStmt.getLeftOp.isInstanceOf[JArrayRef]) {
          val arrRef = jAssignStmt.getLeftOp.asInstanceOf[JArrayRef]
          val local = arrRef.getBase.asInstanceOf[JimpleLocal]
          val index = arrRef.getIndex
          if (!local.getType.isInstanceOf[ArrayType]){
            newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(local, local.getType.asInstanceOf[RefType].getSootClass.
              getMethodByName("set").makeRef(), Arrays.asList(index, jAssignStmt.getRightOp))), unit)
            newMethodBody.getUnits.remove(unit)
          }
        }
        /**
          * 右边数组
          */
        else if(jAssignStmt.getRightOp.isInstanceOf[JArrayRef]){
          val arrRef=jAssignStmt.getRightOp.asInstanceOf[JArrayRef]
          val local=arrRef.getBase.asInstanceOf[JimpleLocal]
          val index=arrRef.getIndex
          if(!local.getType.isInstanceOf[ArrayType]){
            newMethodBody.getUnits.insertBefore(Jimple.v().newAssignStmt(jAssignStmt.getLeftOp,Jimple.v().newVirtualInvokeExpr(local,local.getType.asInstanceOf[RefType].getSootClass.
              getMethodByName("get").makeRef(),index)),unit)
            newMethodBody.getUnits.remove(unit)
          }

        }

        /**
          * 右边是一个new 数组，变成一个decaArray数组
          */
        else if(jAssignStmt.getRightOp.isInstanceOf[JNewArrayExpr]){
          val leftType=jAssignStmt.getLeftOp.getType

          if(!leftType.isInstanceOf[ArrayType]) {
            newMethodBody.getUnits.insertBefore(Jimple.v().newAssignStmt(jAssignStmt.getLeftOp, Jimple.v().newNewExpr(leftType.asInstanceOf[RefType])), unit)

            newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(jAssignStmt.getLeftOp.asInstanceOf[JimpleLocal], leftType.asInstanceOf[RefType].getSootClass
              .getMethodByName("<init>").makeRef())), unit)
            newMethodBody.getUnits.remove(unit)
          }

        }else if(jAssignStmt.getRightOp.isInstanceOf[JCastExpr]){
          val casttype=jAssignStmt.getRightOp.asInstanceOf[JCastExpr].getCastType
          jAssignStmt.getRightOp.asInstanceOf[JCastExpr].setCastType(getRelationTypeString(casttype,context))
        }

      } else if (unit.isInstanceOf[JInvokeStmt]) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]

        if (unit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JVirtualInvokeExpr] || unit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JInterfaceInvokeExpr]) {
          val jVirtualInvokeExpr = if (jInvokeStmt.getInvokeExpr.isInstanceOf[JVirtualInvokeExpr]) {
            jInvokeStmt.getInvokeExpr.asInstanceOf[JVirtualInvokeExpr]
          } else {
            jInvokeStmt.getInvokeExpr.asInstanceOf[JInterfaceInvokeExpr]
          }
          val baseClass = jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes = jVirtualInvokeExpr.getArgs.map(arg => arg.getType)
          //这里有区别？
          val mr = jVirtualInvokeExpr.getMethodRef
          if (baseClass.getMethodUnsafe(mr.getSubSignature)!=null) {
            val method = jVirtualInvokeExpr.getMethod
            val returnType = method.getReturnType
            val methodClass = method.getDeclaringClass
            if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString)||decaSet.contains(returnType.toString)) {
              //这里加一句吧
              val decaMethod=if(originDecaMethodMap.containsKey(method.getSubSignature)){
                originDecaMethodMap.get(method.getSubSignature)
              }else{
                method
              }
              val actualMethod=getActualInvokeString(baseClass,decaMethod,context)
              if (actualMethod == null) {
                if (baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                  val nUnit=new JInvokeStmt(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase,createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef(),
                    jVirtualInvokeExpr.getArgs))
                  newMethodBody.getUnits.insertBefore(nUnit,unit)
                  newMethodBody.getUnits.remove(unit)

                  //                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                }
                else {
                  val nUnit=new JInvokeStmt(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase,baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef(),jVirtualInvokeExpr.getArgs))
                  newMethodBody.getUnits.insertBefore(nUnit,unit)
                  newMethodBody.getUnits.remove(unit)
                  //                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                }
              } else {

                val nUnit=new JInvokeStmt(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase,createMethodForFuncClassString(actualMethod, funcClass, realTypes,  context).makeRef(),jVirtualInvokeExpr.getArgs))
                newMethodBody.getUnits.insertBefore(nUnit,unit)
                newMethodBody.getUnits.remove(unit)
                //              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, context).makeRef()
                //              jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }

            }
          }
        }


      }else if(unit.isInstanceOf[JReturnStmt]){
        val retuOpe=unit.asInstanceOf[JReturnStmt].getOp
        if(newSootClass.getMethodUnsafe(newMethod.getName,newMethod.getParameterTypes,retuOpe.getType)==null){
          if(isExist){

            val tempMethod=new SootMethod(newMethod.getName,newMethod.getParameterTypes,retuOpe.getType,newMethod.getModifiers,newMethod.getExceptions)
            val tempBody=Utils.cloneSootBody(newMethodBody)
            tempMethod.setActiveBody(tempBody)
            transformedMethods.add(tempMethod.getSubSignature)
          }else{
            newMethod.setReturnType(retuOpe.getType)
          }
        }
      }
    }
    try {
      newMethodBody.getThisLocal.setType(newSootClass.getType)
    }catch {
      case e:Exception=>{

      }
    }
    removeUnuseLocals(newMethod)
    newMethod

  }

  def createMethodForFuncClass(oldMethod:SootMethod,funcClass:SootClass,realParaTypes:util.List[Type],originDecaMap:util.HashMap[SootClass,SootClass],originTempMap:util.HashMap[SootClass,SootClass],decaSet:util.HashSet[String],decaOriginMap:util.HashMap[SootClass,SootClass],
                               originDecaMethodMap:util.HashMap[SootMethod,SootMethod],transformedMethods:util.HashSet[SootMethod],context: Context): SootMethod = {

    //首先判断是哪的方法吧
    val newSootClass = getNewSootClass(oldMethod, funcClass, originDecaMap)
    var isExist = false
    //这里的SIGNATURES是一样的么，会因为参数传入而改变么
    if (newSootClass.getMethodUnsafe(covertName(oldMethod, originTempMap, newSootClass, context), realParaTypes
      , covertType(oldMethod.getReturnType, originDecaMap, context)) != null) {
      val nMethod = newSootClass.getMethodUnsafe(covertName(oldMethod, originTempMap, newSootClass, context), realParaTypes
        , covertType(oldMethod.getReturnType, originDecaMap, context))
      isExist = true
      if (transformedMethods.size() != 0 && transformedMethods.contains(nMethod))
        return newSootClass.getMethodUnsafe(covertName(oldMethod, originTempMap, newSootClass, context), realParaTypes
          , covertType(oldMethod.getReturnType, originDecaMap, context))
    }


    val pa = context.scene.getPointsToAnalysis

    val newMethod = if (!isExist) {
      new SootMethod(covertName(oldMethod, originTempMap, newSootClass, context), realParaTypes
        , covertType(oldMethod.getReturnType, originDecaMap, context),
        oldMethod.getModifiers, oldMethod.getExceptions)
    } else {
      newSootClass.getMethodUnsafe(covertName(oldMethod, originTempMap, newSootClass, context), realParaTypes
        , covertType(oldMethod.getReturnType, originDecaMap, context))
    }
    newMethod.setDeclaringClass(newSootClass)
    transformedMethods.add(newMethod)


    if (!oldMethod.hasActiveBody) {
      return newMethod

    }
    if (!isExist){
    val localMethodBody = oldMethod.getActiveBody
    newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
    newSootClass.addMethod(newMethod)
    }
    val newMethodBody = newMethod.retrieveActiveBody()
    val newLocals=newMethodBody.getLocals

    /**
      * 设置对应类型
      */
    var flag=true

    var lastLocal:Local=null
    var curLocal:Local=null
    for(local<-oldMethod.getActiveBody.getLocals){
      if(!flag){
        curLocal=newLocals.getSuccOf(lastLocal)
      }else{
        flag=false
        curLocal=newLocals.getFirst
      }
      var ty=local.getType

      if(ty.isInstanceOf[RefType]) {
        val pts = pa.reachingObjects(local).possibleTypes()
        if (pts.size() == 1) {
          if (pts.toArray.apply(0).isInstanceOf[AnySubType]) {
            ty = pts.toArray.apply(0).asInstanceOf[AnySubType].getBase

          }else if(pts.toArray.apply(0).isInstanceOf[RefType]){

            ty=pts.toArray.apply(0).asInstanceOf[Type]
          }
        }
      }
      curLocal.setType(getRelationType(ty,originDecaMap,context))
      lastLocal=curLocal

    }



    var randIndex=0

    for (unit <- newMethodBody.getUnits.snapshotIterator()) {
//      if(oldMethod.getName.equals("apply")&&oldMethod.getReturnType.toString.equals("breeze.linalg.Vector")){
//        print()
//      }
      if (unit.isInstanceOf[JIdentityStmt]) {
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
//          jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal].setType(newSootClass.getType)
          jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
        }else if(jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]){
          val ty=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getType
          val index=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getIndex
          jIdentityStmt.setRightOp(Jimple.v().newParameterRef(realParaTypes.get(index),index))
          jIdentityStmt.getLeftOp.asInstanceOf[JimpleLocal].setType(realParaTypes.get(index))
        }
      }
      else if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]


          if(jVirtualInvokeExpr.getBase.isInstanceOf[RefType]) {
            val baseClass = jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
            val realTypes = jVirtualInvokeExpr.getArgs.map(arg => arg.getType)
            var findMethodException = false
            try {
              val method = jVirtualInvokeExpr.getMethod

              if (findMethodException == false) {
                val returnType = method.getReturnType
                val methodClass = method.getDeclaringClass
                if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
                  //这里加一句吧
                  val decaMethod = if (originDecaMethodMap.containsKey(method)) {
                    originDecaMethodMap.get(method)
                  } else {
                    method
                  }
                  val actualMethod = getActualInvoke(baseClass, decaMethod, decaOriginMap)
                  if (actualMethod == null) {
                    if (baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                      jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                    }
                    else {
                      jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                    }

                  } else {
                    val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef()
                    jVirtualInvokeExpr.setMethodRef(newMethodRef)
                  }
                }
              }

            } catch {
              case e: Exception => {
                val base = jVirtualInvokeExpr.getBase
                println("****did not find method  " + unit.toString())
                findMethodException = true


              }
            }
          }

        } else if (jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]


          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          val method=jVirtualInvokeExpr.getMethod
          val returnType=method.getReturnType
          val methodClass=method.getDeclaringClass
          if(decaSet.contains(methodClass.toString)||containsBySet(decaSet,realTypes)||decaSet.contains(baseClass.toString)||decaSet.contains(returnType.toString)){
            //这里加一句吧
            val decaMethod=if(originDecaMethodMap.containsKey(method)){
              originDecaMethodMap.get(method)
            }else{
              method
            }
            val actualMethod=getActualInvoke(baseClass,decaMethod,decaOriginMap)
            if(actualMethod==null){
              if(baseClass.getMethodUnsafe(method.getName,jVirtualInvokeExpr.getArgs.map(arg=>arg.getType),returnType)==null) {
                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
              }
              else {
                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
              }
            }else {

              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap,originDecaMethodMap,transformedMethods, context).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }

          }

        }
        else  if (jAssignStmt.getRightOp.isInstanceOf[JStaticInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JStaticInvokeExpr]

          val method=jVirtualInvokeExpr.getMethod
          //附加一些东西
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          val returnType=method.getReturnType
          val methodClass=method.getDeclaringClass

          /**
            *
            */
          if(decaSet.contains(methodClass.toString)||containsBySet(decaSet,realTypes)||decaSet.contains(returnType.toString)){
            //这里加一句吧
            val decaMethod=if(originDecaMethodMap.containsKey(method)){
              originDecaMethodMap.get(method)
            }else{
              method
            }
            val newMethodRef = createMethodForFuncClass(decaMethod,funcClass,realTypes,originDecaMap,originTempMap,decaSet,decaOriginMap,originDecaMethodMap,transformedMethods,context).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        }
        else if (jAssignStmt.getLeftOp.isInstanceOf[JStaticInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JStaticInvokeExpr]
          //判断下这个方法是不是父类方法
          val method=jVirtualInvokeExpr.getMethod
          //附加一些东西
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          val returnType=method.getReturnType
          val methodClass=method.getDeclaringClass

          if(decaSet.contains(methodClass.toString)||containsBySet(decaSet,realTypes)||decaSet.contains(returnType.toString)){
            //这里加一句吧
            val decaMethod=if(originDecaMethodMap.containsKey(method)){
              originDecaMethodMap.get(method)
            }else{
              method
            }
            val newMethodRef = createMethodForFuncClass(decaMethod,funcClass,realTypes,originDecaMap,originTempMap,decaSet,decaOriginMap,originDecaMethodMap,transformedMethods,context).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        }
        else if(jAssignStmt.getRightOp.isInstanceOf[JInterfaceInvokeExpr]){

          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JInterfaceInvokeExpr]
          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          try {
            val methodRef=jVirtualInvokeExpr.getMethodRef


            val returnType = methodRef.returnType()
            val methodClass = methodRef.declaringClass()
            if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
              val methodName=methodRef.name()
              val methodParameters=methodRef.parameterTypes()

              val actualMethod = getInterfaceInvoke(baseClass,methodName,methodParameters,returnType,decaOriginMap)
              if (actualMethod == null) {
                println("*******************"+methodClass.getShortName+methodName)
                if (baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                  jAssignStmt.setRightOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createEmptyMethod(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                }
                else {
                  jAssignStmt.setRightOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                }
              } else {
                jAssignStmt.setRightOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef(), jVirtualInvokeExpr.getArgs))
                //              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, context).makeRef()
                //              jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }
            }
          }catch {
            case e:Exception=> {
              println("****")
            }

          }

        }
        else if(jAssignStmt.getLeftOp.isInstanceOf[JInterfaceInvokeExpr]){

          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JInterfaceInvokeExpr]
          val baseClass=jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass
          val realTypes=jVirtualInvokeExpr.getArgs.map(arg=>arg.getType)
          try {
            val methodRef=jVirtualInvokeExpr.getMethodRef


            val returnType = methodRef.returnType()
            val methodClass = methodRef.declaringClass()
            if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
              //              //这里加一句吧
              //              val decaMethod = if (originDecaMethodMap.containsKey(method)) {
              //                originDecaMethodMap.get(method)
              //              } else {
              //                method
              //              }
              val methodName=methodRef.name()
              val methodParameters=methodRef.parameterTypes()

              val actualMethod = getInterfaceInvoke(baseClass,methodName,methodParameters,returnType,decaOriginMap)
              if (actualMethod == null) {
                if (baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                  jAssignStmt.setLeftOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createEmptyMethod(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                }
                else {
                  jAssignStmt.setLeftOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, baseClass.getMethodUnsafe(methodClass.getShortName+methodName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef(), jVirtualInvokeExpr.getArgs))
                  //                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                }
              } else {
                jAssignStmt.setLeftOp(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef(), jVirtualInvokeExpr.getArgs))
                //              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, context).makeRef()
                //              jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }
            }
          }catch {
            case e:Exception=> {

              println("****")
            }

          }
        }

        /** 这里要改下字段方法，比如set和get */
        //这里要注意了，如果是funcClass，是没有getset字段方法
        else if (jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
          /**
            * 思路是先找到声明field的类，如果是可以转成deca类，就找deca类里面的方法调用替换掉，如果不是，就不替换
            */
          val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]
          val fieldDeclareClass=jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef].getFieldRef.declaringClass()
          if (decaSet.contains(fieldDeclareClass.toString)) {
            val decaClass=if(originDecaMap.containsKey(fieldDeclareClass)){
              originDecaMap.get(fieldDeclareClass)
            }else{
              fieldDeclareClass
            }
            val putMethod = decaClass.getMethodByNameUnsafe("set" + jInstanceFieldRef.getFieldRef.name())
            if(putMethod!=null) {
              val fieldType = jInstanceFieldRef.getType
              if (fieldType.isInstanceOf[PrimType]) {
                val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef(), jAssignStmt.getRightOp))
                newMethodBody.getUnits.insertBefore(nUnit, unit)
              } else {
                val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef()))
                newMethodBody.getUnits.insertBefore(nUnit, unit)
              }
              newMethodBody.getUnits.remove(unit)
            }

          }else{
            if(fieldDeclareClass.getName.equals(funcClass.getName)){
              if(fieldDeclareClass.getFieldByNameUnsafe(jInstanceFieldRef.getFieldRef.name())!=null){
                jInstanceFieldRef.setFieldRef(fieldDeclareClass.getFieldByName(jInstanceFieldRef.getFieldRef.name()).makeRef())
              }
            }
          }
        } else if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          val fieldDeclareClass=jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].getFieldRef.declaringClass()
          if (decaSet.contains(fieldDeclareClass.toString)) {
            val decaClass=if(originDecaMap.containsKey(fieldDeclareClass)){
              originDecaMap.get(fieldDeclareClass)
            }else{
              fieldDeclareClass
            }
            val getMethod = decaClass.getMethodByNameUnsafe("get" + jInstanceFieldRef.getFieldRef.name())
            if(getMethod!=null) {
              jAssignStmt.setRightOp(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, getMethod.makeRef()))
            }
          }else{
            if(fieldDeclareClass.getName.equals(funcClass.getName)){
              if(fieldDeclareClass.getFieldByNameUnsafe(jInstanceFieldRef.getFieldRef.name())!=null){
                jInstanceFieldRef.setFieldRef(fieldDeclareClass.getFieldByName(jInstanceFieldRef.getFieldRef.name()).makeRef())
              }
            }

          }
        }
        /**
          *这里是对数组local操作
          */
        //如何把arr类型的local调用set方法放进去呢
        else if(jAssignStmt.getLeftOp.isInstanceOf[JArrayRef]) {
          val arrRef = jAssignStmt.getLeftOp.asInstanceOf[JArrayRef]
          val local = arrRef.getBase.asInstanceOf[JimpleLocal]
          val index = arrRef.getIndex
          if (!local.getType.isInstanceOf[ArrayType]){
            newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(local, local.getType.asInstanceOf[RefType].getSootClass.
              getMethodByName("set").makeRef(), Arrays.asList(index, jAssignStmt.getRightOp))), unit)
            newMethodBody.getUnits.remove(unit)
          }
        }
        /**
          * 右边数组
          */
        else if(jAssignStmt.getRightOp.isInstanceOf[JArrayRef]){
          val arrRef=jAssignStmt.getRightOp.asInstanceOf[JArrayRef]
          val local=arrRef.getBase.asInstanceOf[JimpleLocal]
          val index=arrRef.getIndex
          if(!local.getType.isInstanceOf[ArrayType]){
            newMethodBody.getUnits.insertBefore(Jimple.v().newAssignStmt(jAssignStmt.getLeftOp,Jimple.v().newVirtualInvokeExpr(local,local.getType.asInstanceOf[RefType].getSootClass.
              getMethodByName("get").makeRef(),index)),unit)
            newMethodBody.getUnits.remove(unit)
          }

        }

        /**
          * 右边是一个new 数组，变成一个decaArray数组
          */
        else if(jAssignStmt.getRightOp.isInstanceOf[JNewArrayExpr]){
          val leftType=jAssignStmt.getLeftOp.getType

          if(!leftType.isInstanceOf[ArrayType]) {
            newMethodBody.getUnits.insertBefore(Jimple.v().newAssignStmt(jAssignStmt.getLeftOp, Jimple.v().newNewExpr(leftType.asInstanceOf[RefType])), unit)

            newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(jAssignStmt.getLeftOp.asInstanceOf[JimpleLocal], leftType.asInstanceOf[RefType].getSootClass
              .getMethodByName("<init>").makeRef())), unit)
            newMethodBody.getUnits.remove(unit)
          }

        }else if(jAssignStmt.getRightOp.isInstanceOf[JCastExpr]){
          val casttype=jAssignStmt.getRightOp.asInstanceOf[JCastExpr].getCastType
          jAssignStmt.getRightOp.asInstanceOf[JCastExpr].setCastType(getRelationType(casttype,originDecaMap,context))
        }

      } else if (unit.isInstanceOf[JInvokeStmt]) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]

        if (unit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JVirtualInvokeExpr] || unit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JInterfaceInvokeExpr]) {
          val jVirtualInvokeExpr = if (jInvokeStmt.getInvokeExpr.isInstanceOf[JVirtualInvokeExpr]) {
            jInvokeStmt.getInvokeExpr.asInstanceOf[JVirtualInvokeExpr]
          } else {
            jInvokeStmt.getInvokeExpr.asInstanceOf[JInterfaceInvokeExpr]
          }
          if (jVirtualInvokeExpr.getBase.getType.isInstanceOf[RefType]){
          val baseClass = jVirtualInvokeExpr.getBase.getType.asInstanceOf[RefType].getSootClass

          val realTypes = jVirtualInvokeExpr.getArgs.map(arg => arg.getType)
          //这里有区别？
          val mr = jVirtualInvokeExpr.getMethodRef
          if (baseClass.getMethodUnsafe(mr.getSubSignature) != null) {
            val method = jVirtualInvokeExpr.getMethod
            val returnType = method.getReturnType
            val methodClass = method.getDeclaringClass
            if (decaSet.contains(methodClass.toString) || containsBySet(decaSet, realTypes) || decaSet.contains(baseClass.toString) || decaSet.contains(returnType.toString)) {
              //这里加一句吧
              val decaMethod = if (originDecaMethodMap.containsKey(method)) {
                originDecaMethodMap.get(method)
              } else {
                method
              }
              val actualMethod = getActualInvoke(baseClass, decaMethod, decaOriginMap)
              if (actualMethod == null) {
                if (baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType) == null) {
                  val nUnit = new JInvokeStmt(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef(),
                    jVirtualInvokeExpr.getArgs))
                  newMethodBody.getUnits.insertBefore(nUnit, unit)
                  newMethodBody.getUnits.remove(unit)

                  //                jVirtualInvokeExpr.setMethodRef(createEmptyMethod(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType, baseClass).makeRef())
                }
                else {
                  val nUnit = new JInvokeStmt(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef(), jVirtualInvokeExpr.getArgs))
                  newMethodBody.getUnits.insertBefore(nUnit, unit)
                  newMethodBody.getUnits.remove(unit)
                  //                jVirtualInvokeExpr.setMethodRef(baseClass.getMethodUnsafe(method.getName, jVirtualInvokeExpr.getArgs.map(arg => arg.getType), returnType).makeRef())
                }
              } else {

                val nUnit = new JInvokeStmt(new JVirtualInvokeExpr(jVirtualInvokeExpr.getBase, createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, originDecaMethodMap, transformedMethods, context).makeRef(), jVirtualInvokeExpr.getArgs))
                newMethodBody.getUnits.insertBefore(nUnit, unit)
                newMethodBody.getUnits.remove(unit)
                //              val newMethodRef = createMethodForFuncClass(actualMethod, funcClass, realTypes, originDecaMap, originTempMap, decaSet, decaOriginMap, context).makeRef()
                //              jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }

            }
          }
        }
        }


      }else if(unit.isInstanceOf[JReturnStmt]){
        val retuOpe=unit.asInstanceOf[JReturnStmt].getOp
        if(newSootClass.getMethodUnsafe(newMethod.getName,newMethod.getParameterTypes,retuOpe.getType)==null){
          if(isExist){

            val tempMethod=new SootMethod(newMethod.getName,newMethod.getParameterTypes,retuOpe.getType,newMethod.getModifiers,newMethod.getExceptions)
            val tempBody=Utils.cloneSootBody(newMethodBody)
            tempMethod.setActiveBody(tempBody)
            transformedMethods.add(tempMethod)
          }else{
            newMethod.setReturnType(retuOpe.getType)
          }
        }
      }
    }
    newMethodBody.getThisLocal.setType(newSootClass.getType)

    removeUnuseLocals(newMethod)
    newMethod

  }



  def getFieldsAndMethodsUsed(sootClass: SootClass,context: Context):(util.List[SootField],util.List[SootMethod])={

    val usedFields=new util.ArrayList[SootField]()
    val usedMethods=new util.ArrayList[SootMethod]()
    var parent=sootClass
    while ((!parent.getName.equals("java.lang.Object"))&&(!parent.isAbstract)){
      parent.getFields.map(f=>usedFields.add(f))
      parent.getMethods.map(m=>usedMethods.add(m))
      parent=parent.getSuperclass
    }
    (usedFields,usedMethods)
  }


  //这些field可能declaringCLass不是本类，方法也不一定是，
  //如果是属于sootClass父类的
  def createDecaClass(sootClass: SootClass,originDecaMap:util.HashMap[SootClass,SootClass],originTempMap:util.HashMap[SootClass,SootClass],
                      decaOriginMap:util.HashMap[SootClass,SootClass],tempDecaMethodMap:util.HashMap[SootMethod,SootMethod],context: Context):SootClass={
    create(sootClass.getType,0,originDecaMap,originTempMap,decaOriginMap,tempDecaMethodMap,context)
  }

  def isSupperClass(son:SootClass,parent:SootClass,originTempMap:util.HashMap[SootClass,SootClass]):Boolean={

    if(parent.getName.equals("java.lang.Object"))
      return false

    val realParent=if(originTempMap.containsKey(parent)){
      originTempMap.get(parent)
    }else{
      parent
    }



    var temp=son
    while (!temp.getName.equals(realParent.getName)&&(!temp.getName.equals("java.lang.Object"))){
      temp=temp.getSuperclass
    }
    if(temp.getName.equals(realParent.getName)){
     return true
    }
    false

  }


  // 这是用来转换方法里面的参数和返回类型

  def covertType(ty:Type,originDecaMap:util.HashMap[SootClass,SootClass],context: Context):Type={


    if(ty.isInstanceOf[RefType]){
      val tysc=ty.asInstanceOf[RefType].getSootClass
      if(originDecaMap.containsKey(tysc)){
        return originDecaMap.get(tysc).getType
      }else{
        return ty
      }
    }else if(ty.isInstanceOf[ArrayType]){
      if(createArrayDeca(ty,context)!=null)
        createArrayDeca(ty,context).getType
      else
        ty
    }else{
      ty
    }
  }
  def covertTypeString(ty:Type,context: Context):Type={


    if(ty.isInstanceOf[RefType]){
      val tysc=ty.asInstanceOf[RefType].getSootClass
      if(TransformCollection.originDecaMapStrng.containsKey(tysc.toString)){
        return TransformCollection.originDecaMapStrng.get(tysc.toString).getType
      }else{
        return ty
      }
    }else if(ty.isInstanceOf[ArrayType]){
      if(createArrayDeca(ty,context)!=null)
        createArrayDeca(ty,context).getType
      else
        ty
    }else{
      ty
    }
  }

  //转换方法的名字吧，加前缀，比如如果是父类就加父类名前缀
  def covertName(oldMethod:SootMethod,originTempMap:util.HashMap[SootClass,SootClass],destinationClass:SootClass,context: Context):String={
    val methodClass=oldMethod.getDeclaringClass

//    if(methodClass.getName.endsWith("Deca")){
//      return oldMethod.getName
//    }
    if(methodClass.getName.equals(destinationClass.toString)){
      return oldMethod.getName
    }

    val decaClasses=originTempMap.values()
    if(originTempMap.containsKey(methodClass)){
      return originTempMap.get(methodClass).getShortName+oldMethod.getName
    }else if(decaClasses.contains(methodClass)){
      oldMethod.getName
    }
    else {
      methodClass.getShortName+oldMethod.getName
    }
  }
  def covertNameString(oldMethod:SootMethod,destinationClass:SootClass,context: Context):String={
    val methodClass=oldMethod.getDeclaringClass

    if(methodClass.getName.equals(destinationClass.toString)){
      return oldMethod.getName
    }

    val decaClasses=TransformCollection.originTempMapStrng.values()
    if(TransformCollection.originTempMapStrng.containsKey(methodClass.toString)){
      return TransformCollection.originTempMapStrng.get(methodClass.toString).getShortName+oldMethod.getName
    }else if(decaClasses.contains(methodClass)){
      oldMethod.getName
    }
    else {
      methodClass.getShortName+oldMethod.getName
    }
  }

  /**
    * 这里是为temp创建decaclass里面的方法转换，主要涉及的有，一些类型到特化类型
    * @param oldMethod
    * @param oldSootClass
    * @param newSootClass
    * @param originDecaMap
    * @param originTempMap
    * @param context
    */
  def createMethod(oldMethod:SootMethod,oldSootClass:SootClass,newSootClass:SootClass,originDecaMap:util.HashMap[SootClass,SootClass],originTempMap:util.HashMap[SootClass,SootClass],context: Context): SootMethod ={

    //这里的SIGNATURES是一样的么，会因为参数传入而改变么
    if(newSootClass.getMethodUnsafe(covertName(oldMethod,originTempMap,newSootClass,context),oldMethod.getParameterTypes.map(ty=>covertType(ty,originDecaMap,context))
      ,covertType(oldMethod.getReturnType,originDecaMap,context))!=null){
      return  null
    }
    val newMethod = new SootMethod(covertName(oldMethod,originTempMap,newSootClass,context), oldMethod.getParameterTypes.map(ty=>covertType(ty,originDecaMap,context))
      ,covertType(oldMethod.getReturnType,originDecaMap,context),
      oldMethod.getModifiers, oldMethod.getExceptions)
    newMethod.setDeclaringClass(newSootClass)
    newSootClass.addMethod(newMethod)

    if(!oldMethod.hasActiveBody){
      return newMethod
    }
    val localMethodBody = oldMethod.getActiveBody
    newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
    val newMethodBody = newMethod.retrieveActiveBody()

    for (local <- newMethodBody.getLocals) {
      local.setType(covertType(local.getType,originDecaMap,context))
    }

    //我怀疑这里万一，有的方法没克隆完，那么方法转换会出错的，所以最好是先对所有方法进行上面的循环，再对所有方法进行下面的循环
    val localFieldMap=new mutable.HashMap[JimpleLocal,SootField]()
    var randIndex=0

    for (unit <- newMethodBody.getUnits.snapshotIterator()) {

      var findExcept=false
      if (unit.isInstanceOf[JIdentityStmt]) {
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
          jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
        }else if(jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]){
          val ty=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getType
          val index=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getIndex
          jIdentityStmt.setRightOp(Jimple.v().newParameterRef(covertType(ty,originDecaMap,context),index))
        }
      }
      else if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {

          try {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]
          //判断下这个方法是不是父类方法
          //这里有异常，如果被裁剪掉
          val method = jVirtualInvokeExpr.getMethod
          if(findExcept==false) {
            if (isSupperClass(oldSootClass, method.getDeclaringClass, originTempMap)) {
              if (newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
                covertType(method.getReturnType, originDecaMap, context)) == null) {
                createMethod(method, oldSootClass, newSootClass, originDecaMap, originTempMap, context)

              }
              if (newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)), covertType(method.getReturnType, originDecaMap, context)) != null) {
                val newMethodRef = newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)), covertType(method.getReturnType, originDecaMap, context)).makeRef()
                jVirtualInvokeExpr.setMethodRef(newMethodRef)
              }
              //            val returnType=newSootClass.getMethod(covertName(method,originTempMap,context),method.getParameterTypes.map(ty=>covertType(ty,originDecaMap,context))).getReturnType
              //            if(jAssignStmt.getLeftOp.isInstanceOf[JimpleLocal]){
              //              jAssignStmt.getLeftOp.asInstanceOf[JimpleLocal].setType(returnType)
              //            }
            }
          }
        }catch {
            case e:Exception=> {
              println(" *******************\n*********************\nthe method has been tail wrong "+unit.toString()+"\n************************")
               findExcept=true
            }

          }

        } else if(jAssignStmt.getRightOp.isInstanceOf[JStaticInvokeExpr]){
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JStaticInvokeExpr]
          //判断下这个方法是不是父类方法
          val method=jVirtualInvokeExpr.getMethod
          if(isSupperClass(oldSootClass,method.getDeclaringClass,originTempMap)){
            if(newSootClass.getMethodUnsafe(covertName(method,originTempMap,newSootClass,context),method.getParameterTypes.map(ty=>covertType(ty,originDecaMap,context)),
              covertType(method.getReturnType,originDecaMap,context))==null){
              createMethod(method,oldSootClass,newSootClass,originDecaMap,originTempMap,context)

            }
            if(newSootClass.getMethodUnsafe(covertName(method, originTempMap,newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)), covertType(method.getReturnType, originDecaMap, context))!=null) {
              val newMethodRef = newSootClass.getMethodUnsafe(covertName(method, originTempMap,newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)), covertType(method.getReturnType, originDecaMap, context)).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }
            //            val returnType=newSootClass.getMethod(covertName(method,originTempMap,context),method.getParameterTypes.map(ty=>covertType(ty,originDecaMap,context))).getReturnType
            //            if(jAssignStmt.getLeftOp.isInstanceOf[JimpleLocal]){
            //              jAssignStmt.getLeftOp.asInstanceOf[JimpleLocal].setType(returnType)
            //            }
          }
        }

        else if (jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]
          //判断下这个方法是不是父类方法
          val method=jVirtualInvokeExpr.getMethod
          if(isSupperClass(oldSootClass,method.getDeclaringClass,originTempMap)) {
            if (newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass,context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
              covertType(method.getReturnType, originDecaMap, context)) == null) {
              createMethod(method, oldSootClass, newSootClass, originDecaMap, originTempMap, context)

            }
            if (newSootClass.getMethodUnsafe(covertName(method, originTempMap,newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
              covertType(method.getReturnType, originDecaMap, context))!=null){
              val newMethodRef = newSootClass.getMethodUnsafe(covertName(method, originTempMap,newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
                covertType(method.getReturnType, originDecaMap, context)).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }
          }
        }

        /** 这里要改下字段方法，比如set和get */
        else if (jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]
          if (isSupperClass(oldSootClass,jInstanceFieldRef.getFieldRef.declaringClass(),originTempMap)) {
            val putMethod = newSootClass.getMethodByNameUnsafe("set" + jInstanceFieldRef.getFieldRef.name())
            if(putMethod!=null){
              val fieldType = jInstanceFieldRef.getType


              if (fieldType.isInstanceOf[PrimType]) {
                val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef(), jAssignStmt.getRightOp))
                newMethodBody.getUnits.insertBefore(nUnit, unit)

              } else {
                val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef()))
                newMethodBody.getUnits.insertBefore(nUnit, unit)
              }
              newMethodBody.getUnits.remove(unit)
            }
          }
        } else if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          if (isSupperClass(oldSootClass,jInstanceFieldRef.getFieldRef.declaringClass(),originTempMap)) {

            val getMethod = newSootClass.getMethodByNameUnsafe("get" + jInstanceFieldRef.getFieldRef.name())
            if(getMethod!=null) {

              jAssignStmt.setRightOp(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, getMethod.makeRef()))
            }

          }
        }

        /**
          *这里是对数组local操作
          */
        //如何把arr类型的local调用set方法放进去呢

        else if(jAssignStmt.getLeftOp.isInstanceOf[JArrayRef]){

          val arrRef=jAssignStmt.getLeftOp.asInstanceOf[JArrayRef]
          val local=arrRef.getBase.asInstanceOf[JimpleLocal]
          val index=arrRef.getIndex


          try {
            if (!local.getType.isInstanceOf[ArrayType]) {

              newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(local, local.getType.asInstanceOf[RefType].getSootClass.
                getMethodByName("set").makeRef(), Arrays.asList(index, jAssignStmt.getRightOp))), unit)
              newMethodBody.getUnits.remove(unit)
            }
          }catch {
            case e:Exception=>{
              println("****")
            }
          }

        }

        /**
          * 右边数组
          */
        else if(jAssignStmt.getRightOp.isInstanceOf[JArrayRef]){
          val arrRef=jAssignStmt.getRightOp.asInstanceOf[JArrayRef]
          val local=arrRef.getBase.asInstanceOf[JimpleLocal]
          val index=arrRef.getIndex


          if(!local.getType.isInstanceOf[ArrayType]) {

            newMethodBody.getUnits.insertBefore(Jimple.v().newAssignStmt(jAssignStmt.getLeftOp, Jimple.v().newVirtualInvokeExpr(local, local.getType.asInstanceOf[RefType].getSootClass.
              getMethodByName("get").makeRef(), index)), unit)

            newMethodBody.getUnits.remove(unit)
          }
        }

        /**
          * 右边是一个new 数组，变成一个decaArray数组
          */
        else if(jAssignStmt.getRightOp.isInstanceOf[JNewArrayExpr]) {
          val leftType = jAssignStmt.getLeftOp.getType

          if (!leftType.isInstanceOf[ArrayType]){
            newMethodBody.getUnits.insertBefore(Jimple.v().newAssignStmt(jAssignStmt.getLeftOp, Jimple.v().newNewExpr(leftType.asInstanceOf[RefType])), unit)

            newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(jAssignStmt.getLeftOp.asInstanceOf[JimpleLocal], leftType.asInstanceOf[RefType].getSootClass
              .getMethodByName("<init>").makeRef())), unit)
            newMethodBody.getUnits.remove(unit)

          }
        }else if(jAssignStmt.getRightOp.isInstanceOf[JCastExpr]){
          val castExpr=jAssignStmt.getRightOp.asInstanceOf[JCastExpr]
          val castType=castExpr.getCastType
          castExpr.setCastType(covertType(castType,originDecaMap,context))
        }

      } else if (unit.isInstanceOf[JInvokeStmt]) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        try {
          val method = jInvokeStmt.getInvokeExpr.getMethod
          //        if (invokeMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
          if (isSupperClass(oldSootClass, method.getDeclaringClass(), originTempMap)) {

            if (newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
              covertType(method.getReturnType, originDecaMap, context)) == null) {
              createMethod(method, oldSootClass, newSootClass, originDecaMap, originTempMap, context)

            }

            if (newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
              covertType(method.getReturnType, originDecaMap, context)) != null) {
              val newInvokeMethodRef = newSootClass.getMethodUnsafe(covertName(method, originTempMap, newSootClass, context), method.getParameterTypes.map(ty => covertType(ty, originDecaMap, context)),
                covertType(method.getReturnType, originDecaMap, context)).makeRef()
              jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
            }
          }
        }
        catch {
          case e:Exception=>{
            println("****method is not exist")
          }
        }
      }else if(unit.isInstanceOf[JReturnStmt]){
        val op=unit.asInstanceOf[JReturnStmt].getOp
        if(newMethod.getReturnType.toString.equals("java.lang.Object"))
          if(newSootClass.getMethodUnsafe(newMethod.getName,newMethod.getParameterTypes,op.getType)==null)
            newMethod.setReturnType(op.getType)
      }
    }
    removeUnuseLocals(newMethod)
    newMethod

  }

  def putkv2DecaMap(oldClass:SootClass,decaClass:SootClass,originDecaMap:util.HashMap[SootClass,SootClass],context: Context): Unit ={
    var parent=oldClass
    while (!parent.getName.equals("java.lang.Object")){
      originDecaMap.put(parent,decaClass)
      if(parent.getName.endsWith("temp")){
        if(context.scene.getSootClassUnsafe(parent.getName.substring(0,parent.getName.length-4))!=null){
          originDecaMap.put(context.sootClass(parent.getName.substring(0,parent.getName.length-4)),decaClass)
        }
      }

      parent=parent.getSuperclass
    }

  }
  def create(classType:Type,curOffset:Long,originDecaMap:util.HashMap[SootClass,SootClass],originTempMap:util.HashMap[SootClass,SootClass],decaOriginMap:util.HashMap[SootClass,SootClass],
             tempDecaMethodMap:util.HashMap[SootMethod,SootMethod],context: Context):SootClass={
    var result:SootClass=null
    if(classType.isInstanceOf[RefType]&&(!classType.toString.equals("java.lang.Class"))&&classType.asInstanceOf[RefType].getSootClass.getFields.size()!=0){
      val refType=classType.asInstanceOf[RefType]
      val sootClass=refType.getSootClass


      val sootClassName=sootClass.getName
      val decaName= if(sootClassName.endsWith("temp")) {
        sootClassName.substring(0, sootClassName.length - 4) + "Deca"
      }else{
        sootClassName+"Deca"
      }

      if(context.scene.getSootClassUnsafe(decaName)!=null){
        return context.sootClass(decaName)
      }
      //oldClass
      result=new SootClass(decaName,Modifier.PUBLIC)
      result.setSuperclass(context.sootClass("java.lang.Object"))

      decaOriginMap.put(result,sootClass)

      ///////////////////////
      putkv2DecaMap(sootClass,result,originDecaMap,context)




      context.applicationClasses.add(result)
      addFieldAndSetMethod(result,"address",LongType.v(),context)
      //设置一个list，添加元素为非基本字段对应的deca类实例，用来获得方法的
      val unPrimField=new util.ArrayList[SootField]()
      var offSet:Long=0

      val (usedFields,usedMethods)=getFieldsAndMethodsUsed(sootClass,context)

      //先放基本类型吧，再放其他类型
      val primFields=new util.ArrayList[SootField]()
      val otherFields=new util.ArrayList[SootField]()
      for(field<-usedFields){
        if(field.getType.isInstanceOf[PrimType]){
          primFields.add(field)
        }else{
          otherFields.add(field)
        }
      }
      for(field<-primFields){
        val (getCall,setCall)=getMethod2Call(field.getType,context)
        addGetForPrim(result,field,result.getFieldByName("address"),offSet,getCall)
        addSetForPrim(result,field,result.getFieldByName("address"),offSet,setCall)
        offSet+=getTypeSize(field.getType)
      }
      for(field<-otherFields){
        val fieldDeca=create(field.getType,curOffset+offSet,originDecaMap,originTempMap,decaOriginMap,tempDecaMethodMap,context)

        if(fieldDeca!=null) {
          val nField = new SootField(field.getName, fieldDeca.getType)
          result.addField(nField)
          /**
            * 记得加怎么设置这个为decaClass 对象的初始地址设置
            * 我怎么觉得应该在最后添加呢，在init添加？
            */
          addSetGetUnprimField(result, nField, unPrimField, offSet, context)
          //这里也可以加一个方法，getField方法，就返回这个引用
          unPrimField.add(nField)
        }
      }
      //都搞完了，就加一个length方法吧
      addGetLength(result,unPrimField,offSet,context)

      /**
        * 对用到的方法进行转换
        */
      for(method<-usedMethods){
        //Modify
        if((!method.getName.endsWith("<clinit>"))&&method.hasActiveBody) {
          tempDecaMethodMap.put(method, createMethod(method, sootClass, result, originDecaMap, originTempMap, context))
        }else{
          val coName=covertName(method,originTempMap,result,context)
          tempDecaMethodMap.put(method,createEmptyMethod(coName,method.getParameterTypes,method.getReturnType,result))

        }
      }
    }else if(classType.isInstanceOf[ArrayType]){
      result=createArrayDeca(classType,context)
    }
    result
  }

  def createArrayDeca(classType:Type,context: Context):SootClass={
    var result:SootClass=null

    val arrType=classType.asInstanceOf[ArrayType]
    val baseType=arrType.getElementType
    if(baseType.isInstanceOf[PrimType]){

      val name=baseType.toString+"ArrayDeca"
      if(context.scene.getSootClassUnsafe(name)!=null){
        return context.sootClass(name)
      }
      result=new SootClass(name,Modifier.PUBLIC)
      result.setSuperclass(context.sootClass("java.lang.Object"))
      context.applicationClasses.add(result)

      addFieldAndSetMethod(result,"address",LongType.v(),context)
      addFieldAndSetMethod(result,"arrLength",LongType.v(),context)


      /**
        * 添加get（index）和set（index，value）
        */
      addGetSetForArrayType(result,baseType.asInstanceOf[PrimType],context)
      addGetLengthForArrayType(result,baseType.asInstanceOf[PrimType],context)

      //加一个init吧

      val init=new SootMethod("<init>",null,VoidType.v(),Modifier.PUBLIC)
      result.addMethod(init)
      val body=Jimple.v().newBody(init)
      init.setActiveBody(body)
      val units=body.getUnits
      val locals=body.getLocals

      val iden=Jimple.v().newLocal("iden",result.getType)
      locals.add(iden)
      units.add(Jimple.v().newIdentityStmt(iden,Jimple.v().newThisRef(result.getType)))

      units.add(Jimple.v().newReturnVoidStmt())
    }
    else if(baseType.isInstanceOf[RefType]){
      // TODO  element类型不是基本类型的数组类
    }
    result
  }






  /**
    *生成一个中间类，对原来类中的类型进行特化。
    * @param sootClass  原来的类
    * @param fieldInfoMap  类中字段泛型与实际类型的map
    * @param context
    * @return
    */
  def modifyFieldTypeOfSootClass(sootClass: SootClass,fieldInfoMap:mutable.HashMap[SootField,FieldInfo],originTempMap:util.HashMap[SootClass,SootClass],originTempMethodMap:util.HashMap[SootMethod,SootMethod],context: Context): SootClass ={

    if(context.scene.getSootClassUnsafe(sootClass.getName+"temp")!=null){
      return context.sootClass(sootClass.getName+"temp")
    }
    val tempClass=new SootClass(sootClass.getName+"temp",Modifier.PUBLIC)
    tempClass.setSuperclass(sootClass.getSuperclass)
    originTempMap.put(sootClass,tempClass)
    context.applicationClasses.add(tempClass)
    val modifyFieldMap=new mutable.HashMap[SootField,Type]()
    val typeMap=new util.HashMap[Type,Type]()
    typeMap.put(sootClass.getType,tempClass.getType)
    for(field<-sootClass.getFields){
      if(fieldInfoMap.contains(field)){
        val specificType=fieldInfoMap.get(field).get.specificClass.getType
        val isArr=fieldInfoMap.get(field).get.isArray
        val tempType=if(isArr){

          val typeName=specificType.toString
          if(typeName.equals("double")){
            DoubleType.v().makeArrayType()
          }else if(typeName.equals("long")){
            LongType.v().makeArrayType()
          }else if(typeName.equals("int")){
            IntType.v().makeArrayType()
          }else if(typeName.equals("float")){
            FloatType.v().makeArrayType()
          }else if(typeName.equals("char")){
            CharType.v().makeArrayType()
          }else if(typeName.equals("boolean")){
            BooleanType.v().makeArrayType()
          }else if(typeName.equals("short")){
            ShortType.v().makeArrayType()
          }else if(typeName.equals("byte")){
            ByteType.v().makeArrayType()
          }
          else{
            specificType.makeArrayType()
          }

        }else{
          val typeName=specificType.toString
          if(typeName.equals("double")){
            DoubleType.v()
          }else if(typeName.equals("long")){
            LongType.v()
          }else if(typeName.equals("int")){
            IntType.v()
          }else if(typeName.equals("float")){
            FloatType.v()
          }else if(typeName.equals("char")){
            CharType.v()
          }else if(typeName.equals("boolean")){
            BooleanType.v()
          }else if(typeName.equals("short")){
            ShortType.v()
          }else if(typeName.equals("byte")){
            ByteType.v()
          }else if(typeName.equals("double[]")){
            DoubleType.v().makeArrayType()
          }else if(typeName.equals("long[]")){
            LongType.v().makeArrayType()
          }else if(typeName.equals("int[]")){
            IntType.v().makeArrayType()
          }else if(typeName.equals("float[]")){
            FloatType.v().makeArrayType()
          }else if(typeName.equals("char[]")){
            CharType.v().makeArrayType()
          }else if(typeName.equals("boolean[]")){
            BooleanType.v().makeArrayType()
          }else if(typeName.equals("short[]")){
            ShortType.v().makeArrayType()
          }else if(typeName.equals("byte[]")){
            ByteType.v().makeArrayType()
          }else{
            specificType
          }
        }
        val tempField=new SootField(field.getName,tempType,field.getModifiers)
        tempClass.addField(tempField)
        modifyFieldMap.put(tempField, field.getType)

      }else{
        tempClass.addField(Utils.cloneSootField(field))
      }
    }
    for(kv<-modifyFieldMap){
      val tempField=kv._1
      val oldType=kv._2
      try {
        if (!tempField.getType.isInstanceOf[ArrayType] && (!oldType.asInstanceOf[RefType].getSootClass.getName.equals("java.lang.Object"))) {
          val tempFieldClass = modifyFieldTypeOfSootClass(tempField.getType.asInstanceOf[RefType].getSootClass, fieldInfoMap, originTempMap, originTempMethodMap, context)
          tempField.setType(tempFieldClass.getType)
          //此处对其他信息，比如方法中输入值，还有返回值，以及body中的local类型，还有invoke里面类型，以及
          typeMap.put(oldType, tempFieldClass.getType)
        }
      }catch {
        case e:Exception=>{
          val fm=fieldInfoMap
          println("************************************************************"+oldType.toString+"\t"+tempField.toString)
        }
      }
    }
    for(method<-sootClass.getMethods){
      originTempMethodMap.put(method,cloneMethod(method, sootClass, tempClass, typeMap,context))

    }

//    context.writeOutput(tempClass)
    tempClass
  }

  /**
    * 对临时类的类型转换
    * @return
    */
  def covertTempType(fieldType:Type,typeMap:util.HashMap[Type,Type]):Type={
    if(typeMap.isEmpty)
      fieldType

    if(typeMap.containsKey(fieldType)){
      typeMap.get(fieldType)
    }else{
      fieldType
    }

  }

  //克隆方法，并对方法中字段转换吧

  def cloneMethod(oldMethod:SootMethod, oldSootClass:SootClass, newSootClass:SootClass,typemap:util.HashMap[Type,Type],context: Context):SootMethod={

    if(newSootClass.getMethodUnsafe(oldMethod.getName,oldMethod.getParameterTypes.map(t=>covertTempType(t,typemap)),covertTempType(oldMethod.getReturnType,typemap))!=null){
      return newSootClass.getMethodUnsafe(oldMethod.getName,oldMethod.getParameterTypes.map(t=>covertTempType(t,typemap)),covertTempType(oldMethod.getReturnType,typemap))
    }
    val newMethod = new SootMethod(oldMethod.getName,oldMethod.getParameterTypes.map(t=>covertTempType(t,typemap)),covertTempType(oldMethod.getReturnType,typemap),
      oldMethod.getModifiers, oldMethod.getExceptions)
    if(!oldMethod.hasActiveBody){
      return newMethod
    }
    val localMethodBody = oldMethod.getActiveBody

    newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
    newMethod.setDeclaringClass(newSootClass)
    newSootClass.addMethod(newMethod)
    val newMethodBody = newMethod.retrieveActiveBody()
    /**
      * 设置对应类型
      */
    val pa=context.scene.getPointsToAnalysis
    val newLocals=newMethodBody.getLocals
    var flag=true
    var lastLocal:Local=null
    var curLocal:Local=null
    for(local<-oldMethod.getActiveBody.getLocals){
      if(!flag){
        curLocal=newLocals.getSuccOf(lastLocal)
      }else{
        flag=false
        curLocal=newLocals.getFirst
      }
      var ty=local.getType

      //      val pts=pa.reachingObjects(local).possibleTypes()
//      if(pts.size()==1){
//        ty=pts.toArray.apply(0).asInstanceOf[Type]
//        println()
//      }


      curLocal.setType(covertTempType(ty,typemap))
      lastLocal=curLocal
    }
    /**
      * 结束
      */

    for (unit <- newMethodBody.getUnits) {
      if (unit.isInstanceOf[JIdentityStmt]) {
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
          jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
        }else if(jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]){
          //这里改变量类型
          val parameterType=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getType
          val index=jIdentityStmt.getRightOp.asInstanceOf[ParameterRef].getIndex
          jIdentityStmt.setRightOp(Jimple.v().newParameterRef(covertTempType(parameterType,typemap),index))

        }
      }
      else if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]
          if( jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {

            val invokeName = jVirtualInvokeExpr.getMethodRef.name()
            val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
            val returnType=jVirtualInvokeExpr.getMethodRef.returnType()
            if(newSootClass.getMethodUnsafe(invokeName,invokeParameter.map(pt=>covertTempType(pt,typemap)),covertTempType(jVirtualInvokeExpr.getMethod.getReturnType,typemap))==null){
              cloneMethod(jVirtualInvokeExpr.getMethod,oldSootClass,newSootClass,typemap,context)
            }
            if(newSootClass.getMethodUnsafe(invokeName, invokeParameter.map(pt => covertTempType(pt, typemap)), covertTempType(jVirtualInvokeExpr.getMethod.getReturnType, typemap))!=null) {
              val newMethodRef = newSootClass.getMethodUnsafe(invokeName, invokeParameter.map(pt => covertTempType(pt, typemap)), covertTempType(jVirtualInvokeExpr.getMethod.getReturnType, typemap)).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }
          }
        } else if(jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]
          if( jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
            val invokeName = jVirtualInvokeExpr.getMethodRef.name()
            val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
            val returnType=jVirtualInvokeExpr.getMethodRef.returnType()
            if(newSootClass.getMethodUnsafe(invokeName,invokeParameter.map(pt=>covertTempType(pt,typemap)),covertTempType(jVirtualInvokeExpr.getMethod.getReturnType,typemap))==null){
              cloneMethod(jVirtualInvokeExpr.getMethod,oldSootClass,newSootClass,typemap,context)
            }
            val newMethodRef = newSootClass.getMethodUnsafe(invokeName,invokeParameter.map(pt=>covertTempType(pt,typemap)),covertTempType(jVirtualInvokeExpr.getMethod.getReturnType,typemap)).makeRef()

            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        } else if(jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]

          /**
            *
            */
          if(typemap.containsKey(jInstanceFieldRef.getFieldRef.declaringClass().getType)){
            val invokeName = jInstanceFieldRef.getFieldRef.name()
            val newFieldRef=typemap.get(jInstanceFieldRef.getFieldRef.declaringClass().getType).asInstanceOf[RefType].getSootClass
              .getFieldByName(invokeName).makeRef()
            jInstanceFieldRef.setFieldRef(newFieldRef)
          }

        } else if(jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          if(typemap.containsKey(jInstanceFieldRef.getFieldRef.declaringClass().getType)){
            val invokeName = jInstanceFieldRef.getFieldRef.name()
            val newFieldRef=typemap.get(jInstanceFieldRef.getFieldRef.declaringClass().getType).asInstanceOf[RefType].getSootClass
              .getFieldByName(invokeName).makeRef()
            jInstanceFieldRef.setFieldRef(newFieldRef)
          }
        }
        else if(jAssignStmt.getRightOp.isInstanceOf[JNewExpr]){
          val classType=jAssignStmt.getRightOp.asInstanceOf[JNewExpr].getType

          jAssignStmt.setRightOp(Jimple.v().newNewExpr(covertTempType(classType,typemap).asInstanceOf[RefType]))

        }
        else if(jAssignStmt.getRightOp.isInstanceOf[JCastExpr]){
          val castExp=jAssignStmt.getRightOp.asInstanceOf[JCastExpr]

          castExp.setCastType(covertTempType(castExp.getCastType,typemap))

        }
      } else if(unit.isInstanceOf[JInvokeStmt]){
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
        if(invokeMethodRef.declaringClass().getName.equals(oldSootClass.getName)){

          val invokeName=invokeMethodRef.name()
          val invokeParameter=invokeMethodRef.parameterTypes()
          val returnType=invokeMethodRef.returnType()
          if(newSootClass.getMethodUnsafe(invokeName,invokeParameter.map(t=>covertTempType(t,typemap)),covertTempType(returnType,typemap))==null){
            cloneMethod(jInvokeStmt.getInvokeExpr.getMethod,oldSootClass,newSootClass,typemap,context)
          }

          val newInvokeMethodRef = newSootClass.getMethodUnsafe(invokeName,invokeParameter.map(t=>covertTempType(t,typemap)),covertTempType(returnType,typemap)).makeRef()
          jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
        }
      }
    }

    newMethod

  }


  override def transform(context: Context):Unit={
    println("transform object to off-heap and transform the method")

  }


  def addGetLengthForArrayType(sootClass: SootClass,baseType:PrimType,context: Context): Unit ={

    val getLength=new SootMethod("getLength",null,LongType.v(),Modifier.PUBLIC)
    sootClass.addMethod(getLength)

    val baseSize=getTypeSize(baseType)
    val body=Jimple.v().newBody(getLength)
    getLength.setActiveBody(body)
    val locals=body.getLocals
    val units=body.getUnits

    val iden=Jimple.v().newLocal("iden",sootClass.getType)
    locals.add(iden)
    units.add(Jimple.v().newIdentityStmt(iden,Jimple.v().newThisRef(sootClass.getType)))

    val arrLength=Jimple.v().newLocal("arrLength",LongType.v())
    locals.add(arrLength)
    units.add(Jimple.v().newAssignStmt(arrLength,Jimple.v().newInstanceFieldRef(iden,sootClass.getFieldByName("arrLength").makeRef())))

    val len=Jimple.v().newLocal("len",LongType.v())
    locals.add(len)
    units.add(Jimple.v().newAssignStmt(len,Jimple.v().newMulExpr(arrLength,LongConstant.v(baseSize))))

    units.add(Jimple.v().newReturnStmt(len))


  }
  def addGetSetForArrayType(sootClass: SootClass,baseType:PrimType,context: Context): Unit ={
    val get=new SootMethod("get",Arrays.asList(IntType.v()),baseType,Modifier.PUBLIC)
    sootClass.addMethod(get)
    val baseSize=getTypeSize(baseType)
    val (getCall,setCall)=getMethod2Call(baseType,context)

    {
      val body = Jimple.v().newBody(get)
      get.setActiveBody(body)
      val locals = body.getLocals
      val units = body.getUnits

      val iden=Jimple.v().newLocal("iden",sootClass.getType)
      locals.add(iden)
      units.add(Jimple.v().newIdentityStmt(iden,Jimple.v().newThisRef(sootClass.getType)))

      val i0=Jimple.v().newLocal("p0",IntType.v())
      locals.add(i0)
      units.add(Jimple.v().newIdentityStmt(i0,Jimple.v().newParameterRef(IntType.v(),0)))

      val l0=Jimple.v().newLocal("l0",LongType.v())
      locals.add(l0)
      units.add(Jimple.v().newAssignStmt(l0,Jimple.v().newCastExpr(i0,LongType.v())))

      val multi=Jimple.v().newLocal("multi",LongType.v())
      locals.add(multi)
      units.add(Jimple.v().newAssignStmt(multi,Jimple.v().newMulExpr(l0,LongConstant.v(baseSize))))

      val address=Jimple.v().newLocal("address",LongType.v())
      locals.add(address)
      units.add(Jimple.v().newAssignStmt(address,Jimple.v().newInstanceFieldRef(iden,sootClass.getFieldByName("address").makeRef())))

      val sum=Jimple.v().newLocal("sum",LongType.v())
      locals.add(sum)
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(multi,address)))

      val result=Jimple.v().newLocal("result",baseType)
      locals.add(result)
      units.add(Jimple.v().newAssignStmt(result,Jimple.v().newStaticInvokeExpr(getCall.makeRef(),Arrays.asList(NullConstant.v(),sum))))
      units.add(Jimple.v().newReturnStmt(result))


    }
    val set=new SootMethod("set",Arrays.asList(IntType.v(),baseType),VoidType.v(),Modifier.PUBLIC)
    sootClass.addMethod(set)


    {
      val body = Jimple.v().newBody(set)
      set.setActiveBody(body)
      val locals = body.getLocals
      val units = body.getUnits

      val iden=Jimple.v().newLocal("iden",sootClass.getType)
      locals.add(iden)
      units.add(Jimple.v().newIdentityStmt(iden,Jimple.v().newThisRef(sootClass.getType)))

      val i0=Jimple.v().newLocal("p0",IntType.v())
      locals.add(i0)
      units.add(Jimple.v().newIdentityStmt(i0,Jimple.v().newParameterRef(IntType.v(),0)))

      val value=Jimple.v().newLocal("p1",baseType)
      locals.add(value)
      units.add(Jimple.v().newIdentityStmt(value,Jimple.v().newParameterRef(baseType,1)))

      val l0=Jimple.v().newLocal("l0",LongType.v())
      locals.add(l0)
      units.add(Jimple.v().newAssignStmt(l0,Jimple.v().newCastExpr(i0,LongType.v())))

      val multi=Jimple.v().newLocal("multi",LongType.v())
      locals.add(multi)
      units.add(Jimple.v().newAssignStmt(multi,Jimple.v().newMulExpr(l0,LongConstant.v(baseSize))))

      val address=Jimple.v().newLocal("address",LongType.v())
      locals.add(address)
      units.add(Jimple.v().newAssignStmt(address,Jimple.v().newInstanceFieldRef(iden,sootClass.getFieldByName("address").makeRef())))

      val sum=Jimple.v().newLocal("sum",LongType.v())
      locals.add(sum)
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(multi,address)))


      units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setCall.makeRef(),Arrays.asList(NullConstant.v(),sum,value))))

      units.add(Jimple.v().newReturnVoidStmt())

    }


  }
  def addGetLength(sootClass: SootClass,unPrimFields:util.ArrayList[SootField],offset:Long, context: Context): Unit ={
    val initAddress=new SootMethod("getLength",null,LongType.v(),Modifier.PUBLIC)
    sootClass.addMethod(initAddress)
    val body=Jimple.v().newBody(initAddress)
    initAddress.setActiveBody(body)
    val units=body.getUnits
    val locals=body.getLocals

    val iden0=Jimple.v().newLocal("iden0",sootClass.getType)
    locals.add(iden0)
    units.add(Jimple.v().newIdentityStmt(iden0,Jimple.v().newThisRef(sootClass.getType)))

    var index=0
    var tempLength=Jimple.v().newLocal("tempLength"+index,LongType.v())
    var tempSum=Jimple.v().newLocal("tempSum"+index,LongType.v())
    locals.add(tempSum)
    units.add(Jimple.v().newAssignStmt(tempSum,LongConstant.v(offset)))
    var sum=Jimple.v().newLocal("sum"+index,LongType.v())


    for(unPrimField<-unPrimFields){
      var tempLocal=Jimple.v().newLocal("tempLocal"+index,unPrimField.getType())

      locals.add(tempLocal)
      locals.add(tempLength)
      locals.add(sum)

      units.add(Jimple.v().newAssignStmt(tempLocal,Jimple.v().newInstanceFieldRef(iden0,unPrimField.makeRef())))
      if(unPrimField.getType.asInstanceOf[RefType].getSootClass.getMethodByNameUnsafe("getLength")!=null)
        units.add(Jimple.v().newAssignStmt(tempLength,Jimple.v().newVirtualInvokeExpr(tempLocal,unPrimField.getType.asInstanceOf[RefType].getSootClass.getMethodByName("getLength").makeRef())))
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(tempLength,tempSum)))

      index+=1
      tempSum=sum
      tempLength=Jimple.v().newLocal("tempLength"+index,LongType.v())
      sum=Jimple.v().newLocal("sum"+index,LongType.v())



    }

    units.add(Jimple.v().newReturnStmt(tempSum))

  }

  def addSetGetUnprimField(sootClass: SootClass,sootField:SootField,unPrimFields:util.ArrayList[SootField],offset:Long, context: Context): Unit ={

    //直接加get字段方法，返回这个deca字段就行
    {
      val get=new SootMethod("get"+sootField.getName,null,sootField.getType,Modifier.PUBLIC)
      sootClass.addMethod(get)
      val getBody=Jimple.v().newBody(get)
      get.setActiveBody(getBody)
      val getUnits=getBody.getUnits
      val getLocals=getBody.getLocals
      val iden=Jimple.v().newLocal("iden0",sootClass.getType)
      getLocals.add(iden)
      getUnits.add(Jimple.v().newIdentityStmt(iden,Jimple.v().newThisRef(sootClass.getType)))
      val r=Jimple.v().newLocal("re",sootField.getType)
      getLocals.add(r)
      getUnits.add(Jimple.v().newAssignStmt(r,Jimple.v().newInstanceFieldRef(iden,sootField.makeRef())))
      getUnits.add(Jimple.v().newReturnStmt(r))
    }

    val initAddress=new SootMethod("set"+sootField.getName,null,VoidType.v(),Modifier.PUBLIC)
    sootClass.addMethod(initAddress)
    val body=Jimple.v().newBody(initAddress)
    initAddress.setActiveBody(body)
    val units=body.getUnits
    val locals=body.getLocals

    val iden0=Jimple.v().newLocal("iden0",sootClass.getType)
    locals.add(iden0)
    units.add(Jimple.v().newIdentityStmt(iden0,Jimple.v().newThisRef(sootClass.getType)))

    //初始值
    val add=Jimple.v().newLocal("add",LongType.v())
    locals.add(add)
    units.add(Jimple.v().newAssignStmt(add,Jimple.v().newInstanceFieldRef(iden0,sootClass.getFieldByName("address").makeRef())))

    var index=0
    var tempLength=Jimple.v().newLocal("tempLength"+index,LongType.v())
    var tempSum=Jimple.v().newLocal("tempSum"+index,LongType.v())
    locals.add(tempSum)
    units.add(Jimple.v().newAssignStmt(tempSum,Jimple.v().newAddExpr(add,LongConstant.v(offset))))
    var sum=Jimple.v().newLocal("sum"+index,LongType.v())


    for(unPrimField<-unPrimFields){
      var tempLocal=Jimple.v().newLocal("tempLocal"+index,unPrimField.getType())

      locals.add(tempLocal)
      locals.add(tempLength)
      locals.add(sum)

      units.add(Jimple.v().newAssignStmt(tempLocal,Jimple.v().newInstanceFieldRef(iden0,unPrimField.makeRef())))
      if(unPrimField.getType.asInstanceOf[RefType].getSootClass.getMethodByNameUnsafe("getLength")!=null)
        units.add(Jimple.v().newAssignStmt(tempLength,Jimple.v().newVirtualInvokeExpr(tempLocal,unPrimField.getType.asInstanceOf[RefType].getSootClass.getMethodByName("getLength").makeRef())))
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(tempLength,tempSum)))

      index+=1
      tempSum=sum
      tempLength=Jimple.v().newLocal("tempLength"+index,LongType.v())
      sum=Jimple.v().newLocal("sum"+index,LongType.v())



    }
    val thisField=Jimple.v().newLocal("thisField",sootField.getType)
    locals.add(thisField)
    units.add(Jimple.v().newAssignStmt(thisField,Jimple.v().newInstanceFieldRef(iden0,sootField.makeRef())))
    units.add(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(thisField,sootField.getType.asInstanceOf[RefType].getSootClass.getMethodByName("setaddress").makeRef(),tempSum)))

    units.add(Jimple.v().newReturnVoidStmt())

  }

  //用来添加addressfield以及添加设置地址的方法
  def addFieldAndSetMethod(sootClass: SootClass,name:String,ty:Type,context: Context): Unit ={
    val address=new SootField(name,ty,Modifier.PUBLIC)
    sootClass.addField(address)

    val setAddress=new SootMethod("set"+name,Arrays.asList(ty),VoidType.v(),Modifier.PUBLIC)
    sootClass.addMethod(setAddress)
    val body=Jimple.v().newBody(setAddress)
    setAddress.setActiveBody(body)
    val units=body.getUnits
    val locals=body.getLocals

    val iden0=Jimple.v().newLocal("iden0",sootClass.getType)
    locals.add(iden0)
    units.add(Jimple.v().newIdentityStmt(iden0,Jimple.v().newThisRef(sootClass.getType)))

    val p0=Jimple.v().newLocal("p0",ty)
    locals.add(p0)
    units.add(Jimple.v().newIdentityStmt(p0,Jimple.v().newParameterRef(ty,0)))

    units.add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(iden0,address.makeRef()),p0))

    units.add(Jimple.v().newReturnVoidStmt())
  }







  def getTypeSize(primType: Type): Long ={
    val baseLegth:Long=primType match {
      case intType:IntType=>4
      case longType:LongType=>8
      case floatType:FloatType=>8
      case doubleType:DoubleType=>8
      case byteType:ByteType=>1
      case booleanType:BooleanType=>1
      case _=>2
    }
    baseLegth
  }

  def getMethod2Call(fieldType: Type,context: Context):(SootMethod,SootMethod)={
    val platForm = context.sootClass("cn.edu.hust.grid.soot.optimize.Platform")
    //setCall
    val putLong = platForm.getMethodByName("putLong")
    val putInt = platForm.getMethodByName("putInt")
    val putDouble = platForm.getMethodByName("putDouble")
    val putShort=platForm.getMethodByName("putShort")
    val putBoolean=platForm.getMethodByName("putBoolean")
    val putFloat=platForm.getMethodByName("putFloat")
    val putByte=platForm.getMethodByName("putByte")
    //get call
    val getLong = platForm.getMethodByName("getLong")
    val getInt = platForm.getMethodByName("getInt")
    val getDouble = platForm.getMethodByName("getDouble")
    val getShort=platForm.getMethodByName("getShort")
    val getBoolean=platForm.getMethodByName("getBoolean")
    val getFloat=platForm.getMethodByName("getFloat")
    val getByte=platForm.getMethodByName("getByte")
    val getCall=fieldType match {
      case intType:IntType=>getInt
      case longType:LongType=>getLong
      case floatType:FloatType=>getFloat
      case doubleType:DoubleType=>getDouble
      case byteType:ByteType=>getByte
      case booleanType:BooleanType=>getBoolean
      case _=>getShort
    }

    val setCall=fieldType match {
      case intType:IntType=>putInt
      case longType:LongType=>putLong
      case floatType:FloatType=>putFloat
      case doubleType:DoubleType=>putDouble
      case byteType:ByteType=>putByte
      case booleanType:BooleanType=>putBoolean
      case _=>putShort
    }
    (getCall,setCall)
  }


  /**
    * 为类添加一个get方法，这里有一个问题，就是说，这个方法的返回值类型，我写的是field类型，但是如果他不是一个基本类型
    * 比如是一个引用类型，但是这里我不拆解。如果是一个Array[]类型，我该返回什么呢？
    * 所以这只是对一个基本类型的添加get方法，而对于Array[]我会加索引
    * @param facadeClass  转化过的类
    * @param field        解析的字段
    * @param addressField 堆外起始地址，是转化类之后一个字段
    * @param curOffset    当前偏移
    * @param getCall      这是一个取值方法，对应类型字段
    */
  def  addGetForPrim(facadeClass: SootClass,field:SootField,addressField:SootField,curOffset:Long,getCall:SootMethod):Unit={

    val methodGet = new SootMethod("get" + field.getName, null, field.getType, Modifier.PUBLIC)
    if(facadeClass.getMethodByNameUnsafe(methodGet.getName)!=null)
      return
    facadeClass.addMethod(methodGet)

    val getBody = Jimple.v().newBody(methodGet)
    methodGet.setActiveBody(getBody)
    val getUnits = getBody.getUnits

    val r0 = Jimple.v().newLocal("r0", facadeClass.getType)
    getBody.getLocals.add(r0)
    getUnits.add(Jimple.v().newIdentityStmt(r0, Jimple.v().newThisRef(facadeClass.getType)))


    // r1=addressField
    val r1 = Jimple.v().newLocal("r1", LongType.v())
    getBody.getLocals.add(r1)
    getUnits.add(Jimple.v().newAssignStmt(r1, Jimple.v().newInstanceFieldRef(r0, addressField.makeRef())))

    //r2=r1+ curoffset
    // 注意此处是否写入常数
    val r2 = Jimple.v().newLocal("r2", LongType.v())
    getBody.getLocals.add(r2)
    getUnits.add(Jimple.v().newAssignStmt(r2, Jimple.v().newAddExpr(r1, LongConstant.v(curOffset))))


    // r3=get(null,r2)
    val r3 = Jimple.v().newLocal("r3", field.getType)
    getBody.getLocals.add(r3)
    getUnits.add(Jimple.v().newAssignStmt(r3, Jimple.v().newStaticInvokeExpr(getCall.makeRef(),Arrays.asList(NullConstant.v(),r2))))

    //return r3
    getUnits.add(Jimple.v().newReturnStmt(r3))

  }

  def addSetForPrim(facadeClass:SootClass,field:SootField,addressField:SootField,curOffset:Long,setCall:SootMethod): Unit ={
    val methodSet = new SootMethod("set" + field.getName, Arrays.asList(field.getType), VoidType.v(), Modifier.PUBLIC)
    if(facadeClass.getMethodByNameUnsafe(methodSet.getName)!=null)
      return
    facadeClass.addMethod(methodSet)

    val setBody = Jimple.v().newBody(methodSet)
    methodSet.setActiveBody(setBody)
    val setUnits = setBody.getUnits


    val r0 = Jimple.v().newLocal("r0", facadeClass.getType)
    setBody.getLocals.add(r0)
    setUnits.add(Jimple.v().newIdentityStmt(r0, Jimple.v().newThisRef(facadeClass.getType)))

    // p0:= @parameter:0
    val p0=Jimple.v().newLocal("p0",field.getType)
    setBody.getLocals.add(p0)
    setUnits.add(Jimple.v().newIdentityStmt(p0,Jimple.v().newParameterRef(field.getType,0)))

    // r1=addressField
    val r1 = Jimple.v().newLocal("r1", LongType.v())
    setBody.getLocals.add(r1)
    setUnits.add(Jimple.v().newAssignStmt(r1, Jimple.v().newInstanceFieldRef(r0, addressField.makeRef())))

    //r2=r1+ curoffset
    // 注意此处是否写入常数
    val r2 = Jimple.v().newLocal("r2", LongType.v())
    setBody.getLocals.add(r2)
    setUnits.add(Jimple.v().newAssignStmt(r2, Jimple.v().newAddExpr(r1, LongConstant.v(curOffset))))


    setUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setCall.makeRef(),Arrays.asList(NullConstant.v(),r2,p0))))

    //return
    setUnits.add(Jimple.v().newReturnVoidStmt())
  }
  /**
    * 移除用不到的local
    */
  def removeUnuseLocals(method:SootMethod): Unit ={
    val body=method.getActiveBody

    val usedLocals=new mutable.HashSet[JimpleLocal]()
    for(unit<-body.getUnits){
      if(unit.isInstanceOf[JAssignStmt]&&unit.asInstanceOf[JAssignStmt].getLeftOp.isInstanceOf[JimpleLocal]){
        usedLocals.add(unit.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal])

      }else if(unit.isInstanceOf[JIdentityStmt]){
        usedLocals.add(unit.asInstanceOf[JIdentityStmt].getLeftOp.asInstanceOf[JimpleLocal])
      }
    }
    val locals=body.getLocals
    locals.clear()
    locals.addAll(usedLocals)

  }
}