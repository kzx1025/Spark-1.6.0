package cn.edu.hust.grid.soot.optimize

import java.util
import java.util.{ArrayList, Arrays}

import cn.edu.hust.grid.soot.Utils

import scala.collection.JavaConversions._
import soot.jimple._
import soot._
import soot.jimple.internal._

import scala.collection.mutable
import scala.Unit

/** 转换成deca的类*/
object Convertor extends Transformer {

  override def transform(context: Context):Unit={
    println("transform object to off-heap and transform the method")

  }



  def convert(sc: SootClass,context: Context){
//    针对densevector
    val newDataField=new SootField("ndata",ArrayType.v(DoubleType.v(),1))
    sc.addField(newDataField)

    val allPrimFields=new util.ArrayList[SootField]()
    val allArrayTypeFields=new util.ArrayList[SootField]()
    val allRefTypeFields=new util.ArrayList[SootField]()
    val decaClass=new SootClass(sc.getName+"Deca",Modifier.PUBLIC)
    // add the extend class
    decaClass.setSuperclass(context.sootClass("java.lang.Object"))
    //因为我想输出这个类
    context.applicationClasses.add(decaClass)

    val addressField = new SootField("address", LongType.v(),Modifier.PUBLIC)
    decaClass.addField(addressField)
    var curOffset=0L


    val platForm = context.sootClass("cn.edu.hust.grid.soot.Platform")

    //memory operation
    val freeMemory=platForm.getMethodByName("freeMemory")
    val allcotaMemory=platForm.getMethod("long allocateMemory(long)")
    val setMemory=platForm.getMethod("void setMemory(long,byte,long)")


    val allFields:util.Queue[SootField] = new util.LinkedList()
    sc.getFields.map(field=>allFields.add(field))
    var parrentClass = sc.getSuperclass
    while (!parrentClass.getName.equals("java.lang.Object")) {
      parrentClass.getFields.map(field => allFields.add(field))
      parrentClass = parrentClass.getSuperclass
    }




    while (allFields.size()!=0){
      val field=allFields.poll()
      if(field.getType.isInstanceOf[PrimType]){
        allPrimFields.add(field)
      }else if(field.getType.isInstanceOf[RefType]){

        allRefTypeFields.add(field)
      }else{
        allArrayTypeFields.add(field)
      }
    }

    for(field<-allPrimFields){
      processPrimTypeField(field,decaClass,curOffset,addressField,context)

      //偏移量增加
      curOffset+=getTypeSize(field.getType)


    }




    /** 此处引用类型，需要加一个类的初始化，还有就是类的返回地址了
      * 加的是arrayType的字段，和其基本类型的长度*/
    val atFieldList=new util.ArrayList[(SootField,Long)]()
    for (field<-allRefTypeFields){

      curOffset+=processRefTypeField(field,decaClass,curOffset,addressField,context,atFieldList)
    }



    for(field<-allArrayTypeFields){
      processArrayTypeField(field,decaClass,curOffset,addressField,context,atFieldList)
    }

    convertMethod(sc,decaClass)
   // addInitMethod(decaClass,allcotaMemory,setMemory,context,addressField,curOffset,atFieldList)
  }


  /**
    * 此处设置三个方法，分别处理基本类型字段，引用类型字段，和数组类型字段
    */
  def processPrimTypeField(field:SootField,decaClass:SootClass,curOffset:Long,addressField:SootField,context: Context): Unit ={
    val(getCall,setCall)=getMethod2Call(field.getType,context)

    addGetForPrim(decaClass,field,addressField,curOffset,getCall)
    addSetForPrim(decaClass,field,addressField,curOffset,setCall)

  }

  def processArrayTypeField(field:SootField,decaClass:SootClass,curOffset:Long,addressField:SootField,context: Context, atFieldList: util.ArrayList[(SootField,Long)]): Unit ={
    /**
      * 这里我只考虑单层array的情形，多层嵌套我不管，一个array里面的baseType，如果是引用类，那么这个引用类里面没有ArrayType
      */
    val arratField=field.getType.asInstanceOf[ArrayType]
    val baseType=arratField.baseType

    val fieldLength=new SootField(field.getName+"Length",LongType.v(),Modifier.PUBLIC)
    decaClass.addField(fieldLength)
    if(baseType.isInstanceOf[RefType]) {
      /**base是引用类怎么处理*/
      val (baseTypeLength, fieldInfos) = getBaseClassInfo(baseType.asInstanceOf[RefType].getSootClass)

      for(info<-fieldInfos){
        val fieldName=info._1
        val inOffset=info._2
        val fType=info._3

        val (getCall,setCall)=getMethod2Call(fType,context)
        addGetMethodForArrTypeRefBase(decaClass,curOffset,atFieldList,fieldName,fType,inOffset,getCall,addressField)
        addSetMethodForArrTypeRefBase(decaClass,curOffset,atFieldList,fieldName,fType,inOffset,setCall,addressField)
      }


      atFieldList.add((fieldLength,baseTypeLength))



    }else if(baseType.isInstanceOf[PrimType]){
      /** 基本类型怎么处理*/
      val baseLegth=getTypeSize(baseType)


      val (getCall,setCall)=getMethod2Call(baseType,context)

      /**
        * 添加get,set方法，要有一个索引
        */
      addGetMethodForArrTypePrimBase(decaClass,curOffset,atFieldList,field,getCall,addressField)
      addSetMethodForArrTypePrimBase(decaClass,curOffset,atFieldList,field,setCall,addressField)
      atFieldList.add((fieldLength,baseLegth))

    }else{
      //数组套数组，这种不考虑
    }
  }

  def processRefTypeField(field:SootField,decaClass:SootClass,curOffset:Long,addressField:SootField,context: Context, atFieldList: util.ArrayList[(SootField,Long)]): Long ={

    /**如何处理引用类型，首先是写一个引用类型的初始化类，比如 get返回第一个字段的偏移量
      * 而set则是转化所有init方法，对字段赋值操作转换为一些put，get操作
     */

    var length:Long=0
    val getFieldAddress=new SootMethod("get"+field.getName,null,LongType.v(),Modifier.PUBLIC)
    decaClass.addMethod(getFieldAddress)
    val body=Jimple.v().newBody(getFieldAddress)
    getFieldAddress.setActiveBody(body)
    val units=body.getUnits
    val locals=body.getLocals

    {

      val r0 = Jimple.v().newLocal("r0", decaClass.getType)
      locals.add(r0)
      units.add(Jimple.v().newIdentityStmt(r0, Jimple.v().newThisRef(decaClass.getType)))

      // r1=addressField
      val r1 = Jimple.v().newLocal("r1", LongType.v())
      locals.add(r1)
      units.add(Jimple.v().newAssignStmt(r1, Jimple.v().newInstanceFieldRef(r0, addressField.makeRef())))

      //r2=r1+ curoffset
      // 注意此处是否写入常数
      val r2 = Jimple.v().newLocal("r2", LongType.v())
      body.getLocals.add(r2)
      units.add(Jimple.v().newAssignStmt(r2, Jimple.v().newAddExpr(r1, LongConstant.v(curOffset))))

      units.add(Jimple.v().newReturnStmt(r2))
    }

    for(sonField<-field.getType.asInstanceOf[RefType].getSootClass.getFields){
      if(sonField.getType.isInstanceOf[PrimType]){
        processPrimTypeField(sonField,decaClass,curOffset+length,addressField,context)
        length+=getTypeSize(sonField.getType)
      }else if(sonField.getType.isInstanceOf[RefType]){
        length+=processRefTypeField(sonField,decaClass,curOffset+length,addressField,context,atFieldList)
      }else{
        processArrayTypeField(sonField,decaClass,curOffset+length,addressField,context,atFieldList)
      }
    }

    /**
      * 这里加set方法,为所有类型都添加一个吧
      */

    val fieldSootClass=field.getType.asInstanceOf[RefType].getSootClass
    for(method<-fieldSootClass.getMethods){
      if(method.getName.equals("<init>")){

        val initMethod=new SootMethod("set"+field.getName,method.getParameterTypes,method.getReturnType,method.getModifiers)
        decaClass.addMethod(initMethod)
        val initBody=Jimple.v().newBody(initMethod)
        initMethod.setActiveBody(initBody)


        val paraMeterNum=method.getParameterCount

        //方法体不知道怎么转换，先写个空的吧
        {
          val initLocals=initBody.getLocals
          val initUnits=initBody.getUnits
          val r0 = Jimple.v().newLocal("r0", decaClass.getType)
          initLocals.add(r0)
          initUnits.add(Jimple.v().newIdentityStmt(r0, Jimple.v().newThisRef(decaClass.getType)))


          for(i<- 0 until paraMeterNum){
            val parameter=Jimple.v().newLocal("pa"+i,method.getParameterType(i))
            initLocals.add(parameter)
            initUnits.add(Jimple.v().newIdentityStmt(parameter,Jimple.v().newParameterRef(method.getParameterType(i),i)))
          }

          initUnits.add(Jimple.v().newReturnVoidStmt())
        }

      }
    }



    length
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
    val platForm = context.sootClass("cn.edu.hust.grid.soot.Platform")
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

  /**这里只考虑class里面都是基本类型*/
  def getBaseClassInfo(baseClass:SootClass):(Long,util.ArrayList[(String,Long,Type)])={

    val fields=baseClass.getFields
    var curOffset=0L
    val list=new util.ArrayList[(String,Long,Type)]
    for(field<-fields){
      list.add((field.getName,curOffset,field.getType))

      curOffset+=getTypeSize(field.getType)

    }
    (curOffset,list)
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
    *
    * @param decaClass
    * @param curOffset   静态的偏移量
    * @param unfixedFieldList   动态数组的偏移量
    * @param field          这个是arrayType那个
    * @param getCall    get方法
    * @param addressField   全局空间的初始地址
    */

  def addGetMethodForArrTypePrimBase(decaClass:SootClass, curOffset:Long, unfixedFieldList: util.ArrayList[(SootField,Long)], field:SootField, getCall:SootMethod, addressField:SootField): Unit ={

    val primType=field.getType.asInstanceOf[ArrayType].baseType
    val primSize=getTypeSize(primType)


    val methodGet=new SootMethod("get"+field.getName,Arrays.asList(LongType.v()),primType,Modifier.PUBLIC)
    decaClass.addMethod(methodGet)
    val getBody=Jimple.v().newBody(methodGet)
    methodGet.setActiveBody(getBody)
    val units=getBody.getUnits
    val locals=getBody.getLocals


    val r0=Jimple.v().newLocal("r0",decaClass.getType)
    locals.add(r0)
    units.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(decaClass.getType)))


    //index=parameter(0)
    val i0=Jimple.v().newLocal("i0",LongType.v())
    locals.add(i0)
    units.add(Jimple.v().newIdentityStmt(i0,Jimple.v().newParameterRef(LongType.v(),0)))

    val l1=Jimple.v().newLocal("l1",addressField.getType)
    locals.add(l1)
    units.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))


    var index=0
    //设置一些变量
    var temp=Jimple.v().newLocal("temp"+index,LongType.v())
    var tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())
    var tempSum=Jimple.v().newLocal("tempSum"+index,LongType.v())
    locals.add(tempSum)
    units.add(Jimple.v().newAssignStmt(tempSum,LongConstant.v(0L)))

    for(arrLengthAndBaseLength<-unfixedFieldList){
      locals.add(temp)
      locals.add(tempBase)
      val arrLengthField=arrLengthAndBaseLength._1
      val baseLength=arrLengthAndBaseLength._2
      units.add(Jimple.v().newAssignStmt(temp,Jimple.v().newInstanceFieldRef(r0,arrLengthField.makeRef())))

      units.add(Jimple.v().newAssignStmt(tempBase,Jimple.v().newMulExpr(temp,LongConstant.v(baseLength))))

      val sum=Jimple.v().newLocal("sum"+index,LongType.v())
      locals.add(sum)
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(tempSum,tempBase)))

      index+=1

      temp=Jimple.v().newLocal("temp"+index,LongType.v())
      tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())

      tempSum=sum


    }
    val resultSum=locals.getLast

    //数组内的偏移量

    //强制类型转换
//    val cast2Long=Jimple.v().newLocal("cast2Long",LongType.v())
//    locals.add(cast2Long)
//    units.add(Jimple.v().newAssignStmt(cast2Long,Jimple.v().newCastExpr(i0,LongType.v())))


    val inArrOffset=Jimple.v().newLocal("inArrOffset",LongType.v())
    locals.add(inArrOffset)
    units.add(Jimple.v().newAssignStmt(inArrOffset,Jimple.v().newMulExpr(i0,LongConstant.v(primSize))))

    val t1=Jimple.v().newLocal("t1",LongType.v())
    locals.add(t1)
    units.add(Jimple.v().newAssignStmt(t1,Jimple.v().newAddExpr(l1,resultSum)))

    val realoffset=Jimple.v().newLocal("realOffset",LongType.v())
    locals.add(realoffset)
    units.add(Jimple.v().newAssignStmt(realoffset,Jimple.v().newAddExpr(t1,inArrOffset)))

    //加上静态的
    val lastOffset=Jimple.v().newLocal("lastOffset",LongType.v())
    locals.add(lastOffset)
    units.add(Jimple.v().newAssignStmt(lastOffset,Jimple.v().newAddExpr(realoffset,LongConstant.v(curOffset))))

    val result=Jimple.v().newLocal("reslut",primType)
    locals.add(result)
    units.add(Jimple.v().newAssignStmt(result,Jimple.v().newStaticInvokeExpr(getCall.makeRef(),Arrays.asList(NullConstant.v(),lastOffset))))

    units.add(Jimple.v().newReturnStmt(result))

  }

  def addSetMethodForArrTypePrimBase(decaClass:SootClass, curOffset:Long, unfixedFieldList:util.ArrayList[(SootField,Long)], field:SootField, setCall:SootMethod, addressField:SootField): Unit ={

    val primType=field.getType.asInstanceOf[ArrayType].baseType
    val primSize=getTypeSize(primType)

    val methodSet=new SootMethod("set"+field.getName,Arrays.asList(LongType.v(),primType),VoidType.v(),Modifier.PUBLIC)
    decaClass.addMethod(methodSet)
    val setBody=Jimple.v().newBody(methodSet)
    methodSet.setActiveBody(setBody)
    val units=setBody.getUnits
    val locals=setBody.getLocals


    val r0=Jimple.v().newLocal("r0",decaClass.getType)
    locals.add(r0)
    units.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(decaClass.getType)))


    //index=parameter(0)
    val i0=Jimple.v().newLocal("i0",LongType.v())
    locals.add(i0)
    units.add(Jimple.v().newIdentityStmt(i0,Jimple.v().newParameterRef(LongType.v(),0)))

    //value=parameter(1)
    val value=Jimple.v().newLocal("value",primType)
    locals.add(value)
    units.add(Jimple.v().newIdentityStmt(value,Jimple.v().newParameterRef(primType,1)))

    val l1=Jimple.v().newLocal("l1",addressField.getType)
    locals.add(l1)
    units.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))


    var index=0
    //设置一些变量
    var temp=Jimple.v().newLocal("temp"+index,LongType.v())
    var tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())
    var tempSum=Jimple.v().newLocal("tempSum"+index,LongType.v())
    locals.add(tempSum)
    units.add(Jimple.v().newAssignStmt(tempSum,LongConstant.v(0L)))

    for(arrLengthAndBaseLength<-unfixedFieldList){
      locals.add(temp)
      locals.add(tempBase)
      val arrLengthField=arrLengthAndBaseLength._1
      val baseLength=arrLengthAndBaseLength._2
      units.add(Jimple.v().newAssignStmt(temp,Jimple.v().newInstanceFieldRef(r0,arrLengthField.makeRef())))

      units.add(Jimple.v().newAssignStmt(tempBase,Jimple.v().newMulExpr(temp,LongConstant.v(baseLength))))

      val sum=Jimple.v().newLocal("sum"+index,LongType.v())
      locals.add(sum)
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(tempSum,tempBase)))

      index+=1

      temp=Jimple.v().newLocal("temp"+index,LongType.v())
      tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())

      tempSum=sum


    }
    val resultSum=locals.getLast

    //数组内的偏移量

    //强制类型转换
//    val cast2Long=Jimple.v().newLocal("cast2Long",LongType.v())
//    locals.add(cast2Long)
//    units.add(Jimple.v().newAssignStmt(cast2Long,Jimple.v().newCastExpr(i0,LongType.v())))

    val inArrOffset=Jimple.v().newLocal("inArrOffset",LongType.v())
    locals.add(inArrOffset)
    units.add(Jimple.v().newAssignStmt(inArrOffset,Jimple.v().newMulExpr(i0,LongConstant.v(primSize))))

    val t1=Jimple.v().newLocal("t1",LongType.v())
    locals.add(t1)
    units.add(Jimple.v().newAssignStmt(t1,Jimple.v().newAddExpr(l1,resultSum)))

    val realoffset=Jimple.v().newLocal("realOffset",LongType.v())
    locals.add(realoffset)
    units.add(Jimple.v().newAssignStmt(realoffset,Jimple.v().newAddExpr(t1,inArrOffset)))

    //加上静态的
    val lastOffset=Jimple.v().newLocal("lastOffset",LongType.v())
    locals.add(lastOffset)
    units.add(Jimple.v().newAssignStmt(lastOffset,Jimple.v().newAddExpr(realoffset,LongConstant.v(curOffset))))
//
//    val result=Jimple.v().newLocal("reslut",primType)
//    locals.add(result)
//    units.add(Jimple.v().newAssignStmt(result,Jimple.v().newStaticInvokeExpr(setCall.makeRef(),Arrays.asList(NullConstant.v(),lastOffset,value))))
//
//    units.add(Jimple.v().newReturnStmt(result))
    units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setCall.makeRef(),Arrays.asList(NullConstant.v(),lastOffset,value))))
    units.add(Jimple.v().newReturnVoidStmt())

  }


  /**
    *
    * @param decaClass
    * @param curOffset    静态偏移量
    * @param unfixedFieldList   这个是数组类型集合，要加起来前面的计算偏移量用
    * @param fieldName    类内字段名
    * @param fieldType     类内字段类型
    * @param inOffset     类内偏移
    * @param getCall     调用方法
    * @param addressField   这个是全局的初始地址
    */

  def addGetMethodForArrTypeRefBase(decaClass:SootClass, curOffset:Long, unfixedFieldList:util.ArrayList[(SootField,Long)], fieldName:String, fieldType:Type, inOffset:Long, getCall:SootMethod, addressField:SootField): Unit ={

    val primSize=getTypeSize(fieldType)

    val methodGet=new SootMethod("get"+fieldName,Arrays.asList(LongType.v()),fieldType,Modifier.PUBLIC)
    decaClass.addMethod(methodGet)
    val getBody=Jimple.v().newBody(methodGet)
    methodGet.setActiveBody(getBody)
    val units=getBody.getUnits
    val locals=getBody.getLocals


    val r0=Jimple.v().newLocal("r0",decaClass.getType)
    locals.add(r0)
    units.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(decaClass.getType)))


    //index=parameter(0)
    val i0=Jimple.v().newLocal("i0",LongType.v())
    locals.add(i0)
    units.add(Jimple.v().newIdentityStmt(i0,Jimple.v().newParameterRef(LongType.v(),0)))

    val l1=Jimple.v().newLocal("l1",addressField.getType)
    locals.add(l1)
    units.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))


    var index=0
    //设置一些变量
    var temp=Jimple.v().newLocal("temp"+index,LongType.v())
    var tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())
    var tempSum=Jimple.v().newLocal("tempSum"+index,LongType.v())
    locals.add(tempSum)
    units.add(Jimple.v().newAssignStmt(tempSum,LongConstant.v(0L)))

    for(arrLengthAndBaseLength<-unfixedFieldList){
      locals.add(temp)
      locals.add(tempBase)
      val arrLengthField=arrLengthAndBaseLength._1
      val baseLength=arrLengthAndBaseLength._2
      units.add(Jimple.v().newAssignStmt(temp,Jimple.v().newInstanceFieldRef(r0,arrLengthField.makeRef())))

      units.add(Jimple.v().newAssignStmt(tempBase,Jimple.v().newMulExpr(temp,LongConstant.v(baseLength))))

      val sum=Jimple.v().newLocal("sum"+index,LongType.v())
      locals.add(sum)
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(tempSum,tempBase)))

      index+=1

      temp=Jimple.v().newLocal("temp"+index,LongType.v())
      tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())

      tempSum=sum


    }
    val resultSum=locals.getLast

    //数组内的偏移量

    //强制类型转换
//    val cast2Long=Jimple.v().newLocal("cast2Long",LongType.v())
//    locals.add(cast2Long)
//    units.add(Jimple.v().newAssignStmt(cast2Long,Jimple.v().newCastExpr(i0,LongType.v())))


    val inArrOffset=Jimple.v().newLocal("inArrOffset",LongType.v())
    locals.add(inArrOffset)
    units.add(Jimple.v().newAssignStmt(inArrOffset,Jimple.v().newMulExpr(i0,LongConstant.v(primSize))))

    val t1=Jimple.v().newLocal("t1",LongType.v())
    locals.add(t1)
    units.add(Jimple.v().newAssignStmt(t1,Jimple.v().newAddExpr(l1,resultSum)))

    val realoffset=Jimple.v().newLocal("realOffset",LongType.v())
    locals.add(realoffset)
    units.add(Jimple.v().newAssignStmt(realoffset,Jimple.v().newAddExpr(t1,inArrOffset)))

    //这里加上类之内的偏移
    val innerOffset=Jimple.v().newLocal("innerOffset",LongType.v())
    locals.add(innerOffset)
    units.add(Jimple.v().newAssignStmt(innerOffset,Jimple.v().newAddExpr(realoffset,LongConstant.v(inOffset))))

    //加上静态的
    val lastOffset=Jimple.v().newLocal("lastOffset",LongType.v())
    locals.add(lastOffset)
    units.add(Jimple.v().newAssignStmt(lastOffset,Jimple.v().newAddExpr(innerOffset,LongConstant.v(curOffset))))

    val result=Jimple.v().newLocal("reslut",fieldType)
    locals.add(result)
    units.add(Jimple.v().newAssignStmt(result,Jimple.v().newStaticInvokeExpr(getCall.makeRef(),Arrays.asList(NullConstant.v(),lastOffset))))

    units.add(Jimple.v().newReturnStmt(result))

  }

  /**
    *
    * @param decaClass
    * @param curOffset
    * @param unfixedFieldList
    * @param fieldName
    * @param fieldType
    * @param inOffset
    * @param setCall
    * @param addressField
    */
  def addSetMethodForArrTypeRefBase(decaClass:SootClass, curOffset:Long, unfixedFieldList:util.ArrayList[(SootField,Long)], fieldName:String, fieldType:Type, inOffset:Long, setCall:SootMethod, addressField:SootField): Unit ={

    val primSize=getTypeSize(fieldType)

    val methodSet=new SootMethod("set"+fieldName,Arrays.asList(LongType.v(),fieldType),VoidType.v(),Modifier.PUBLIC)
    decaClass.addMethod(methodSet)
    val setBody=Jimple.v().newBody(methodSet)
    methodSet.setActiveBody(setBody)
    val units=setBody.getUnits
    val locals=setBody.getLocals


    val r0=Jimple.v().newLocal("r0",decaClass.getType)
    locals.add(r0)
    units.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(decaClass.getType)))


    //index=parameter(0)
    val i0=Jimple.v().newLocal("i0",LongType.v())
    locals.add(i0)
    units.add(Jimple.v().newIdentityStmt(i0,Jimple.v().newParameterRef(LongType.v(),0)))

    //value=parameter(1)
    val value=Jimple.v().newLocal("value",fieldType)
    locals.add(value)
    units.add(Jimple.v().newIdentityStmt(value,Jimple.v().newParameterRef(fieldType,1)))

    val l1=Jimple.v().newLocal("l1",addressField.getType)
    locals.add(l1)
    units.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))


    var index=0
    //设置一些变量
    var temp=Jimple.v().newLocal("temp"+index,LongType.v())
    var tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())
    var tempSum=Jimple.v().newLocal("tempSum"+index,LongType.v())
    locals.add(tempSum)
    units.add(Jimple.v().newAssignStmt(tempSum,LongConstant.v(0L)))

    for(arrLengthAndBaseLength<-unfixedFieldList){
      locals.add(temp)
      locals.add(tempBase)
      val arrLengthField=arrLengthAndBaseLength._1
      val baseLength=arrLengthAndBaseLength._2
      units.add(Jimple.v().newAssignStmt(temp,Jimple.v().newInstanceFieldRef(r0,arrLengthField.makeRef())))

      units.add(Jimple.v().newAssignStmt(tempBase,Jimple.v().newMulExpr(temp,LongConstant.v(baseLength))))

      val sum=Jimple.v().newLocal("sum"+index,LongType.v())
      locals.add(sum)
      units.add(Jimple.v().newAssignStmt(sum,Jimple.v().newAddExpr(tempSum,tempBase)))

      index+=1

      temp=Jimple.v().newLocal("temp"+index,LongType.v())
      tempBase=Jimple.v().newLocal("tempBase"+index,LongType.v())

      tempSum=sum


    }
    val resultSum=locals.getLast

    //数组内的偏移量

    //强制类型转换
//    val cast2Long=Jimple.v().newLocal("cast2Long",LongType.v())
//    locals.add(cast2Long)
//    units.add(Jimple.v().newAssignStmt(cast2Long,Jimple.v().newCastExpr(i0,LongType.v())))


    val inArrOffset=Jimple.v().newLocal("inArrOffset",LongType.v())
    locals.add(inArrOffset)
    units.add(Jimple.v().newAssignStmt(inArrOffset,Jimple.v().newMulExpr(i0,LongConstant.v(primSize))))

    val t1=Jimple.v().newLocal("t1",LongType.v())
    locals.add(t1)
    units.add(Jimple.v().newAssignStmt(t1,Jimple.v().newAddExpr(l1,resultSum)))

    val realoffset=Jimple.v().newLocal("realOffset",LongType.v())
    locals.add(realoffset)
    units.add(Jimple.v().newAssignStmt(realoffset,Jimple.v().newAddExpr(t1,inArrOffset)))

    //这里加上类之内的偏移
    val innerOffset=Jimple.v().newLocal("innerOffset",LongType.v())
    locals.add(innerOffset)
    units.add(Jimple.v().newAssignStmt(innerOffset,Jimple.v().newAddExpr(realoffset,LongConstant.v(inOffset))))

    //加上静态的
    val lastOffset=Jimple.v().newLocal("lastOffset",LongType.v())
    locals.add(lastOffset)
    units.add(Jimple.v().newAssignStmt(lastOffset,Jimple.v().newAddExpr(innerOffset,LongConstant.v(curOffset))))

//    val result=Jimple.v().newLocal("reslut",fieldType)
//    locals.add(result)
//    units.add(Jimple.v().newAssignStmt(result,Jimple.v().newStaticInvokeExpr(setCall.makeRef(),Arrays.asList(NullConstant.v(),lastOffset,value))))
//
//    units.add(Jimple.v().newReturnStmt(result))
    units.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setCall.makeRef(),Arrays.asList(NullConstant.v(),lastOffset,value))))
    units.add(Jimple.v().newReturnVoidStmt())

  }

  /***/
  def addInitMethod(decaClass:SootClass,allocate:SootMethod,setMem:SootMethod,context: Context,address:SootField,curOffset:Long,unfixedFieldList:util.ArrayList[(SootField,Long)]): Unit ={
    val init = new SootMethod("<init>", null, VoidType.v(),Modifier.PUBLIC)
    decaClass.addMethod(init)
    val initBody = Jimple.v().newBody(init)
    init.setActiveBody(initBody)
    val initUnits = initBody.getUnits
    //r0 := @this: cn.edu.hust.grid.soot.demo.demoFacade
    val r0=Jimple.v().newLocal("r0",decaClass.getType)
    initBody.getLocals.add(r0)
    initUnits.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(decaClass.getType)))
    //specialinvoke r0.<java.lang.Object: void <init>()>()
    initUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(r0,context.sootClass("java.lang.Object").getMethodByName("<init>").makeRef())))
    //$l0 = staticinvoke <cn.edu.hust.grid.soot.Platform: long allocateMemory(long)>(1000L)
    val i0=Jimple.v().newLocal("i0",LongType.v())
    initBody.getLocals.add(i0)
    initUnits.add(Jimple.v().newAssignStmt(i0,Jimple.v().newStaticInvokeExpr(allocate.makeRef(),LongConstant.v(curOffset))))

    //r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address> = $l0
    initUnits.add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(r0,address.makeRef()),i0))

    //$l1 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>
    val l1=Jimple.v().newLocal("l1",LongType.v())
    initBody.getLocals.add(l1)
    initUnits.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,address.makeRef())))

    //staticinvoke <cn.edu.hust.grid.soot.Platform: void setMemory(long,byte,long)>($l1, 0, 1000L)
    initUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setMem.makeRef(),Arrays.asList(l1,IntConstant.v(0),LongConstant.v(curOffset)))))

    var index=1;
    for(info<-unfixedFieldList){
      val field=info._1
      val temp=Jimple.v().newLocal("temp"+index,LongType.v())
      init.getActiveBody.getLocals.add(temp)
      initUnits.add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(r0,field.makeRef()),LongConstant.v(10)))
    }
    //return
    initUnits.add(Jimple.v().newReturnVoidStmt())
  }







  def cloneMethod(oldMethod:SootMethod,oldSootClass:SootClass,newSootClass:SootClass): Unit ={
    if(newSootClass.getMethodUnsafe(oldMethod.getSubSignature)!=null){
      return
    }


    val localMethodBody = oldMethod.getActiveBody
    val newMethod = new SootMethod(oldMethod.getName, oldMethod.getParameterTypes, oldMethod.getReturnType,
      oldMethod.getModifiers, oldMethod.getExceptions)
    newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
    newMethod.setDeclaringClass(newSootClass)
    newSootClass.addMethod(newMethod)
    val newMethodBody = newMethod.retrieveActiveBody()

    for (local <- newMethodBody.getLocals) {
      if (local.getType.toString.equals(oldSootClass.getName)) {
        local.setType(newSootClass.getType)
      }
    }

    for (unit <- newMethodBody.getUnits.snapshotIterator()) {
      if (unit.isInstanceOf[JIdentityStmt]) {
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
          jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
        }
        //        } else if (unit.isInstanceOf[JAssignStmt]) {
        //          val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        //          if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
        //            val field = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].getField
        //            val fieldName = field.getName
        //            if (field.getDeclaringClass == oldSootClass) {
        //              val newFieldRef = newSootClass.getFieldByName(fieldName).makeRef()
        //              jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].setFieldRef(newFieldRef)
        //            }
        //          }
      }
    }


    //我怀疑这里万一，有的方法没克隆完，那么方法转换会出错的，所以最好是先对所有方法进行上面的循环，再对所有方法进行下面的循环
    for (unit <- newMethodBody.getUnits.snapshotIterator()) {

      /**
        * 这里加一个map，key为local，value为对应的字段吧
        */
      val localFieldMap=new mutable.HashMap[JimpleLocal,SootField]()
      if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]
          if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
            //              val invokeName = jVirtualInvokeExpr.getMethodRef.name()
            //              val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
            if(newSootClass.getMethodUnsafe(jVirtualInvokeExpr.getMethod.getSubSignature)==null){
              cloneMethod(jVirtualInvokeExpr.getMethod,oldSootClass,newSootClass)
            }

            val newMethodRef = newSootClass.getMethod(jVirtualInvokeExpr.getMethodRef.getSubSignature).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        } else if (jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]
          if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
            if(newSootClass.getMethodUnsafe(jVirtualInvokeExpr.getMethod.getSubSignature)==null){
              cloneMethod(jVirtualInvokeExpr.getMethod,oldSootClass,newSootClass)
            }

            val newMethodRef = newSootClass.getMethod(jVirtualInvokeExpr.getMethodRef.getSubSignature).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        }

        /** 这里要改下字段方法，比如set和get */
        else if (jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]
          if (jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(oldSootClass.getName)) {
            //            val invokeName = jInstanceFieldRef.getFieldRef.name()
            //            val newFieldRef = newSootClass.getFieldByName(invokeName).makeRef()
            //            jInstanceFieldRef.setFieldRef(newFieldRef)
            if (jInstanceFieldRef.getFieldRef.`type`().isInstanceOf[PrimType]) {

              val putMethod = newSootClass.getMethodByName("set" + jInstanceFieldRef.getFieldRef.name())

              val nUnit = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, putMethod.makeRef(), jAssignStmt.getRightOp))
              newMethodBody.getUnits.insertBefore(nUnit, unit)
              newMethodBody.getUnits.remove(unit)

            }
            /**这里针对的是那种字段为类的get，set*/
            else if(jInstanceFieldRef.getFieldRef.`type`().isInstanceOf[RefType]){

              val rightValue=jAssignStmt.getRightOp
              if(rightValue.isInstanceOf[JimpleLocal]){
                val rightLocal=rightValue.asInstanceOf[JimpleLocal]

                //向上找初始化方法
                var flag=false
                var curUnit=unit
                var tempUnit=unit
                while (!flag){
                  val preUnit=newMethodBody.getUnits.getPredOf(curUnit)
                  if(preUnit.isInstanceOf[JInvokeStmt]){
                    if(preUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.isInstanceOf[JSpecialInvokeExpr]){
                      val specialInvokeExpr=preUnit.asInstanceOf[JInvokeStmt].getInvokeExpr.asInstanceOf[JSpecialInvokeExpr]
                      if(specialInvokeExpr.getBase==rightLocal){
                        if(specialInvokeExpr.getMethodRef.name().equals("<init>")){
                          val methodRef=specialInvokeExpr.getMethodRef
                          val parameters=specialInvokeExpr.getArgs

//                          val rightBox=Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal,newSootClass.getMethod("set"+jInstanceFieldRef.getFieldRef.name(),methodRef.parameterTypes(),
//                            methodRef.returnType()).makeRef(),parameters)
//
//                          //这里设置了之后，是不是上面的new语句要删掉
//                          jAssignStmt.setRightOp(Jimple.v().newInvokeExprBox(rightBox))


                          //应该是删掉这条语句
                          newMethodBody.getUnits.insertAfter(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal,newSootClass.getMethod("set"+
                          jInstanceFieldRef.getFieldRef.name(),methodRef.parameterTypes(),methodRef.returnType()).makeRef(),parameters)),unit)
                          newMethodBody.getUnits.remove(unit)


                          tempUnit=preUnit

                        }
                      }
                    }
                  }else if(preUnit.isInstanceOf[JAssignStmt]){
                    if(preUnit.asInstanceOf[JAssignStmt].getLeftOp.isInstanceOf[JimpleLocal]){
                      val leftLocal=preUnit.asInstanceOf[JAssignStmt].getLeftOp.asInstanceOf[JimpleLocal]
                      if(leftLocal==rightLocal&&preUnit.asInstanceOf[JAssignStmt].getRightOp.isInstanceOf[JNewExpr]){

                        val newExpr=preUnit.asInstanceOf[JAssignStmt].getRightOp.asInstanceOf[JNewExpr]
                        if(newExpr.getType.isInstanceOf[RefType]){
                          if(newExpr.getType.asInstanceOf[RefType].getClassName.equals(jInstanceFieldRef.getFieldRef.`type`().toString)){
                            newMethodBody.getUnits.remove(preUnit)

                            flag=true
                            newMethodBody.getUnits.remove(tempUnit)


                          }
                        }

                      }
                    }

                  }
                  curUnit=preUnit
                }


              }

            }
            else{
//              /**如果左边是数组类型*/
//                //这里默认右边是local
//              val rightLocal=jAssignStmt.getRightOp.asInstanceOf[JimpleLocal]
//              var flag=false
//              var curUnit=unit
//              var preUnit=unit
//              while (!flag){
//                preUnit=newMethodBody.getUnits.getPredOf(curUnit)
//                if(preUnit.isInstanceOf[JAssignStmt]){
//                  if(preUnit.asInstanceOf[JAssignStmt].getLeftOp.isInstanceOf[JimpleLocal]){
//                    if(preUnit.asInstanceOf[AssignStmt].getLeftOp.asInstanceOf[JimpleLocal]==rightLocal&&preUnit.asInstanceOf[JAssignStmt].getRightOp.isInstanceOf[JNewArrayExpr]){
//                      val newArrayExpr=preUnit.asInstanceOf[JAssignStmt].getRightOp.asInstanceOf[JNewArrayExpr]
//
//                      val length=newArrayExpr.getSize
//
//                      val fieldLengthAssign=Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(newMethodBody.getThisLocal,newSootClass.getFieldByName(jInstanceFieldRef.getFieldRef.name()+"Length").makeRef()),length)
//
//                      newMethodBody.getUnits.insertAfter(fieldLengthAssign,preUnit)
//                      newMethodBody.getUnits.remove(preUnit)
//                      flag=true
//
//                    }
//                  }
//                }
//                curUnit=preUnit
//
//              }
//              newMethodBody.getUnits.remove(unit)


            }
          }
        } else if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          if (jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(oldSootClass.getName)) {
            //            val invokeName = jInstanceFieldRef.getFieldRef.name()
            //            val newFieldRef = newSootClass.getFieldByName(invokeName).makeRef()
            //            jInstanceFieldRef.setFieldRef(newFieldRef)
            if (jInstanceFieldRef.getFieldRef.`type`().isInstanceOf[PrimType]) {
              val getMethod = newSootClass.getMethodByName("get" + jInstanceFieldRef.getFieldRef.name())

              jAssignStmt.setRightOp(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal, getMethod.makeRef()))
            }
//            else if(jInstanceFieldRef.getFieldRef.`type`().isInstanceOf[ArrayType]){
//              val leftOp=jAssignStmt.getLeftOp
//              if(leftOp.isInstanceOf[JimpleLocal]){
//                localFieldMap.put(leftOp.asInstanceOf[JimpleLocal],jInstanceFieldRef.getField)
//                newMethodBody.getUnits.remove(unit)
//              }
//
//            }
          }
        }
        //如何把arr类型的local调用set方法放进去呢
//
//        else if(jAssignStmt.getLeftOp.isInstanceOf[JArrayRef]&&localFieldMap.contains(jAssignStmt.getLeftOp.asInstanceOf[JArrayRef].getBase.asInstanceOf[JimpleLocal])){
//          val relateField=localFieldMap.get(jAssignStmt.getLeftOp.asInstanceOf[JArrayRef].getBase.asInstanceOf[JimpleLocal])
//          val methodCall=newSootClass.getMethodByName("set"+relateField.get.getName)
//
//          val arrayRef=jAssignStmt.getLeftOp.asInstanceOf[JArrayRef]
//          val index=arrayRef.getIndex
//          newMethodBody.getUnits.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(newMethodBody.getThisLocal,methodCall.makeRef(),Arrays.asList(index,jAssignStmt.getRightOp))),
//            unit)
//          newMethodBody.getUnits.remove(unit)
//        }

      } else if (unit.isInstanceOf[JInvokeStmt]) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
        if (invokeMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {

          if(newSootClass.getMethodUnsafe(invokeMethodRef.getSubSignature)==null){
            cloneMethod(jInvokeStmt.getInvokeExpr.getMethod,oldSootClass,newSootClass)
          }
          val newInvokeMethodRef = newSootClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
          jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
        }
      }
    }
  }
  /**
    * 转换
    */
  def convertMethod( oldSootClass:SootClass, newSootClass:SootClass):Unit= {
    for(method<-oldSootClass.getMethods){
      cloneMethod(method,oldSootClass,newSootClass)
    }
  }
}

