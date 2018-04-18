package cn.edu.hust.grid.soot.optimize

import java.io.{FileOutputStream, OutputStream, OutputStreamWriter, PrintWriter}
import java.util

import soot._

import scala.collection.JavaConversions._
import java.util.Arrays

import soot.jimple._
import soot.jimple.internal.{JInvokeStmt, JimpleLocal}
import soot.options.Options
import soot.util.JasminOutputStream


object SplitClass {


  def split(sc: SootClass, context: Context):SootClass= {
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


    val freeMemory=platForm.getMethodByName("freeMemory")
    val allcotaMemory=platForm.getMethod("long allocateMemory(long)")
    val setMemory=platForm.getMethod("void setMemory(long,byte,long)")

    var curOffset: Long = 0

    val allFields = new util.ArrayList[SootField]()
    sc.getFields.map(field => allFields.add(field))

    var parrentClass = sc.getSuperclass
    while (!parrentClass.getName.equals("java.lang.Object")) {
      parrentClass.getFields.map(field => allFields.add(field))
      parrentClass = parrentClass.getSuperclass
    }

    // create a new class
    val facadeClass = new SootClass(sc.getName + "Facade", Modifier.PUBLIC)

    // add the extend class
    facadeClass.setSuperclass(context.sootClass("java.lang.Object"))
    //因为我想输出这个类
    context.applicationClasses.add(facadeClass)

    val addressField = new SootField("address", LongType.v(),Modifier.PUBLIC)
    facadeClass.addField(addressField)

    for (field <- allFields) {

      println(field.getName+" "+field.getDeclaringClass+"  "+field.getType.isInstanceOf[RefType])

      /**
      **如果这个field不是引用类型，也就是说是基本类型
       */
      if (!field.getType.isInstanceOf[RefType]) {
        val setCall={
          if(field.getType.isInstanceOf[IntType]){
            putInt
          }else if (field.getType.isInstanceOf[LongType]){
            putLong
          }else if(field.getType.isInstanceOf[DoubleType]){
            putDouble
          }else if(field.getType.isInstanceOf[FloatType]){
            putFloat
          }else if (field.getType.isInstanceOf[BooleanType]) {
            putBoolean
          }else if(field.getType.isInstanceOf[ByteType]){
            putByte
          }else{
            putShort
          }
        }
        val getCall={
          if(field.getType.isInstanceOf[IntType]){
            getInt
          }else if (field.getType.isInstanceOf[LongType]){
            getLong
          }else if(field.getType.isInstanceOf[DoubleType]){
            getDouble
          }else if(field.getType.isInstanceOf[FloatType]){
            getFloat
          }else if (field.getType.isInstanceOf[BooleanType]) {
            getBoolean
          }else if(field.getType.isInstanceOf[ByteType]){
            getByte
          }else{
            getShort
          }
        }
      // create the get method
      {
        val methodGet = new SootMethod("get" + field.getName, null, field.getType, Modifier.PUBLIC)
        facadeClass.addMethod(methodGet)

        val getBody = Jimple.v().newBody(methodGet)
        methodGet.setActiveBody(getBody)
        val getUnits = getBody.getUnits
        // l1 := @this: cn.edu.hust.grid.soot.demo....
        //        val local=new JimpleLocal("l1",field.getType)
        //        getBody.getLocals.add(local)
        //
        //r0=facadeClass
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
        //, List(new NullConstant(null), r2))))


        //return r3
        getUnits.add(Jimple.v().newReturnStmt(r3))

      }
      //create the set method
      {
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

        //偏移量增加
         curOffset={
          if(field.getType.isInstanceOf[IntType]){
            curOffset+4
          }else if (field.getType.isInstanceOf[LongType]){
            curOffset+8
          }else if(field.getType.isInstanceOf[DoubleType]){
            curOffset+8
          }else if(field.getType.isInstanceOf[FloatType]){
            curOffset+8
          }else if (field.getType.isInstanceOf[BooleanType]) {
            curOffset+1
          }else if(field.getType.isInstanceOf[ByteType]){
            curOffset+1
          }else{
            curOffset+2
          }
        }
    } else{
        /**此处需要加一个get方法，返回值应该是一个long地址，然后还有一个init方法，是初始化一个facade。然后还有一个是set方法，传入一个对象吧
          * 需要三个方法，
        */
        val refType=field.getType.asInstanceOf[RefType]
        val refClass=refType.getSootClass
        //递归拆解这个字段类
        val afterSplit=split(refClass,context)
        //拆解之后是一个新的facade
        /** get这个字段的方法，返回一个地址
         */

        {
          val methodGet = new SootMethod("get" + field.getName, null,LongType.v(), Modifier.PUBLIC)
          facadeClass.addMethod(methodGet)

          val getBody = Jimple.v().newBody(methodGet)
          methodGet.setActiveBody(getBody)
          val getUnits = getBody.getUnits
          // l1 := @this: cn.edu.hust.grid.soot.demo....
          //        val local=new JimpleLocal("l1",field.getType)
          //        getBody.getLocals.add(local)
          //
          //r0=facadeClass
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
          val r3 = Jimple.v().newLocal("r3", LongType.v())
          getBody.getLocals.add(r3)
          getUnits.add(Jimple.v().newAssignStmt(r3, Jimple.v().newStaticInvokeExpr(getLong.makeRef(), Arrays.asList(NullConstant.v(), r2))))
          //, List(new NullConstant(null), r2))))


          //return r3
          getUnits.add(Jimple.v().newReturnStmt(r3))
        }

        /** 此处加set方法，无返回值，参数是那个类，如何set呢，首先是如果地址为0，那么是没有set过，就进行一次构造吧
          * 如果有地址，那就先释放掉这部分空间，然后重新构造。
           */

        {
          val setMethod=new SootMethod("set"+field.getName,Arrays.asList(refClass.getType),VoidType.v(),Modifier.PUBLIC)
          facadeClass.addMethod(setMethod)
          val setBody=Jimple.v().newBody(setMethod)
          setMethod.setActiveBody(setBody)
          val setUnits=setBody.getUnits
          val locals=setBody.getLocals
          /**
            0 = {JIdentityStmt@1675} "r0 := @this: cn.edu.hust.grid.soot.demo.demoFacade"
            1 = {JIdentityStmt@1676} "r1 := @parameter0: cn.edu.hust.grid.soot.demo.flattenExample"
            2 = {JAssignStmt@1677} "$l0 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>"
            3 = {JAssignStmt@1678} "$l1 = $l0 + 8L"
            4 = {JAssignStmt@1679} "$l2 = staticinvoke <cn.edu.hust.grid.soot.Platform: long getLong(java.lang.Object,long)>(null, $l1)"
            5 = {JAssignStmt@1680} "$b3 = $l2 cmp 0L"
            6 = {JIfStmt@1681} "if $b3 == 0 goto $l4 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>"
            7 = {JAssignStmt@1682} "$l7 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>"
            8 = {JAssignStmt@1683} "$l8 = $l7 + 8L"
            9 = {JAssignStmt@1684} "$l9 = staticinvoke <cn.edu.hust.grid.soot.Platform: long getLong(java.lang.Object,long)>(null, $l8)"
            10 = {JInvokeStmt@1685} "staticinvoke <cn.edu.hust.grid.soot.Platform: void freeMemory(long)>($l9)"
            11 = {JAssignStmt@1686} "$l4 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>"
            12 = {JAssignStmt@1687} "$l5 = $l4 + 8L"
            13 = {JAssignStmt@1688} "$r2 = new cn.edu.hust.grid.soot.demo.flatternExampleFacade"
            14 = {JInvokeStmt@1689} "specialinvoke $r2.<cn.edu.hust.grid.soot.demo.flatternExampleFacade: void <init>(cn.edu.hust.grid.soot.demo.flattenExample)>(r1)"
            15 = {JAssignStmt@1690} "$l6 = $r2.<cn.edu.hust.grid.soot.demo.flatternExampleFacade: long address>"
            16 = {JInvokeStmt@1691} "staticinvoke <cn.edu.hust.grid.soot.Platform: void putLong(java.lang.Object,long,long)>(null, $l5, $l6)"
            17 = {JReturnVoidStmt@1692} "return"
            *
            * */

          val r0=Jimple.v().newLocal("r0",facadeClass.getType)
          locals.add(r0)
          setUnits.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(facadeClass.getType)))

          val r1=Jimple.v().newLocal("r1",refClass.getType)
          locals.add(r1)
          setUnits.add(Jimple.v().newIdentityStmt(r1,Jimple.v().newParameterRef(refClass.getType,0)))

          var l0=Jimple.v().newLocal("l0",LongType.v())
          locals.add(l0)
          setUnits.add(Jimple.v().newAssignStmt(l0,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))

          val l1=Jimple.v().newLocal("l1",LongType.v)
          locals.add(l1)
          setUnits.add(Jimple.v().newAssignStmt(l1,Jimple.v().newAddExpr(l0,LongConstant.v(curOffset))))

          val l2=Jimple.v().newLocal("l2",LongType.v())
          locals.add(l2)
          setUnits.add(Jimple.v().newAssignStmt(l2,Jimple.v().newStaticInvokeExpr(getLong.makeRef(),Arrays.asList(NullConstant.v(),l1))))

          val b3=Jimple.v().newLocal("b3",ByteType.v())
          locals.add(b3)
          setUnits.add(Jimple.v().newAssignStmt(b3,Jimple.v().newCmpExpr(l2,LongConstant.v(0))))


          val l4=Jimple.v().newLocal("l4",LongType.v())
          locals.add(l4)
          val gotoUnit=Jimple.v().newAssignStmt(l4,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef()))


          setUnits.add(Jimple.v().newIfStmt(Jimple.v().newEqExpr(b3,IntConstant.v(0)),gotoUnit))

          //这里就重复下吧，别出错就好
          var l7=Jimple.v().newLocal("l7",LongType.v())
          locals.add(l7)
          setUnits.add(Jimple.v().newAssignStmt(l7,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))

          val l8=Jimple.v().newLocal("l8",LongType.v)
          locals.add(l8)
          setUnits.add(Jimple.v().newAssignStmt(l8,Jimple.v().newAddExpr(l7,LongConstant.v(curOffset))))

          val l9=Jimple.v().newLocal("l9",LongType.v())
          locals.add(l9)
          setUnits.add(Jimple.v().newAssignStmt(l9,Jimple.v().newStaticInvokeExpr(getLong.makeRef(),Arrays.asList(NullConstant.v(),l8))))

          setUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(freeMemory.makeRef(),l9)))

          setUnits.add(gotoUnit)

          val l5=Jimple.v().newLocal("l5",LongType.v())
          locals.add(l5)
          setUnits.add(Jimple.v().newAssignStmt(l5,Jimple.v().newAddExpr(l4,LongConstant.v(curOffset))))

          val r2=Jimple.v().newLocal("r2",afterSplit.getType)
          locals.add(r2)
          setUnits.add(Jimple.v().newAssignStmt(r2,Jimple.v().newNewExpr(afterSplit.getType)))

          setUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(r2,afterSplit.getMethod("void <init>("+refClass.getName+")").makeRef(),r1)))

          val l6=Jimple.v().newLocal("l6",LongType.v())
          locals.add(l6)
          setUnits.add(Jimple.v().newAssignStmt(l6,Jimple.v().newInstanceFieldRef(r2,afterSplit.getFieldByName("address").makeRef())))

          setUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(putLong.makeRef(),Arrays.asList(NullConstant.v(),l5,l6))))

          setUnits.add(Jimple.v().newReturnVoidStmt())


        }




        curOffset+=8


      }


    }

    {
      // add the init methodof facade
      val init = new SootMethod("<init>", null, VoidType.v(),Modifier.PUBLIC)
      facadeClass.addMethod(init)
      val initBody = Jimple.v().newBody(init)
      init.setActiveBody(initBody)
      val initUnits = initBody.getUnits
      //r0 := @this: cn.edu.hust.grid.soot.demo.demoFacade
      val r0=Jimple.v().newLocal("r0",facadeClass.getType)
      initBody.getLocals.add(r0)
      initUnits.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(facadeClass.getType)))
      //specialinvoke r0.<java.lang.Object: void <init>()>()
      initUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(r0,context.sootClass("java.lang.Object").getMethodByName("<init>").makeRef())))
      //$l0 = staticinvoke <cn.edu.hust.grid.soot.Platform: long allocateMemory(long)>(1000L)
      val i0=Jimple.v().newLocal("i0",LongType.v())
      initBody.getLocals.add(i0)
      initUnits.add(Jimple.v().newAssignStmt(i0,Jimple.v().newStaticInvokeExpr(allcotaMemory.makeRef(),LongConstant.v(curOffset))))

      //r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address> = $l0
      initUnits.add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(r0,addressField.makeRef()),i0))

      //$l1 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>
      val l1=Jimple.v().newLocal("l1",LongType.v())
      initBody.getLocals.add(l1)
      initUnits.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))

      //staticinvoke <cn.edu.hust.grid.soot.Platform: void setMemory(long,byte,long)>($l1, 0, 1000L)
      initUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setMemory.makeRef(),Arrays.asList(l1,IntConstant.v(0),LongConstant.v(curOffset)))))
      //return
      initUnits.add(Jimple.v().newReturnVoidStmt())




    }
    {
      // add the init methodof facade
      val init = new SootMethod("<init>", Arrays.asList(sc.getType), VoidType.v(),Modifier.PUBLIC)
      facadeClass.addMethod(init)
      val initBody = Jimple.v().newBody(init)
      init.setActiveBody(initBody)
      val initUnits = initBody.getUnits
      //r0 := @this: cn.edu.hust.grid.soot.demo.demoFacade
      val r0=Jimple.v().newLocal("r0",facadeClass.getType)
      initBody.getLocals.add(r0)
      initUnits.add(Jimple.v().newIdentityStmt(r0,Jimple.v().newThisRef(facadeClass.getType)))
      /**
        * 这里的parameter0没有用，所以疯狂出错
        * */
      val p0=Jimple.v().newLocal("p0",sc.getType)
      initBody.getLocals.add(p0)
      initUnits.add(Jimple.v().newIdentityStmt(p0,Jimple.v().newParameterRef(sc.getType,0)))



      //specialinvoke r0.<java.lang.Object: void <init>()>()
      initUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(r0,context.sootClass("java.lang.Object").getMethodByName("<init>").makeRef())))
      //$l0 = staticinvoke <cn.edu.hust.grid.soot.Platform: long allocateMemory(long)>(1000L)
      val i0=Jimple.v().newLocal("i0",LongType.v())
      initBody.getLocals.add(i0)
      initUnits.add(Jimple.v().newAssignStmt(i0,Jimple.v().newStaticInvokeExpr(allcotaMemory.makeRef(),LongConstant.v(curOffset))))

      //r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address> = $l0
      initUnits.add(Jimple.v().newAssignStmt(Jimple.v().newInstanceFieldRef(r0,addressField.makeRef()),i0))

      //$l1 = r0.<cn.edu.hust.grid.soot.demo.demoFacade: long address>
      val l1=Jimple.v().newLocal("l1",LongType.v())
      initBody.getLocals.add(l1)
      initUnits.add(Jimple.v().newAssignStmt(l1,Jimple.v().newInstanceFieldRef(r0,addressField.makeRef())))

      //staticinvoke <cn.edu.hust.grid.soot.Platform: void setMemory(long,byte,long)>($l1, 0, 1000L)
      initUnits.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setMemory.makeRef(),Arrays.asList(l1,IntConstant.v(0),LongConstant.v(curOffset)))))
      //return
      initUnits.add(Jimple.v().newReturnVoidStmt())
    }


    facadeClass

  }





    def main(args: Array[String]) {
//      val context=new Context("cn.edu.hust.grid.soot.demo.testFlattern")

      val excludeLi=List("sun.misc.*")


      val context = new Context(excludePackages = excludeLi,preload = false)
//
//
//      context.loadClass("cn.edu.hust.grid.soot.Platform",true)
//      val platForm = context.sootClass("cn.edu.hust.grid.soot.Platform")
//      print(1)
//      context.loadClass("cn.edu.hust.grid.soot.demo.testFlattern",true)
      context.loadClass("cn.edu.hust.grid.soot.Platform",true)

      dynamicLoad("cn.edu.hust.grid.soot.demo.testFlattern",context)


      val sc = context.sootClass("cn.edu.hust.grid.soot.demo.testFlattern")
      split(sc,context)


      val ob=context.sootClass("java.lang.Object")
      context.scene.removeClass(context.sootClass("cn.edu.hust.grid.soot.Platform"))
      context.scene.removeClass(ob)
      context.writeOutput()

    }

  def dynamicLoad(class2Load: String,context: Context){
    context.loadClass(class2Load,true)
    val  sc=context.sootClass(class2Load)
    var parentClass=sc.getSuperclass
    val fields=sc.getFields

    for(field<-fields){
      if (field.getType.isInstanceOf[RefType]){
        val refType=field.getType.asInstanceOf[RefType]
        val sootClass=refType.getSootClass
        context.loadClass(sootClass.getName,true)
        println("load class "+sootClass.getName)

      }
    }
    while (!parentClass.getName.equals("java.lang.Object")){
      context.loadClass(parentClass.getName,true)
      println("loadclass "+parentClass.getName)


      parentClass=parentClass.getSuperclass
    }


  }

  }

