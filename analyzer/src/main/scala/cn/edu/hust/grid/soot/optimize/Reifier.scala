package cn.edu.hust.grid.soot.optimize

import java.util.ArrayList

import cn.edu.hust.grid.soot.Utils
import soot._
import soot.jimple._
import soot.jimple.internal._
import soot.jimple.toolkits.callgraph.Edge

import scala.collection.JavaConversions._

/**
 * Created by root on 15-8-6.
 */
object Reifier extends Transformer {

  val genericityClasses = new ArrayList[String]
  val REIFIER_MAP = new scala.collection.mutable.HashMap[String,Int]
  var REIFIER_COUNT = 1
  val REIFIEDCLASS = new ArrayList[String]

  val reifier_type = new ArrayList[Type]
  val extendClasses = new ArrayList[String]

  override def transform(context: Context){
    for (appClass <- context.applicationClasses if appClass.hasTag("SignatureTag")){
      genericityClasses.add(appClass.getName)
    }
    val mainClass = context.sootClass(context.mainClass)
    val entryMethod = mainClass.getMethodByName(context.entryMethod)
    getReifyTypeInMethod(entryMethod,context)
    if(reifier_type.length==0){
      throw OptimizeException("Cannot get the reify type.")
    }else{
      reifyProject(context)
    }
    transformCallGraph(context)
  }

  def reifyWithNewClass(className:String,context:Context,reifyType:Type){

    // whether this class has been reified
    if(REIFIER_MAP.contains(reifyType.toString) && genericityClasses.contains(className)){
      return
    }

    // set the simple name of new class
    REIFIER_MAP += (reifyType.toString -> REIFIER_COUNT)
    REIFIER_COUNT += 1
    val appClass = context.sootClass(className)
    val reifyClass = new SootClass(appClass.getName+"AS"+REIFIER_MAP(reifyType.toString))
    reifyClass.setSuperclass(appClass.getSuperclass)

    // convert the fields
    for(field <- appClass.getFields){
        if(field.hasTag("SignatureTag")) {
          val reifyField = new SootField(field.getName, reifyType, field.getModifiers)
          reifyClass.addField(reifyField)
        }
        else {
          val reifyField = new SootField(field.getName, field.getType, field.getModifiers)
          reifyClass.addField(reifyField)
        }
    }

    /**
     *  convert the methods
     *  --extendClassAndMethodList : It means that some extend class has important method
     *  --methodFurtherOptimize : After the convert of methods, some methods should be further optimize
     */
    val extendClassAndMethodList = new ArrayList[(String,String)]
    val methodFurtherOptimize = new ArrayList[(String,String)]
    for(method <- appClass.getMethods){
      // method with generity
      if(method.hasTag("SignatureTag")) {
        val parameterTypes = method.getParameterTypes
        val newParameterTypes = new ArrayList[Type]

        // convert parameters of method
        for (parameterType <- parameterTypes) {
          if (parameterType.toString.equals("java.lang.Object")){
            if(reifyType.isInstanceOf[ArrayType])
              newParameterTypes.add(reifyType.asInstanceOf[ArrayType].getElementType)
            else
              newParameterTypes.add(reifyType)
          }
          else if(parameterType.toString.equals("java.lang.Object[]"))
            newParameterTypes.add(reifyType)
          else if(parameterType.toString.equals(className))
            newParameterTypes.add(reifyClass.getType)
          else
            newParameterTypes.add(parameterType)
        }
        val newMethod = new SootMethod(method.getName,newParameterTypes,
          method.getReturnType,method.getModifiers,method.getExceptions)
        newMethod.setDeclared(false)
        reifyClass.addMethod(newMethod)

        // convert locals of method
        newMethod.setActiveBody(Utils.cloneSootBody(method.getActiveBody))
        val newMethodBody = newMethod.retrieveActiveBody()
        val localIt = newMethodBody.getLocals.iterator()
        while(localIt.hasNext){
          val local = localIt.next()
          if(local.getType.toString.equals(className))
            local.setType(reifyClass.getType)
          else if(local.getType.toString.equals("java.lang.Object")){
            if(reifyType.isInstanceOf[ArrayType])
              local.setType(reifyType.asInstanceOf[ArrayType].getElementType)
            else
              local.setType(reifyType)
          }
          else if(local.getType.toString.equals("java.lang.Object[]"))
            local.setType(reifyType)
          else if(local.getType.toString.contains(className+"$")){
            extendClasses.add(local.getType.toString)
          }
        }

        // convert body of method
        for(unit <- newMethodBody.getUnits){

          // identity stmt, like :=
          if(unit.getClass.getName.equals("soot.jimple.internal.JIdentityStmt")){
            val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
            val rightType = jIdentityStmt.getRightOp.getType
            // class object
            if(rightType.equals(appClass.getType)){
              unit.getUseBoxes.foreach(valueBox => {
                if(valueBox.getValue.getClass.getName.equals("soot.jimple.ThisRef")){
                  valueBox.setValue(new ThisRef(reifyClass.getType))
                } else if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")) {
                  val paraNumber = valueBox.getValue.toString().charAt(10)
                  valueBox.setValue(new ParameterRef(newMethod.getParameterType(paraNumber.toInt - 48),
                    paraNumber.toInt - 48))
                }
              }
              )
            }
            // java.lang.Object
            else if(rightType.toString.equals("java.lang.Object")){
              unit.getUseBoxes.foreach(valueBox => {
                if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")){
                  val paraNumber = valueBox.getValue.toString().charAt(10)
                  if(reifyType.isInstanceOf[ArrayType])
                    valueBox.setValue(new ParameterRef(reifyType.asInstanceOf[ArrayType].getElementType,
                      paraNumber.toInt-48))
                  else
                    valueBox.setValue(new ParameterRef(reifyType,paraNumber.toInt-48))
                }
              })
            }
            // java.lang.Object[]
            else if(rightType.toString.equals("java.lang.Object[]")){
              unit.getUseBoxes.foreach(valueBox => {
                if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")){
                  val paraNumber = valueBox.getValue.toString().charAt(10)
                  valueBox.setValue(new ParameterRef(reifyType, paraNumber.toInt-48))
                }
              })
            }
          }

          // assign stmt, like =
          else if(unit.getClass.getName.equals("soot.jimple.internal.JAssignStmt")){
            val jAssignStmt = unit.asInstanceOf[JAssignStmt]
            jAssignStmt.getUseAndDefBoxes.foreach(valueBox => {
              val value = valueBox.getValue()
              // fieldRef
              if(value.isInstanceOf[FieldRef]){
                val ref = value.asInstanceOf[FieldRef]
                if(!extendClassAndMethodList.forall(!_._2.equals(ref.getFieldRef.name()))
                  && !newMethod.getName.equals("<init>")){
                  methodFurtherOptimize.add((newMethod.getName,ref.getFieldRef.name()))
                }
                val field = reifyClass.getFieldByName(ref.getField.getName)
                val newSRF = SootHelper.makeFieldRef(field, context)
                ref.setFieldRef(newSRF)
              } else if(value.isInstanceOf[JVirtualInvokeExpr]){

              }
              // we should get the extend class and notice that we must get the method point to it.
              else if(value.isInstanceOf[JNewExpr]){
                val jNewExpr = value.asInstanceOf[JNewExpr]
                val exprClassName = jNewExpr.getBaseType.toString
                val exprLocal = jAssignStmt.getLeftOpBox.getValue.toString()
                val exprInterfaceBox = newMethodBody.getUnits
                  .filter(_.getClass.getName.equals("soot.jimple.internal.JAssignStmt"))
                  .filter(_.asInstanceOf[JAssignStmt].getRightOpBox.getValue.toString().equals(exprLocal))
                  .map(_.asInstanceOf[JAssignStmt].getLeftOpBox).last
                if(exprInterfaceBox.getValue.getClass.getName.equals("soot.jimple.internal.JInstanceFieldRef")){
                  extendClassAndMethodList.add((exprClassName,
                    exprInterfaceBox.getValue.asInstanceOf[JInstanceFieldRef].getFieldRef.name()))
                }
              }
              // cast type
              else if(value.isInstanceOf[JCastExpr]){
                val jCastExpr = value.asInstanceOf[JCastExpr]
                if(jCastExpr.getCastType.toString.equals(className))
                  jCastExpr.setCastType(reifyClass.getType)
                else if(jCastExpr.getCastType.toString.equals("java.lang.Object[]"))
                  jCastExpr.setCastType(reifyType)
              }
            })
          }
          // other type
          else {

          }
        }

        // return type
        if(newMethod.getReturnType.toString.equals(className)){
          newMethod.setReturnType(reifyClass.getType)
        } else if(newMethod.getReturnType.toString.equals("java.lang.Object")){
          if(reifyType.isInstanceOf[ArrayType])
            newMethod.setReturnType(reifyType.asInstanceOf[ArrayType].getElementType)
          else
            newMethod.setReturnType(reifyType)
        }else if(newMethod.getReturnType.toString.equals("java.lang.Object[]")){
          newMethod.setReturnType(reifyType)
        }

      }else{

        // method without generity
        val parameterTypes = method.getParameterTypes
        val newMethod = new SootMethod(method.getName,parameterTypes,
          method.getReturnType,method.getModifiers,method.getExceptions)
        newMethod.setDeclared(false)
        reifyClass.addMethod(newMethod)

        // change body of new method
        newMethod.setActiveBody(Utils.cloneSootBody(method.getActiveBody))
        val newMethodBody = newMethod.retrieveActiveBody()
        val localIt = newMethodBody.getLocals.iterator()
        while(localIt.hasNext){
          val local = localIt.next()
          if(local.getType.toString.equals(className))
            local.setType(reifyClass.getType)
          else if(local.getType.toString.equals("java.lang.Object")){
            if(reifyType.isInstanceOf[ArrayType])
              local.setType(reifyType.asInstanceOf[ArrayType].getElementType)
            else
              local.setType(reifyType)
          }
          else if(local.getType.toString.equals("java.lang.Object[]"))
            local.setType(reifyType)
        }

        for(unit <- newMethodBody.getUnits){
          // identity stmt, like :=
          if(unit.getClass.getName.equals("soot.jimple.internal.JIdentityStmt")){
            val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
            val rightType = jIdentityStmt.getRightOp.getType
            if(rightType.equals(appClass.getType)){
              unit.getUseBoxes.foreach(valueBox => {
                if(valueBox.getValue.getClass.getName.equals("soot.jimple.ThisRef")){
                  valueBox.setValue(new ThisRef(reifyClass.getType))
                } else if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")){
                  val paraNumber = valueBox.getValue.toString().charAt(10)
                  if(reifyType.isInstanceOf[ArrayType])
                    valueBox.setValue(new ParameterRef(reifyType.asInstanceOf[ArrayType].getElementType,
                      paraNumber.toInt-48))
                  else
                    valueBox.setValue(new ParameterRef(reifyType,paraNumber.toInt-48))
                }
              })
            }
          }
          // assign stmt, like =
          else if(unit.getClass.getName.equals("soot.jimple.internal.JAssignStmt")){
            val jAssignStmt = unit.asInstanceOf[JAssignStmt]
            jAssignStmt.getUseAndDefBoxes.foreach(valueBox => {
              val value = valueBox.getValue()
              if(value.isInstanceOf[FieldRef]){
                val ref = value.asInstanceOf[FieldRef]
                val field = reifyClass.getFieldByName(ref.getField.getName)
                val newSRF = SootHelper.makeFieldRef(field, context)
                ref.setFieldRef(newSRF)
              }
            })
          }
          // invoke stmt, like special invoke
          else if(unit.getClass.getName.equals("soot.jimple.internal.JInvokeStmt")){

          }
        }
      }
    }

    // method further optimize
    val methodFurtherOptimizeNew = new ArrayList[SootMethod]

    for( method <- reifyClass.getMethods if(methodFurtherOptimize.map(_._1).contains(method.getName))) {

      // get the invoke method which has real body in extend classes
      val hasMethodBodyMethod = methodFurtherOptimize.filter(_._1.equals(method.getName)).last._2
      val hasMethodBodyClasses = extendClassAndMethodList
        .filter(_._2.equals(hasMethodBodyMethod)).map(_._1)
      val hasMethodBodyClass = hasMethodBodyClasses.filter(p => {
        val invokeClass = context.sootClass(p)
        val reifyMethodInInvokeClasses = invokeClass.getMethods.filter(_.getName == "call")
          .filter(_.getParameterTypes.forall(!_.toString.equals("java.lang.Object")))
        if (reifyMethodInInvokeClasses.length == 0)
          false
        else {
          val reifyMethodInInvokeClass = reifyMethodInInvokeClasses.last
          if (reifyMethodInInvokeClass.getParameterType(0).toString.contains(reifyType.toString))
            true
          else false
        }
      }).last
      val invokeMethod = context.sootClass(hasMethodBodyClass).getMethods.filter(_.getName == "call")
        .filter(_.getParameterTypes.forall(!_.toString.equals("java.lang.Object"))).last

      // add new method according to the invoke method
      val newFurtherMethod = new SootMethod("_" + method.getName, invokeMethod.getParameterTypes,
        invokeMethod.getReturnType, invokeMethod.getModifiers, invokeMethod.getExceptions)
      newFurtherMethod.setDeclared(false)
      methodFurtherOptimizeNew.add(newFurtherMethod)

      // locals of new method
      newFurtherMethod.setActiveBody(Utils.cloneSootBody(invokeMethod.getActiveBody))
      val localIt = newFurtherMethod.getActiveBody.getLocals.iterator()
      while (localIt.hasNext) {
        val local = localIt.next()
        if (local.getType.toString.equals(invokeMethod.getDeclaringClass.getName))
          local.setType(reifyClass.getType)
        else if (local.getType.toString.equals(className))
          local.setType(reifyClass.getType)
      }

      // body of new method
      for(unit <- newFurtherMethod.getActiveBody.getUnits){
        if(unit.isInstanceOf[JIdentityStmt]){
          val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
          if(jIdentityStmt.getRightOp.getType.toString.equals(invokeMethod.getDeclaringClass.getName)){
            jIdentityStmt.getUseAndDefBoxes.foreach(valueBox => {
              if(valueBox.getValue.getClass.getName.equals("soot.jimple.ThisRef"))
                valueBox.setValue(new ThisRef(reifyClass.getType))
              else if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")) {
                val paraNumber = valueBox.getValue.toString().charAt(10)
                valueBox.setValue(new ParameterRef(method.getParameterType(paraNumber.toInt-48),
                  paraNumber.toInt-48))
              }
            })
          }
        } else if(unit.isInstanceOf[JAssignStmt]){

        } else if(unit.isInstanceOf[JInvokeStmt]){
          val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
          val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
          if(invokeMethodRef.declaringClass().getName.equals(className)){
            jInvokeStmt.getInvokeExpr
              .setMethodRef(reifyClass.getMethodByName(invokeMethodRef.name()).makeRef())
          }
        }
      }

      // return type of new method
      if (newFurtherMethod.getReturnType.toString.equals(className)) {
        newFurtherMethod.setReturnType(reifyClass.getType)
      } else if (newFurtherMethod.getReturnType.toString.equals("java.lang.Object")) {
        if (reifyType.isInstanceOf[ArrayType])
          newFurtherMethod.setReturnType(reifyType.asInstanceOf[ArrayType].getElementType)
        else
          newFurtherMethod.setReturnType(reifyType)
      } else if (newFurtherMethod.getReturnType.toString.equals("java.lang.Object[]")) {
        newFurtherMethod.setReturnType(reifyType)
      }
    }

    // add the new methods to reifyClass
    methodFurtherOptimizeNew.foreach(reifyClass.addMethod(_))

    for(method <- reifyClass.getMethods if(methodFurtherOptimize.map(_._1).contains(method.getName))){
      //  then we can change the origin method about the new method through methodRef
      for(unit <- method.getActiveBody.getUnits){
        if(unit.isInstanceOf[JAssignStmt]){
          val jAssignStmt = unit.asInstanceOf[JAssignStmt]
          val rightOpBox = jAssignStmt.getRightOpBox
          if(rightOpBox.getValue.isInstanceOf[JInterfaceInvokeExpr]){
            val jInterfaceInvokeExpr = rightOpBox.getValue.asInstanceOf[JInterfaceInvokeExpr]
            rightOpBox.getValue.getUseBoxes.foreach(valueBox => {
              if(valueBox.isInstanceOf[JimpleLocalBox]){
                val thisRefInMethod = method.getActiveBody.getUnits
                  .filter(_.isInstanceOf[JIdentityStmt])
                  .map(_.asInstanceOf[JIdentityStmt])
                  .filter(_.getRightOp.isInstanceOf[ThisRef])
                  .filter(_.getRightOp.getType.toString.equals(reifyClass.getName)).last.getLeftOp
                valueBox.setValue(thisRefInMethod)
              }
            })
            jInterfaceInvokeExpr.setMethodRef(reifyClass.getMethodByName("_"+method.getName).makeRef())
            rightOpBox.setValue(new JVirtualInvokeExpr(jInterfaceInvokeExpr.getBase,
              jInterfaceInvokeExpr.getMethodRef,jInterfaceInvokeExpr.getArgs))

            val leftOpBox = jAssignStmt.getLeftOpBox
            if(!leftOpBox.getValue.getType.toString
              .equals(jInterfaceInvokeExpr.getMethod.getReturnType.toString)){
              for(local <- method.getActiveBody.getLocals){
                if(local.getName.equals(leftOpBox.getValue.toString())) {
                  local.setType(jInterfaceInvokeExpr.getMethod.getReturnType)
                }
              }
            }
          }
        } else if(unit.isInstanceOf[JIdentityStmt]){
          val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
          val rightType = jIdentityStmt.getRightOp.getType
          if(rightType.equals(appClass.getType)){
            unit.getUseBoxes.foreach(valueBox => {
              if(valueBox.getValue.getClass.getName.equals("soot.jimple.ThisRef")){
                valueBox.setValue(new ThisRef(reifyClass.getType))
              } else if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")){
                val paraNumber = valueBox.getValue.toString().charAt(10)
                valueBox.setValue(new ParameterRef(method.getParameterType(paraNumber.toInt-48),
                  paraNumber.toInt-48))
              }
            })
          }
        }

      }
    }

    // tailor myself because many fields or units contain the origin class we don't need
    // 1.change the units about outer to NULL or nullMethod in <init>
    val initMethod = reifyClass.getMethodByName("<init>")

    val toRemove = new ArrayList[Unit]
    val toRemoveLocals = new ArrayList[Local]
    for(local <- initMethod.getActiveBody.getLocals){
      if(extendClasses.contains(local.getType.toString)) {
        toRemoveLocals.add(local)
        for(unit <- initMethod.getActiveBody.getUnits){
          if(!unit.getUseAndDefBoxes.forall(!_.getValue.toString().equals(local.getName))) {
            toRemove.add(unit)
            if(unit.getBoxesPointingToThis.length!=0){
              unit.getBoxesPointingToThis.foreach(u => toRemove.add(u.getUnit))
            }
          }
        }
      } else if(local.getType.toString.equals("java.lang.Class") || local.getType.toString.equals("java.lang.String")){
        for(unit <- initMethod.getActiveBody.getUnits){
          if(unit.isInstanceOf[JAssignStmt]){
            if(unit.asInstanceOf[JAssignStmt].getLeftOp.toString().equals(local.getName)){
              val jAssigStmt = unit.asInstanceOf[JAssignStmt]
              val rightOp = jAssigStmt.getRightOp
              if(rightOp.isInstanceOf[JVirtualInvokeExpr]){
                val rightMethodRef = rightOp.asInstanceOf[JVirtualInvokeExpr].getMethodRef
                if(rightMethodRef.declaringClass().getName.equals("java.lang.Object") &&
                   rightMethodRef.name().equals("getClass")){
                  toRemoveLocals.add(local)
                  toRemove.add(unit)
                }
                if(rightMethodRef.declaringClass().getName.equals("java.lang.Class") &&
                  (rightMethodRef.name().equals("getComponentType") ||
                    rightMethodRef.name().equals("getSimpleName"))){
                  toRemoveLocals.add(local)
                  toRemove.add(unit)
                }
                if(rightMethodRef.declaringClass().getName.equals("java.lang.String") &&
                  rightMethodRef.name().equals("equals")){
                  toRemoveLocals.add(local)
                  toRemove.add(unit)
                }
              }
            }
          }
        }
      } else if(local.getType.toString.equals("boolean")){
        toRemoveLocals.add(local)
        for(unit <- initMethod.getActiveBody.getUnits){
          if(!unit.getUseAndDefBoxes.forall(!_.getValue.toString().equals(local.getName))){
            toRemove.add(unit)
          } else if(unit.isInstanceOf[JGotoStmt]){
            toRemove.add(unit)
          }
        }
      }
    }

    toRemoveLocals.foreach(initMethod.getActiveBody.getLocals.remove(_))
    toRemoveLocals.clear()
    toRemove.foreach(initMethod.getActiveBody.getUnits.remove(_))
    toRemove.clear()

    // 2.change other method
    for(method <- reifyClass.getMethods if !methodFurtherOptimizeNew.map(_.getName).contains(method.getName)){
      for(unit <- method.getActiveBody.getUnits){
        if(unit.toString().contains("_"+method.getName)){
          if(unit.isInstanceOf[JAssignStmt]){
            val rightOp = unit.asInstanceOf[JAssignStmt].getRightOp
            if(rightOp.isInstanceOf[FieldRef]) {
              toRemove.add(unit)
              val leftOp = unit.asInstanceOf[JAssignStmt].getLeftOp
              toRemoveLocals.add(method.getActiveBody.getLocals.filter(_.getName.equals(leftOp.toString())).last)
            }
          }
        }
      }
      toRemoveLocals.foreach(method.getActiveBody.getLocals.remove(_))
      toRemoveLocals.clear()
      toRemove.foreach(method.getActiveBody.getUnits.remove(_))
      toRemove.clear()
    }

    // 3.tailor
    extendClasses.foreach( c => context.removeClass(context.sootClass(c)))
    /**
    val removeFields = new ArrayList[SootField]
    for(field <- reifyClass.getFields){
      if(extendClassAndMethodList.map(_._2).contains(field.getName))
        removeFields.add(field)
    }
    removeFields.foreach(reifyClass.removeField(_))
    */
    context.applicationClasses.add(reifyClass)
    println("ReifierClass " + reifyClass.getName + " build success.")
  }

  def getReifyTypeInMethod(method:SootMethod,context:Context){
    val methodBody = method.getActiveBody
    for (unit <- methodBody.getUnits) {
      println("--"+unit.toString())
      if (unit.getClass.getName.equals("soot.jimple.internal.JInvokeStmt")) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        val invokeMethod = jInvokeStmt.getInvokeExpr.getMethod
        // whether this unit has genericity, if yes, get the genericity class
        var invokeClassName = ""
        val hasGenericity = !jInvokeStmt.getUseAndDefBoxes.
          forall(valueBox => {
          if (genericityClasses.contains(valueBox.getValue.getType.toString())) {
            invokeClassName = valueBox.getValue.getType.toString()
            false
          } else true
        })
        //whether this unit can reify type
        val hasReifyType = jInvokeStmt.getInvokeExpr.toString().contains("java.lang.Object")

        // this unit can get reifyType, get it and convert the unit
        if (hasGenericity & hasReifyType) {

          // get the reifyType
          val invokeMethodParamTypes = invokeMethod.getParameterTypes.toBuffer
          val reifyBox = jInvokeStmt.getUseAndDefBoxes.filter(valueBox => {
            val valueType = valueBox.getValue.getType
            if (valueType.toString().equals(invokeClassName))
              false
            else if (valueType.toString().equals("void"))
              false
            else if (invokeMethodParamTypes.contains(valueType)) {
              invokeMethodParamTypes -= valueType
              false
            } else
              true
          }).get(0)

          val reifyType = reifyBox.getValue.getType
          val hasArrayType = !context.sootClass(invokeClassName).getFields.
            forall(!_.getType.toString.equals("java.lang.Object[]"))
          if ((hasArrayType && reifyType.isInstanceOf[ArrayType])
            || (!hasArrayType && !reifyType.isInstanceOf[ArrayType])) {
            reifier_type.add(reifyType)
            return
            //reify(invokeClassName, context, reifyType)
          }
        }else {
          if (!invokeMethod.getName.equals("<init>")
            && !invokeMethod.getDeclaringClass.isPhantomClass
            && reifier_type.length==0) {
            getReifyTypeInMethod(invokeMethod, context)
          }
        }
      }
    }
  }

  def reifyProject(context:Context){
    // build new class
    reifyWithNewClass(genericityClasses.get(0),context,reifier_type.get(0))
    // reify class from main class
    reifyMainClassGivenType(context.mainClass,genericityClasses.get(0),reifier_type.get(0),context)
  }

  def reifyMainClassGivenType(className:String,invokeClassName:String,reifyType:Type,context:Context){

    val reifyClass = context.sootClass(invokeClassName+"AS"+REIFIER_MAP(reifyType.toString))
    val mainClass = context.sootClass(className)

    for(field <- mainClass.getFields){
      if(field.getType.toString().equals(invokeClassName)){
        field.setType(reifyClass.getType)
      }else {
        if(field.getType.getClass.getName.equals("soot.RefType")){
          val refClassName = field.getType.toString
          if(!context.sootClass(refClassName).isPhantom)
            reifyClassGivenType(refClassName,invokeClassName,reifyType,context)
        }
        else if(field.getType.getClass.getName.equals("soot.ArrayType")) {
          val refClassName = field.getType.toString().subSequence(0,field.getType.toString().length-2).toString
          reifyClassGivenType(refClassName,invokeClassName,reifyType,context)
        }
      }
    }
    REIFIEDCLASS.add(mainClass.getName)

    for(method <- mainClass.getMethods){
      reifyMethodGivenType(method,invokeClassName,reifyType,context)
    }

  }

  def reifyMethodGivenType(method:SootMethod,invokeClassName:String,reifyType:Type,context:Context){

    val reifyClass = context.sootClass(invokeClassName+"AS"+REIFIER_MAP(reifyType.toString))
    val methodBody = method.getActiveBody

    val localIt = methodBody.getLocals.iterator()
    while(localIt.hasNext){
      val local = localIt.next()
      if(local.getType.toString.equals(invokeClassName))
        local.setType(reifyClass.getType)
    }

    val parameterArray = method.getParameterTypes.toBuffer
    for(i <- 0 until parameterArray.length if parameterArray.length!=0){
      if(parameterArray(i).toString.equals(invokeClassName)){
        parameterArray.update(i,reifyClass.getType)
      }
    }
    method.setParameterTypes(parameterArray.toList)

    for(unit <- methodBody.getUnits){
      if(unit.getClass.getName.equals("soot.jimple.internal.JIdentityStmt")){
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        val rightType = jIdentityStmt.getRightOp.getType

        if(rightType.toString.equals(invokeClassName)){
          unit.getUseBoxes.foreach(valueBox => {
            if(valueBox.getValue.getClass.getName.equals("soot.jimple.ParameterRef")){
              val paraNumber = valueBox.getValue.toString().charAt(10)
              valueBox.setValue(new ParameterRef(reifyClass.getType, paraNumber.toInt-48))
            }
          })
        }
      } else if(unit.getClass.getName.equals("soot.jimple.internal.JAssignStmt")){

        val jAssignStmt = unit.asInstanceOf[JAssignStmt]

        for(valueBox <- jAssignStmt.getUseAndDefBoxes){
          val value = valueBox.getValue()
          if(value.getType.toString.equals(invokeClassName)){
            if(value.isInstanceOf[FieldRef]){
              val ref = value.asInstanceOf[FieldRef]
              if(method.getDeclaringClass.getName.equals(invokeClassName)) {
                val field = reifyClass.getField(ref.getFieldRef.name(), reifyClass.getType)
                ref.setFieldRef(SootHelper.makeFieldRef(field, context))
              }else {
                if(!REIFIEDCLASS.contains(ref.getFieldRef.declaringClass().getName))
                  reifyClassGivenType(ref.getFieldRef.declaringClass().getName,invokeClassName,reifyType,context)
                val field = ref.getFieldRef.declaringClass().getField(ref.getFieldRef.name(), reifyClass.getType)
                ref.setFieldRef(SootHelper.makeFieldRef(field, context))
              }
            } else if(value.isInstanceOf[JNewExpr]){
              val jNewExpr = value.asInstanceOf[JNewExpr]
              jNewExpr.setBaseType(reifyClass.getType)
            } else if(value.isInstanceOf[JVirtualInvokeExpr]){
              val jVirtualInvokeExpr = value.asInstanceOf[JVirtualInvokeExpr]
              if(jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(invokeClassName)){
                jVirtualInvokeExpr.setMethodRef(reifyClass.getMethodByName(jVirtualInvokeExpr.getMethodRef.name()).makeRef())
              }else{
                val jInvokeClass = jVirtualInvokeExpr.getMethodRef.declaringClass()
                if(!REIFIEDCLASS.contains(jInvokeClass.getName)){
                  reifyClassGivenType(jInvokeClass.getName,invokeClassName,reifyType,context)
                }
                jVirtualInvokeExpr.setMethodRef(jInvokeClass.getMethodByName(jVirtualInvokeExpr.getMethodRef.name()).makeRef())
              }
            }
          }else{
            if(value.isInstanceOf[JVirtualInvokeExpr]){
              val jVirtualInvokeExpr = value.asInstanceOf[JVirtualInvokeExpr]
              if(jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(invokeClassName)){
                jVirtualInvokeExpr.setMethodRef(reifyClass.getMethodByName(jVirtualInvokeExpr.getMethodRef.name()).makeRef())
              }
            } else if(value.isInstanceOf[JInstanceFieldRef]){
              val jInstanceFieldRef = value.asInstanceOf[JInstanceFieldRef]
              if(jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(invokeClassName)){
                jInstanceFieldRef.setFieldRef(reifyClass.getFieldByName(jInstanceFieldRef.getFieldRef.name()).makeRef())
              }
            }
          }
        }
      } else if(unit.getClass.getName.equals("soot.jimple.internal.JInvokeStmt")){
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
        if(invokeMethodRef.declaringClass().getName.equals(invokeClassName)){
          jInvokeStmt.getInvokeExpr
            .setMethodRef(reifyClass.getMethodByName(invokeMethodRef.name()).makeRef())
        } else{
          if(!jInvokeStmt.getInvokeExpr.toString().contains("java.lang.Object: void <init>()")
            && !jInvokeStmt.getInvokeExpr.getMethodRef.declaringClass().isPhantom) {
            if (!REIFIEDCLASS.contains(method.getDeclaringClass.getName)) {
              reifyClassGivenType(invokeMethodRef.declaringClass().getName, invokeClassName, reifyType, context)
            }
            jInvokeStmt.getInvokeExpr
              .setMethodRef(invokeMethodRef.declaringClass().getMethodByName(invokeMethodRef.name()).makeRef())
          }
        }
      } else if(unit.getClass.getName.equals("soot.jimple.internal.JReturnStmt")){

      }
    }

  }

  def reifyClassGivenType(className:String,invokeClassName:String,reifyType:Type,context:Context){

    val reifyClass = context.sootClass(invokeClassName+"AS"+REIFIER_MAP(reifyType.toString))
    val currentClass = context.sootClass(className)

    for(field <- currentClass.getFields){
      if(field.getType.toString.equals(invokeClassName)){
        field.setType(reifyClass.getType)
      }
    }

    REIFIEDCLASS.add(className)

    for(method <- currentClass.getMethods){
      reifyMethodGivenType(method,invokeClassName,reifyType,context)
    }

  }

  def transformCallGraph(context:Context){

    context.buildCallGraph()

    val callGraph = context.callGraph
    val newEdges = new ArrayList[Edge]
    val appClassNames = new ArrayList[String]
    for(appClass <- context.applicationClasses){
      appClassNames.add(appClass.getName)
    }

    // unitsInCG means ( src Unit, src Stmt, target Method)
    for( appClass <- context.applicationClasses; method <- appClass.getMethods){
      val unitsInCG = callGraph.iterator().filter(_.src().getName.equals(method.getName))
        .map(u => (u.srcUnit(),u.srcStmt(),u.tgt().getName))

      if(method.hasActiveBody) {
        for (unit <- method.getActiveBody.getUnits) {
          if (!unitsInCG.map(_._1).contains(unit)) {

            def hasInvokeExpr = {
              if (!unit.getUseAndDefBoxes.forall(!_.getValue.isInstanceOf[JVirtualInvokeExpr]))
                true
              else false
            }

            if (hasInvokeExpr) {
              val invokeExprBox = unit.getUseAndDefBoxes.filter(_.getValue.isInstanceOf[JVirtualInvokeExpr]).last
              val invokeExpr = invokeExprBox.getValue.asInstanceOf[JVirtualInvokeExpr]
              val invokeMethod  = invokeExpr.getMethod
              if(appClassNames.contains(invokeMethod.getDeclaringClass.getName)){
                if(!unitsInCG.map(_._3).contains(invokeMethod.getName)){
                  val addNewEdge = new Edge(method,unit.asInstanceOf[Stmt],invokeMethod)
                  newEdges.add(addNewEdge)
                }
              }
            }

          }
        }
      }
    }

    newEdges.foreach(callGraph.addEdge(_))

  }

}
