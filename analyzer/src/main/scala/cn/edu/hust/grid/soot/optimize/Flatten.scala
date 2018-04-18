package cn.edu.hust.grid.soot.optimize

import java.util.ArrayList

import cn.edu.hust.grid.soot.Utils
import soot._
import soot.jimple.{FieldRef, _}
import soot.jimple.internal._

import scala.collection.JavaConversions._

/**
 * Created by zx on 15-11-30.
 */
object Flatten extends Transformer{

  override def transform(context: Context) {
    flatten(context)
  }

  /**flatten relative classes recursively*/
  private def flattenClasses(currentClass: SootClass, superClass: SootClass, context: Context) {
    /**if the superclass has the super class, it should be flattened firstly*/
    if(superClass.getSuperclass.getName != "java.lang.Object"){
      //println(appClass.getName+"&"+appClass.getSuperclass.getName)
      flattenClasses(superClass, superClass.getSuperclass, context)
    }

    /**transform the fields from the super class to the current class*/
    val supperFieldsIterator = superClass.getFields.iterator
    while(supperFieldsIterator.hasNext){
      val supperField=supperFieldsIterator.next
      if(!currentClass.getFields.contains(supperField) && !Utils.ContainSameNameOfSootField(currentClass.getFields, supperField.getName)){
        currentClass.addField(Utils.cloneSootField(supperField))
      }
    }

    /**transform the methods from the super class to the current class*/
    for(supperMethod <- superClass.getMethods){

      val currentClassMethodNamesContain = currentClass.getMethods.map(_.getName).contains(supperMethod.getName)
      val sameParameters = if(currentClassMethodNamesContain && supperMethod.getParameterCount != 0){
        currentClass.getMethods.filter(_.getName.equals(supperMethod.getName)).map(_.getParameterTypes).contains(supperMethod.getParameterTypes)
      }else false
      if(!currentClass.isPhantom
        && !currentClassMethodNamesContain
        && supperMethod.getName != "<init>"
        && !supperMethod.getDeclaringClass.isPhantom
        && supperMethod.hasActiveBody){
        /**------copy a new soot method from the original method--------------*/
        //change the parameter types to the current class
        val parameterTypes = supperMethod.getParameterTypes
        val newParameterTypes = new ArrayList[Type]
        for(parameter <- parameterTypes){
          if(parameter.toString == superClass.getType.toString)
            newParameterTypes.add(currentClass.getType)
          else
            newParameterTypes.add(parameter)
        }

        //supperMethod.setParameterTypes(Collections.unmodifiableList(newParameterTypes))
        val ct = new SootMethod(supperMethod.getName, newParameterTypes,
          supperMethod.getReturnType(), supperMethod.getModifiers(),
          supperMethod.getExceptions())
        ct.setDeclared(false)
        currentClass.addMethod(ct)

        ct.setActiveBody(Utils.cloneSootBody(supperMethod.getActiveBody))

        //transform the statement of supper class to the current class
        val methodBody = ct.retrieveActiveBody
        //change the type of the locals
        val localIt = methodBody.getLocals.iterator
        while (localIt.hasNext) {
          val local= localIt.next
          if(local.getType.toString == superClass.getType.toString){
            local.setType(currentClass.getType)
          }
        }
        //change the type of the identity statement and invoker statement
        for (unit <- methodBody.getUnits) {
          val unitType = unit.getClass.getName
          /*  if(supperMethod.getName == "dot")
               println(unitType)*/
          if(unitType == "soot.jimple.internal.JIdentityStmt"){
            val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
            val rightType = jIdentityStmt.getRightOp.getType
            if(rightType == superClass.getType){
              unit.getUseBoxes.foreach(valueBox =>
                if(valueBox.getValue.getClass.getName == "soot.jimple.ThisRef")
                  valueBox.setValue(new ThisRef(currentClass.getType))
                else if(valueBox.getValue.getClass.getName == "soot.jimple.ParameterRef"){
                  val paraNumber = valueBox.getValue.toString().charAt(10).toInt - 48
                  valueBox.setValue(new ParameterRef(currentClass.getType, paraNumber))
                }
              )
            }
          }
          else if(unitType == "soot.jimple.internal.JAssignStmt"){
            val jAssignStmt = unit.asInstanceOf[JAssignStmt]
            jAssignStmt.getUseAndDefBoxes.foreach(box => {
              val value = box.getValue
              if (value.isInstanceOf[FieldRef]) {
                val ref = value.asInstanceOf[FieldRef]
                if( currentClass.getFields.contains(ref.getField)) {
                  val field = currentClass.getFieldByName(ref.getField.getName)
                  val newSRF = SootHelper.makeFieldRef(field, context)
                  //println(newSRF)
                  ref.setFieldRef(newSRF)
                }
              }
              else if (value.isInstanceOf[JVirtualInvokeExpr]){
                val methodRef = value.asInstanceOf[JVirtualInvokeExpr]
                //val sootmethod = currentClass.getMethodByName(methodRef.getMethod.getName)
                val sameName = currentClass.getMethods.map(_.getName).contains(methodRef.getMethod.getName)
                val sameParameters = if(sameName)
                  currentClass.getMethods
                  .filter(_.getName.equals(methodRef.getMethod.getName))
                  .map(_.getParameterTypes)
                  .contains(methodRef.getMethod.getParameterTypes)
                else false
                val sameReturnType = if(sameName)
                  currentClass.getMethods
                    .filter(_.getName.equals(methodRef.getMethod.getName))
                    .map(_.getReturnType)
                    .contains(methodRef.getMethod.getReturnType)
                else false
                if(sameName && sameParameters && sameReturnType) {
                  val sootmethod = currentClass.getMethod(methodRef.getMethod.getName, methodRef.getMethod.getParameterTypes,methodRef.getMethod.getReturnType)
                  methodRef.setMethodRef(SootHelper.makeMethodRef(sootmethod, context))
                }
              }

            })
            //println(jAssignStmt.toString)
          }
          else{
            //To do something later
            //println(unitType)
          }
        }
      }
      else if( !currentClass.isPhantom
        && supperMethod.getName == "<init>"
        && currentClassMethodNamesContain
        && sameParameters
        && !supperMethod.getDeclaringClass.isPhantom
        && supperMethod.hasActiveBody ){
        /**------readjust the constructor of current class--------------*/
        val initMethodOfCurrent = currentClass.getMethod("<init>",supperMethod.getParameterTypes)
        //println(initMethodOfCurrent.getActiveBody)
        //change the init method of super class to some statements
        val targetBody = initMethodOfCurrent.getActiveBody
        for (unit <- targetBody.getUnits) {
          val unitType = unit.getClass.getName
          if(unitType == "soot.jimple.internal.JInvokeStmt"){  //JInvokeStmt
          val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
            //unit.getUseBoxes.foreach(v => println())

            val supperMethodBody = supperMethod.getActiveBody
            for (unitTwo <- supperMethodBody.getUnits) {
              val unitTypeTwo = unitTwo.getClass.getName
              if(unitTypeTwo == "soot.jimple.internal.JInvokeStmt"){
                val jInvokeStmtTwo = unitTwo.asInstanceOf[JInvokeStmt]
                //jInvokeStmt.getInvokeExprBox.setValue(jInvokeStmtTwo.getInvokeExprBox.getValue)
                jInvokeStmt.getInvokeExpr.setMethodRef(jInvokeStmtTwo.getInvokeExpr.getMethodRef)
              }
            }
          }
        }
      }
      else{

      }
      //to end
    }
  }

  private def flatten(context: Context) {

    /** remove the cloneable interfaces of all of classes */
    for (appClass <- context.applicationClasses) {
      val interfaces = appClass.getInterfaces.filter(interface =>
        interface.getName == "java.lang.Cloneable" ||
          (interface.isInScene && interface.getFieldCount > 0))
      appClass.getInterfaces.clear()
      appClass.getInterfaces.addAll(interfaces)
    }

    /** get the SootClass of "java.lang.Object" which is used for the inherited classes */
    val objectClass = context.classes.filter(clss => clss.getName == "java.lang.Object").seq.head
    //println(objectClass)

    /** remove the cloneable interfaces of all of classes */
    for (appClass <- context.applicationClasses) {
      //println(appClass.getName+"&"+appClass.getSuperclass.getName)
      if (appClass.getSuperclass.getName != "java.lang.Object") {
        //println(appClass.getName+"&"+appClass.getSuperclass.getName)
        //println(appClass.getType+"&"+appClass.getSuperclass.getType)
        flattenClasses(appClass, appClass.getSuperclass, context)
      }
    }

    /** change the supper class of the app class to java.lang.Object */
    for (appClass <- context.applicationClasses) {
      if (appClass.getSuperclass.getName != "java.lang.Object") {
        appClass.setSuperclass(objectClass)
      }
    }
  }
}
