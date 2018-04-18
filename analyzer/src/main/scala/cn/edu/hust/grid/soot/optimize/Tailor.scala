package cn.edu.hust.grid.soot.optimize

import soot.SootClass
import soot.jimple.FieldRef

import scala.collection.JavaConversions._

/**
  * Created by Administrator on 2015/7/21.
  */
object Tailor extends Transformer {

  override def transform(context: Context) {
    //context.validateTypeMatch()
    context.buildCallGraph()
    removeUnusedParts(context)
  }

  def transformClasses(context: Context, analyzeClasses: java.util.List[SootClass]): Unit = {
    // 首先将要裁剪的类的父类全部添加进来
    val allClasses = handleSuperClass(analyzeClasses)
    removeUnusedFields(context)
    removeUnusedMethods(context)
   // removeUnusedClasses(context)
    println("tailor completed!!!!")
  }


  private def removeUnusedParts(context: Context) {
    removeUnusedFields(context)
    removeUnusedMethods(context)
    removeUnusedClasses(context)
  }


  private def handleSuperClass(analyzeClasses: java.util.List[SootClass]): java.util.List[SootClass] = {
    val allClasses = new java.util.ArrayList[SootClass]()
    for (analyzeClass <- analyzeClasses){
      var currentClass: SootClass = analyzeClass
      while(currentClass != null){
        currentClass = currentClass.getSuperclassUnsafe
        if(currentClass!=null && !currentClass.getName.equals("java.lang.Object") && !allClasses.contains(currentClass)){
          allClasses.add(currentClass)
        }
      }
    }

    for(analyzeClass<-analyzeClasses){
      if(!allClasses.contains(analyzeClass)){
        allClasses.add(analyzeClass)
      }
    }

    allClasses
  }


  private def removeUnusedFields(context: Context) {
    val unusedFields = context.applicationClasses.flatMap(_.getFields).toBuffer
    context.applicationClasses.flatMap(_.getMethods).
      filter(_.hasActiveBody).
      filter(context.reachableMethods.contains(_)).
      map(_.getActiveBody).
      flatMap(_.getUseAndDefBoxes).
      map(_.getValue).
      foreach {
        case fieldRef: FieldRef => unusedFields -= fieldRef.getField
        case _ =>
      }

    for (unusedField <- unusedFields) {
      //      println("!--3:"+unusedField.getSignature)
      unusedField.getDeclaringClass.removeField(unusedField)
    }
  }

  private def removeUnusedFields(context: Context, analyzeClasses: java.util.List[SootClass]) {
    val unusedFields = analyzeClasses.flatMap(_.getFields).toBuffer
    analyzeClasses.flatMap(_.getMethods).
      filter(_.hasActiveBody).
      filter(context.reachableMethods.contains(_)).
      map(_.getActiveBody).
      flatMap(_.getUseAndDefBoxes).
      map(_.getValue).
      foreach {
        case fieldRef: FieldRef => unusedFields -= fieldRef.getField
        case _ =>
      }

    for (unusedField <- unusedFields) {
      //      println("!--3:"+unusedField.getSignature)
      unusedField.getDeclaringClass.removeField(unusedField)
    }
  }


  private def removeUnusedMethods(context: Context, analyzeClasses: java.util.List[SootClass]) {
    for (appClass <- analyzeClasses) {
      for (unusedMethod <- appClass.getMethods.filter(!context.reachableMethods.contains(_))) {
        //println("!--2:"+unusedMethod.getSignature)
        unusedMethod.getDeclaringClass.removeMethod(unusedMethod)
      }
    }
  }


  private def removeUnusedMethods(context: Context) {
    for (appClass <- context.applicationClasses) {
      for (unusedMethod <- appClass.getMethods.filter(!context.reachableMethods.contains(_))) {
        //println("!--2:"+unusedMethod.getSignature)
        if(!unusedMethod.getDeclaringClass.getName.endsWith("Platform")) {
          unusedMethod.getDeclaringClass.removeMethod(unusedMethod)
        }
      }
    }
  }

   def removeUnusedClasses(context: Context) {
    val unusedClasses = context.applicationClasses.
      filter(appClass => appClass.getFieldCount == 0 &&
        appClass.getMethodCount == 0)

    for (unusedClass <- unusedClasses) {
      //      println("!--1:"+unusedClass.getName())
        context.removeClass(unusedClass)
    }
  }
}
