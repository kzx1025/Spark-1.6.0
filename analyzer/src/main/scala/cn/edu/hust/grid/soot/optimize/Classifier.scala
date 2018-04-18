package cn.edu.hust.grid.soot.optimize

import cn.edu.hust.grid.soot.optimize.SizeType._
import soot.jimple.FieldRef
import soot.jimple.internal.JAssignStmt
import soot.{ArrayType, RefType}

import scala.collection.JavaConversions._

/**
  * Created by Administrator on 2015/7/21.
  */
object Classifier extends Transformer {
  override def transform(context: Context): Unit = {
    for (className <- context.decomposeWorkingList) {
      classify(className, context)
    }
  }

  private def classify(className: String, context: Context) {
    if (!context.classifyMap.contains(className)) {
      if (isRecursiveType(className, context)) {
        //println("VIII:"+className)
        context.classifyMap.put(className, SizeType.UNDEFINED_SIZE)
      } else {
        directClassify(className: String, context: Context)
      }
    }
  }

  private def internalClassify(className: String, context: Context): SizeType = {
    context.classifyMap.getOrElse(className, directClassify(className, context))
  }

  private def directClassify(className: String, context: Context): SizeType = {
    if (className.equals("int") || className.equals("double") || className.equals("long"))
      return SizeType.STATIC_FIXED_SIZE
    val appClass = context.sootClass(className)
    if (appClass.isPhantom || !appClass.isApplicationClass)
      return SizeType.STATIC_FIXED_SIZE
    val numOfArrayType = appClass.getFields.filter(_.getType.isInstanceOf[ArrayType]).size
    if (numOfArrayType == 0) {
      val typeInClass = appClass.getFields.filter(_.getType.isInstanceOf[RefType]).
        map(_.getType.asInstanceOf[RefType].getClassName).
        toSet[String].map(internalClassify(_, context))
      val isStatic = typeInClass.forall(_ == SizeType.STATIC_FIXED_SIZE)
      if (isStatic) {
        //println("I:"+className)
        context.classifyMap.put(className, SizeType.STATIC_FIXED_SIZE)
        SizeType.STATIC_FIXED_SIZE
      } else {
        val isRuntime = typeInClass.filter(_ != SizeType.STATIC_FIXED_SIZE).forall(_ == SizeType.RUNTIME_FIXED_SIZE)
        if (isRuntime) {
          //println("II:"+className)
          context.classifyMap.put(className, SizeType.RUNTIME_FIXED_SIZE)
          SizeType.RUNTIME_FIXED_SIZE
        } else {
          val isVariable = typeInClass.
            filter(s => if ((s != SizeType.STATIC_FIXED_SIZE) && (s != SizeType.RUNTIME_FIXED_SIZE)) true else false).
            forall(_ == SizeType.VARIABLE_SIZE)
          if (isVariable) {
            //println("III:"+className)
            context.classifyMap.put(className, SizeType.VARIABLE_SIZE)
            SizeType.VARIABLE_SIZE
          } else {
            //println("IV:"+className)
            context.classifyMap.put(className, SizeType.UNDEFINED_SIZE)
            SizeType.UNDEFINED_SIZE
          }
        }
      }
    } else {
      val sizeOfNoAssignableField = appClass.getFields.
        filter(_.getType.isInstanceOf[ArrayType]).
        filter(s => isNoAssignableByField(className, s.getName, context)).size
      if (sizeOfNoAssignableField == numOfArrayType) {
        val isAllStatic = appClass.getFields.filter(_.getType.isInstanceOf[ArrayType])
          .map(_.getType.asInstanceOf[ArrayType].getElementType.toString)
          .map(t => context.classifyMap.getOrElse(t, directClassify(t, context)))
          .forall(_ == SizeType.STATIC_FIXED_SIZE)
        if (isAllStatic) {
          //println("V:"+className)
          context.classifyMap.put(className, SizeType.RUNTIME_FIXED_SIZE)
          SizeType.RUNTIME_FIXED_SIZE
        } else {
          //println("VI:"+className)
          context.classifyMap.put(className, SizeType.VARIABLE_SIZE)
          SizeType.VARIABLE_SIZE
        }
      } else {
        //println("VII:"+className)
        context.classifyMap.put(className, SizeType.VARIABLE_SIZE)
        SizeType.VARIABLE_SIZE
      }

    }
  }

  private def isRecursiveType(className: String, context: Context): Boolean = {
    val visited = collection.mutable.HashSet.empty[String]
    val edges = collection.mutable.HashSet.empty[(String, String)]
    var isDAG = true

    def visit(className: String) {
      val primeType = className.equals("int") || className.equals("double") || className.equals("float") || className.equals("long")
      if (!primeType && !context.sootClass(className).isPhantom && context.sootClass(className).isApplicationClass) {
        visited.add(className)
        val appClass = context.sootClass(className)
        for (fieldClassName <- appClass.getFields.filter(_.getType.isInstanceOf[RefType]).
          map(_.getType.asInstanceOf[RefType].getClassName).toSet[String]) {
          edges.add((className, fieldClassName))
          if (!visited.contains(fieldClassName)) {
            visit(fieldClassName)
          }
        }
        for (arrayFieldClassName <- appClass.getFields.filter(_.getType.isInstanceOf[ArrayType]).
          map(_.getType.asInstanceOf[ArrayType].getElementType.toString).toSet[String]) {
          edges.add((className, arrayFieldClassName))
          if (!visited.contains(arrayFieldClassName)) {
            visit(arrayFieldClassName)
          }
        }
      }
    }

    visit(className)
    //println("visited:"+visited.mkString(";"))

    var points = visited.map(t => (t, 0))

    def DFSForCircuit(className: String): Unit = {
      points = points.filter(!_._1.equals(className)).+=((className, -1))
      for (edge <- edges) {
        if (edge._1.equals(className)) {
          if (points.contains((edge._2, -1))) {
            isDAG = false
            return
          } else if (points.contains((edge._2, 0)))
            DFSForCircuit(edge._2)
          else
            return
        }
      }
      points = points.filter(!_._1.equals(className)).+=((className, 1))
    }

    DFSForCircuit(className)
    !isDAG
  }

  private def isNoAssignableByField(className: String, fieldName: String, context: Context): Boolean = {
    val appClass = context.sootClass(className)
    var result = true
    val field = appClass.getFieldByName(fieldName)
    if (field.isPublic)
      result = false
    else {
      for (method <- appClass.getMethods if (!method.getName.contains("<init>")) && (!method.isNative) && (method.hasActiveBody)) {
        for (assign@(_a: JAssignStmt) <- method.getActiveBody.getUnits) {
          val leftOp = assign.getLeftOp
          if (leftOp.isInstanceOf[FieldRef]) {
            val fieldRef = leftOp.asInstanceOf[FieldRef]
            if (fieldRef.getFieldRef.name().equals(fieldName) && fieldRef.getFieldRef.declaringClass().equals(className))
              result = false
          }
        }
      }
    }
    result
  }

}
