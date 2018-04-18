package cn.edu.hust.grid.soot.optimize

import java.util

import cn.edu.hust.grid.soot.Utils
import soot.jimple.internal._
import soot.jimple.{ParameterRef, ThisRef}
import soot.{Unit => SootUnit, _}

import scala.collection.JavaConversions._

/**
  * Created by Administrator on 2015/8/5.
  */
object SootHelper {
  def printUnit(unit: SootUnit) = println(unit.getClass.getName + ": " + unit)

  def printBody(body: Body) = body.getUnits.foreach(printUnit)

  def printClass(sl: SootClass) = sl.getMethods.map(_.getActiveBody).foreach(printBody)

  def makeMethodRef(method: SootMethod, context: Context) = context.scene.makeMethodRef(
    method.getDeclaringClass,
    method.getName,
    method.getParameterTypes,
    method.getReturnType,
    method.isStatic)

  def makeFieldRef(field: SootField, context: Context) = context.scene.makeFieldRef(
    field.getDeclaringClass,
    field.getName,
    field.getType,
    field.isStatic)

  /**
    * 只针对闭包函数克隆，因此可以认为该方法内无其他field，唯一的外部引用来自于outer对象
    * 且该闭包对象没有调用本类的其他方法，如果调用，则会出错
    * 再修复过后闭包对象可调用本类的其他方法，该方法会递归克隆调用到的所有方法
    * 但是方法体内引用了类的成员变量的话不知道该如何赋值？
    *
    * @param oldMethod
    * @param oldSootClass
    * @param newSootClass
    * @return
    */
  def cloneMethod(oldMethod: SootMethod, oldSootClass: SootClass, newSootClass: SootClass): SootMethod = {
    val localMethodBody = oldMethod.getActiveBody
    val newMethod = new SootMethod(oldMethod.getName, oldMethod.getParameterTypes, oldMethod.getReturnType,
      oldMethod.getModifiers, oldMethod.getExceptions)
    newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
    val newMethodBody = newMethod.retrieveActiveBody()

    for (local <- newMethodBody.getLocals) {
      if (local.getType.toString.equals(oldSootClass.getName)) {
        local.setType(newSootClass.getType)
      }
    }

    for (unit <- newMethodBody.getUnits) {
      if (unit.isInstanceOf[JIdentityStmt]) {
        val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
        if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
          jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
        }
      } else if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val field = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].getField
          val fieldName = field.getName
          if (field.getDeclaringClass == oldSootClass) {
            if (!newSootClass.getFields.exists(_.getName == fieldName)) {
              val copyFiled = Utils.cloneSootField(field)
              newSootClass.addField(copyFiled)
            }
            val newFieldRef = newSootClass.getFieldByName(fieldName).makeRef()
            jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].setFieldRef(newFieldRef)
          }
        }
      }
    }

    for (unit <- newMethodBody.getUnits) {
      if (unit.isInstanceOf[JAssignStmt]) {
        val jAssignStmt = unit.asInstanceOf[JAssignStmt]
        if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]
          if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
            val invokeName = jVirtualInvokeExpr.getMethodRef.name()
            val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
            if (!newSootClass.getMethods.exists(m => m.getName == invokeName &&
              m.getParameterCount == jVirtualInvokeExpr.getMethod.getParameterCount)) {
              val copyMethod = cloneMethod(jVirtualInvokeExpr.getMethod, oldSootClass, newSootClass)
              if (!newSootClass.getMethods.exists(m => m.getName == invokeName &&
                m.getParameterCount == jVirtualInvokeExpr.getMethod.getParameterCount)) {
                newSootClass.addMethod(copyMethod)
              }
            }
            val newMethodRef = newSootClass.getMethod(invokeName, invokeParameter).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        } else if (jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
          val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]
          if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
            val invokeName = jVirtualInvokeExpr.getMethodRef.name()
            val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
            if (!newSootClass.getMethods.exists(m => m.getName == invokeName &&
              m.getParameterCount == jVirtualInvokeExpr.getMethod.getParameterCount)) {
              val copyMethod = cloneMethod(jVirtualInvokeExpr.getMethod, oldSootClass, newSootClass)
              if (!newSootClass.getMethods.exists(m => m.getName == invokeName &&
                m.getParameterCount == jVirtualInvokeExpr.getMethod.getParameterCount)) {
                newSootClass.addMethod(copyMethod)
              }
            }
            val newMethodRef = newSootClass.getMethod(invokeName, invokeParameter).makeRef()
            jVirtualInvokeExpr.setMethodRef(newMethodRef)
          }
        } else if (jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]
          if (jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(oldSootClass.getName)) {
            val invokeName = jInstanceFieldRef.getFieldRef.name()
            if (!newSootClass.getFields.exists(_.getName == invokeName)) {
              val copyFiled = Utils.cloneSootField(jInstanceFieldRef.getField)
              newSootClass.addField(copyFiled)
            }
            val newFieldRef = newSootClass.getFieldByName(invokeName).makeRef()
            jInstanceFieldRef.setFieldRef(newFieldRef)
          }
        } else if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
          val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
          if (jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(oldSootClass.getName)) {
            val invokeName = jInstanceFieldRef.getFieldRef.name()
            if (!newSootClass.getFields.exists(_.getName == invokeName)) {
              val copyFiled = Utils.cloneSootField(jInstanceFieldRef.getField)
              newSootClass.addField(copyFiled)
            }
            val newFieldRef = newSootClass.getFieldByName(invokeName).makeRef()
            jInstanceFieldRef.setFieldRef(newFieldRef)
          }
        }
      } else if (unit.isInstanceOf[JInvokeStmt]) {
        val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
        val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
        if (invokeMethodRef.declaringClass().getName.equals(oldSootClass.getName)) {
          if (!newSootClass.getMethods.exists(m => m.getName == invokeMethodRef.name() &&
            m.getParameterCount == invokeMethodRef.resolve().getParameterCount)) {
            val copyMethod = cloneMethod(invokeMethodRef.resolve(), oldSootClass, newSootClass)
            if (!newSootClass.getMethods.exists(m => m.getName == invokeMethodRef.name() &&
              m.getParameterCount == invokeMethodRef.resolve().getParameterCount)) {
              newSootClass.addMethod(copyMethod)
            }
          }

          val newInvokeMethodRef = newSootClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
          jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
        }
      }
    }

    newMethod.setDeclaringClass(newSootClass)
    newSootClass.addMethod(newMethod)
    newMethod
  }

  def cloneClass(newClassName: String, modelTransformClass: SootClass, context: Context): SootClass = {

    val newSootClass = new SootClass(newClassName)
    newSootClass.setSuperclass(modelTransformClass.getSuperclass)
    modelTransformClass.getInterfaces.foreach(newSootClass.addInterface)

    for (localField <- modelTransformClass.getFields) {
      newSootClass.addField(Utils.cloneSootField(localField))
    }

    for (localMethod <- modelTransformClass.getMethods) {
      val localMethodBody = localMethod.getActiveBody
      val newMethod = new SootMethod(localMethod.getName, localMethod.getParameterTypes, localMethod.getReturnType,
        localMethod.getModifiers, localMethod.getExceptions)
      newMethod.setActiveBody(Utils.cloneSootBody(localMethodBody))
      newMethod.setDeclaringClass(newSootClass)
      newSootClass.addMethod(newMethod)
      val newMethodBody = newMethod.retrieveActiveBody()

      for (local <- newMethodBody.getLocals) {
        if (local.getType.toString.equals(modelTransformClass.getName)) {
          local.setType(newSootClass.getType)
        }
      }

      for (unit <- newMethodBody.getUnits) {
        if (unit.isInstanceOf[JIdentityStmt]) {
          val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
          if (jIdentityStmt.getRightOp.isInstanceOf[ThisRef]) {
            jIdentityStmt.setRightOp(new ThisRef(newSootClass.getType))
          }
        } else if (unit.isInstanceOf[JAssignStmt]) {
          val jAssignStmt = unit.asInstanceOf[JAssignStmt]
          if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
            val field = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].getField
            val fieldName = field.getName
            if (field.getDeclaringClass == modelTransformClass) {
              val newFieldRef = newSootClass.getFieldByName(fieldName).makeRef()
              jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef].setFieldRef(newFieldRef)
            }
          }
        }
      }

    }

    for (localMethod <- newSootClass.getMethods) {
      val newMethodBody = localMethod.getActiveBody
      for (unit <- newMethodBody.getUnits) {
        if (unit.isInstanceOf[JAssignStmt]) {
          val jAssignStmt = unit.asInstanceOf[JAssignStmt]
          if (jAssignStmt.getRightOp.isInstanceOf[JVirtualInvokeExpr]) {
            val jVirtualInvokeExpr = jAssignStmt.getRightOp.asInstanceOf[JVirtualInvokeExpr]
            if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(modelTransformClass.getName)) {
              val invokeName = jVirtualInvokeExpr.getMethodRef.name()
              val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
              val newMethodRef = newSootClass.getMethod(invokeName, invokeParameter).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }
          } else if (jAssignStmt.getLeftOp.isInstanceOf[JVirtualInvokeExpr]) {
            val jVirtualInvokeExpr = jAssignStmt.getLeftOp.asInstanceOf[JVirtualInvokeExpr]
            if (jVirtualInvokeExpr.getMethodRef.declaringClass().getName.equals(modelTransformClass.getName)) {
              val invokeName = jVirtualInvokeExpr.getMethodRef.name()
              val invokeParameter = jVirtualInvokeExpr.getMethodRef.parameterTypes()
              val newMethodRef = newSootClass.getMethod(invokeName, invokeParameter).makeRef()
              jVirtualInvokeExpr.setMethodRef(newMethodRef)
            }
          } else if (jAssignStmt.getLeftOp.isInstanceOf[JInstanceFieldRef]) {
            val jInstanceFieldRef = jAssignStmt.getLeftOp.asInstanceOf[JInstanceFieldRef]
            if (jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(modelTransformClass.getName)) {
              val invokeName = jInstanceFieldRef.getFieldRef.name()
              val newFieldRef = newSootClass.getFieldByName(invokeName).makeRef()
              jInstanceFieldRef.setFieldRef(newFieldRef)
            }
          } else if (jAssignStmt.getRightOp.isInstanceOf[JInstanceFieldRef]) {
            val jInstanceFieldRef = jAssignStmt.getRightOp.asInstanceOf[JInstanceFieldRef]
            if (jInstanceFieldRef.getFieldRef.declaringClass().getName.equals(modelTransformClass.getName)) {
              val invokeName = jInstanceFieldRef.getFieldRef.name()
              val newFieldRef = newSootClass.getFieldByName(invokeName).makeRef()
              jInstanceFieldRef.setFieldRef(newFieldRef)
            }
          }
        } else if (unit.isInstanceOf[JInvokeStmt]) {
          val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
          val invokeMethodRef = jInvokeStmt.getInvokeExpr.getMethodRef
          if (invokeMethodRef.declaringClass().getName.equals(modelTransformClass.getName)) {
            val newInvokeMethodRef = newSootClass.getMethod(invokeMethodRef.name(), invokeMethodRef.parameterTypes()).makeRef()
            jInvokeStmt.getInvokeExpr.setMethodRef(newInvokeMethodRef)
          } else if (invokeMethodRef.declaringClass().getName.startsWith(modelTransformClass.getName)) {
            val modifyClassName = invokeMethodRef.declaringClass().getName
            context.loadClass(modifyClassName, true)
            val modifyClass = context.sootClass(modifyClassName)
            //modifyClassFunction(modifyClass)
          }
        }
      }

    }

    def modifyClassFunction(goalClass: SootClass) {

      // first: modify the goal class
      val initMethod = goalClass.getMethodByName("<init>")
      val initMethodBody = initMethod.getActiveBody

      val parameters = initMethod.getParameterTypes
      val newParameters = new util.ArrayList[Type](parameters.size())
      for (i <- 0 until parameters.size()) {
        if (i == 0) {
          newParameters.add(newSootClass.getType)
        } else {
          newParameters.add(parameters(i))
        }
      }
      initMethod.setParameterTypes(newParameters)

      for (local <- initMethodBody.getLocals.snapshotIterator()) {
        if (local.getType.toString.equals(modelTransformClass.getName)) {
          local.setType(newSootClass.getType)
        }
      }

      for (unit <- initMethodBody.getUnits.snapshotIterator()) {
        if (unit.isInstanceOf[JIdentityStmt]) {
          val jIdentityStmt = unit.asInstanceOf[JIdentityStmt]
          if (jIdentityStmt.getRightOp.isInstanceOf[ParameterRef]) {
            val jPrameterRef = jIdentityStmt.getRightOp.asInstanceOf[ParameterRef]
            if (jPrameterRef.getIndex == 0)
              jIdentityStmt.setRightOp(new ParameterRef(newSootClass.getType, 0))
          }
        }
      }

      initMethodBody.getLocals.foreach(l => println("----" + l.getName + ":" + l.getType))
      initMethodBody.getUnits.foreach(u => println("----" + u.toString()))

    }

    newSootClass
  }
}
