package cn.edu.hust.grid.soot.optimize

import org.apache.spark.rdd.{RDD, ShuffledRDD}
import soot.jimple.internal._
import soot.{Unit => SootUnit, _}
import soot.jimple._

import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.util.control.Breaks
import Breaks.{break, breakable}

/**
 * Created by Administrator on 2015/7/21.
 */
object Decomposer {

  case class ClassInfo(
                        name: String,
                        totalSize: Int,
                        fieldOffsets: mutable.Map[String, (Int, Int, Int,Type)],
                        injection: mutable.Map[String, Array[String]]
                        ) extends Serializable

  case class PairInfo(
                       ktype: String,
                       vtype:String,
                       vitype: String
                       ) extends Serializable

  def decompose(decomposeClassName:String,mainClassName:String,context: Context): ClassInfo = {
    val appClass = context.sootClass(decomposeClassName)
    context.decomposeWorkingList.enqueue(decomposeClassName)
    Classifier.transform(context)
    val degenerateJudge =
      if(context.classifyMap.get(decomposeClassName).get == SizeType.RUNTIME_FIXED_SIZE) {
        degenerate(decomposeClassName, mainClassName, context)
      }
      else (0,false)
    if(!degenerateJudge._2)
      throw OptimizeException("Degenerate error.")

    val (totalSize, fieldOffsetMap) = computeFieldOffsets(appClass,degenerateJudge._1,context)
    val injectionInfoMap = doInjectionAnalysis(appClass, context)
    val info = ClassInfo(decomposeClassName, totalSize, fieldOffsetMap, injectionInfoMap)

    info
  }

  def decompose(rdd: RDD[_],context: Context): PairInfo ={

    val f= rdd.asInstanceOf[ShuffledRDD[_,_,_]]
    var field = f.getClass.getDeclaredField("aggregator")
    field.setAccessible(true)
    val f1 = field.get(f)
    field = f1.getClass.getDeclaredField("x")
    field.setAccessible(true)
    val f2 = field.get(f1)

    val valueField = f2.getClass.getDeclaredField("mergeValue")
    val combinersField = f2.getClass.getDeclaredField("mergeCombiners")
    val createCombinerField = f2.getClass.getDeclaredField("createCombiner")
    valueField.setAccessible(true)
    combinersField.setAccessible(true)
    createCombinerField.setAccessible(true)
    val mergeValue = valueField.get(f2)
    val mergeCombiners = combinersField.get(f2)
    context.loadClass(mergeCombiners.getClass.getName,true)
    val mergeCombinersClass = context.sootClass(mergeCombiners.getClass.getName)
    val iterableType:String = mergeCombinersClass.getMethods.filter(_.getName.equals("apply")).apply(0)
      .getReturnType.toString

    val createCombiners = createCombinerField.get(f2)

    val outerField = createCombiners.getClass.getDeclaredField("$outer")
    outerField.setAccessible(true)
    val outer = outerField.get(createCombiners)
    val outerField2 = outer.getClass.getDeclaredField("$outer")
    outerField2.setAccessible(true)
    val outer2 = outerField2.get(outer)

    val ktField = outer2.getClass.getDeclaredField("org$apache$spark$rdd$PairRDDFunctions$$kt")
    ktField.setAccessible(true)
    val kt:String = ktField.get(outer2).toString

    val vtField = outer2.getClass.getDeclaredField("org$apache$spark$rdd$PairRDDFunctions$$vt")
    vtField.setAccessible(true)
    val vt:String = vtField.get(outer2).toString

    val info = PairInfo(kt,iterableType,vt)
    info
  }

  def computeFieldOffsets(appClass:SootClass,degenerateValue:Int,context: Context):(Int,mutable.HashMap[String,(Int,Int,Int,Type)])={
    val fieldOffsetMap = mutable.HashMap.empty[String, (Int, Int, Int, Type)]
    var currentOffset = 0
    val (prims, refs) = appClass.getFields.partition(_.getType.isInstanceOf[PrimType])

    def getPrimSize(primType: Type): Int = primType match {
      case _: BooleanType => 1
      case _: CharType => 2
      case _: ByteType => 1
      case _: ShortType => 2
      case _: IntType => 4
      case _: LongType => 8
      case _: FloatType => 4
      case _: DoubleType => 8
    }

    def getArraySize(arrayType: ArrayType, length: Int): (Int, Int, Type) = {
      val elementSize = getPrimSize(arrayType.baseType)
      (elementSize * length, elementSize, arrayType.baseType)
    }

    for (primField <- prims) {
      val size = getPrimSize(primField.getType)
      fieldOffsetMap(primField.getName) = (currentOffset, size, 0, primField.getType)
      currentOffset += size
    }

    for (refField <- refs) {
      val (size, elementSize, baseType) = getArraySize(refField.getType.asInstanceOf[ArrayType], degenerateValue)
      fieldOffsetMap(refField.getName) = (currentOffset, size, elementSize, baseType)
      currentOffset += size
    }

    (currentOffset, fieldOffsetMap)
  }

  def doInjectionAnalysis(appClass:SootClass,context: Context):mutable.Map[String,Array[String]]={
    val injectionInfoMap = mutable.HashMap.empty[String, Array[String]]

    for (method <- appClass.getMethods if !method.isStatic) {
      val injectedFields = Array.fill(method.getParameterCount)("")
      injectionInfoMap(method.getSubSignature) = injectedFields

      var thisLocal = ""
      val localToParameters = collection.mutable.HashMap.empty[String, Int]

      for (stmt <- method.getActiveBody.getUnits) {
        stmt match {
          case identity: JIdentityStmt => {
            val local = identity.getLeftOp.asInstanceOf[Local]
            identity.getRightOp match {
              case _: ThisRef => {
                thisLocal = local.getName
              }
              case parameter: ParameterRef => {
                localToParameters.put(local.getName, parameter.getIndex)
              }
            }
          }
          case assign: JAssignStmt => {
            val leftValue = assign.getLeftOp
            if (leftValue.isInstanceOf[JInstanceFieldRef]) {
              val fieldRef = leftValue.asInstanceOf[JInstanceFieldRef]
              if (fieldRef.getBase.asInstanceOf[Local].getName == thisLocal) {
                val rightValue = assign.getRightOp
                if (rightValue.isInstanceOf[Local]) {
                  val localName = rightValue.asInstanceOf[Local].getName
                  val index = localToParameters(localName)
                  injectedFields(index) = fieldRef.getField.getName
                }
              }
            }
          }
          case _ =>
        }
      }
    }

    injectionInfoMap
  }

  def degenerate(degenerateClassName:String,mainClassName:String,context:Context): (Int,Boolean) = {
    //context.loadClass(mainClassName,true)
    val mainClass = context.sootClass(mainClassName)
    for(method <- mainClass.getMethods){
      for(unit <- method.getActiveBody.getUnits.snapshotIterator()){
        if(unit.isInstanceOf[JInvokeStmt]){
          val jInvokeStmt = unit.asInstanceOf[JInvokeStmt]
          val invokeMethodName = jInvokeStmt.getInvokeExpr.getMethodRef.name()
          if(invokeMethodName.equals("<init>")){
            val invokeClassName = jInvokeStmt.getInvokeExpr.getMethod.getDeclaringClass.getName
            if(invokeClassName.equals(degenerateClassName)){
              val initMethod = jInvokeStmt.getInvokeExpr.getMethod
              var arrayIndex = 0
              for(i <- 0 until initMethod.getParameterCount){
                if(initMethod.getParameterType(i).isInstanceOf[ArrayType])
                  arrayIndex = i
              }
              val arrayValueLocal = jInvokeStmt.getInvokeExpr.getArg(arrayIndex)
              for(geUnit <- method.getActiveBody.getUnits.snapshotIterator() if geUnit.isInstanceOf[JAssignStmt]){
                val jAssignStmt = geUnit.asInstanceOf[JAssignStmt]
                if(jAssignStmt.getLeftOp.equals(arrayValueLocal)){
                  val rightOp = jAssignStmt.getRightOp
                  if(rightOp.isInstanceOf[JNewArrayExpr]){
                    val jNewArrayExpr = rightOp.asInstanceOf[JNewArrayExpr]
                    val degenerateValue = jNewArrayExpr.getSize.toString()
                    return (degenerateValue.toInt,true)
                  }
                }
              }
            } else if(invokeClassName.startsWith(mainClassName)){
              return degenerate(degenerateClassName,invokeClassName,context)
            }
          }
        }
      }
    }
    return (0,false)
  }
}