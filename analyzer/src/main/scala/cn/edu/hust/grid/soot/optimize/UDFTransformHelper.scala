package cn.edu.hust.grid.soot.optimize

import org.apache.hadoop.io.WritableComparator
import org.apache.spark.{Partition, TaskContext}

/**
 * Created by peicheng on 15-12-24.
 */
class UDFTransformHelper  extends Function3[Partition,TaskContext,Iterator[Any],Any] with Serializable{

  val field1 = 0
  val field2 = 0
  val totalSize = 0
  var offset = 0
  val parameterSize: Int = 0
  var byteArray : Array[Byte] = null
  // the dim of array can be changed
  var parameterTest = new Array[Double](parameterSize)

  override def apply(partition:Partition,
                     taskContext: TaskContext,
                     iter:Iterator[Any]): Any = {
    byteArray = iter.next().asInstanceOf[Array[Byte]]
    val endFlag = byteArray.length
    val result = new Array[Double](parameterSize)
    var i = 0
    while(i < result.length) {
      result.update(i, 0)
      i += 1
    }
    while(offset < endFlag){
      val resultTmp = apply_actual()
      val resultTmpLength = resultTmp.length
      i = 0
      while( i < resultTmpLength){
        val resultTmp1 = result(i) + resultTmp(i)
        result.update(i, resultTmp1)
        i += 1
      }
      offset += totalSize
    }
    Some(result)
  }

  def getDouble(fieldOffset: Int): Double = {
    WritableComparator.readDouble(byteArray, offset + fieldOffset)
  }

  def getArrayFieldDouble(fieldOffset: Int, elementSize: Int, index: Int): Double = {
    WritableComparator.readDouble(byteArray, offset + fieldOffset + elementSize * index)
  }

  /**this is for test*/
  def apply_right(): Array[Double] = {
    val gradient: Array[Double] = new Array[Double](parameterSize)
    var i = 0
    while( i < parameterSize) {
      var dot = 0.0
      var j = 0
      while( j < parameterSize){
        dot += parameterTest(j) * getArrayFieldDouble(field2, 8, j)
        j += 1
      }
      gradient(i) = (1 / (1 + Math.exp(-getDouble(field1) * dot)) - 1) * getDouble(field1) * getArrayFieldDouble(field2, 8, i)

      i+=1
    }
    return gradient
  }

  def apply_actual(): Array[Double] = {
    val gradient: Array[Double] = new Array[Double](parameterSize)
    println("You are wrong because the method body is wrong.")
    return gradient
  }

}