package cn.edu.hust.grid.soot.demo

import breeze.linalg.DenseVector

/**
 * Created by zx on 15-11-30.
 */
object DenseVectorDecomposer {
  val D = 10
  val R = 0.7
  val N = 10000

  def main(args:Array[String]): Unit ={
    val test1 = new DenseVector(Array(1,2,3))
    val test2 = new DenseVector(Array(2,3,4))
    val test3 = test1 + test2
    println(test3.toArray.mkString(";"))
  }

}
