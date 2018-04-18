package org.apache.spark.scheduler

import org.apache.spark.{SparkConf, SparkContext, TaskContext}
import org.apache.spark.rdd.RDD

import scala.reflect.ClassTag

class TempContext(conf:SparkConf) extends SparkContext(conf){
  private def this() = this(new SparkConf())



  /**
    * 重写SparkContext提交job的方法
    * 截获上传的job,对此job的代码进行分析和转换
    */
  override def runJob[T, U: ClassTag](
                                       rdd: RDD[T],
                                       func: (TaskContext, Iterator[T]) => U,
                                       partitions: Seq[Int],
                                       allowLocal: Boolean,
                                       resultHandler: (Int, U) => Unit): Unit ={
    RddLineage.analyse(rdd)
    super.runJob(rdd,func,partitions,false,resultHandler)
  }

  override def stop(): Unit = {
    RddLineage.printOp()
    super.stop()
  }
}
