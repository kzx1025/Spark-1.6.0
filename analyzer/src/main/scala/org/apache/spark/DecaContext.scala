package org.apache.spark

import cn.edu.hust.grid.soot.optimize.OptimizeException
import org.apache.spark.rdd._
import org.apache.spark.scheduler.DAGAnalyzer
import org.apache.spark.{SparkConf, SparkContext, TaskContext}
import soot.{IntType, Type}

import scala.collection.mutable
import scala.collection.mutable.{HashSet, Stack}
import scala.reflect.ClassTag

/**
  * Created by iceke on 17/10/17.
  */
class DecaContext(conf: SparkConf) extends SparkContext(conf) {
  /**the transformed cacheRDD */
  private var cacheRDD :RDD[_] = null
  /**the original cacheRDD*/
  private var actualCacheRDD: RDD[_] = null



  private def this() = this(new SparkConf())


  /**
    * 重写SparkContext提交job的方法
    * 截获上传的job,对此job的代码进行分析和转换
    */
  override def runJob[T, U: ClassTag](
                                       rdd: RDD[T],
                                       func: (TaskContext, Iterator[T]) => U,
                                       partitions: Seq[Int],
                                       resultHandler: (Int, U) => Unit): Unit = {
    try {
      // val backup_dag = _dagScheduler
      // _dagScheduler = new DAGScheduler(this)


      val start = System.currentTimeMillis()
      val decaRDD = analyze(rdd, func, partitions, resultHandler)
      val end = System.currentTimeMillis()
      logInfo("!!Deca analyze and transform the program cost:" + (end - start) / 1000)

      //恢复dagScheduler的状态
      // _dagScheduler = backup_dag

      if (decaRDD != null) {
        super.runJob(decaRDD, func, partitions,  resultHandler)
      } else {
        super.runJob(rdd, func, partitions,  resultHandler)
      }
    } catch {
      case OptimizeException(msg) =>
        logWarning("Deca can't optimize! " + msg)
        super.runJob(rdd, func, partitions, resultHandler)
      case e: Exception =>
        logError("Some error occur in Deca optimize! " + e.printStackTrace())
        super.runJob(rdd, func, partitions, resultHandler)
    }


  }

  //  private def handleCacheRDD[T](rdd: RDD[T]):Unit = {
  //    if(actualCacheRDD == null){
  //      actualCacheRDD = findCachedRDDFromRDDChain(rdd)
  //      if(actualCacheRDD !=null && cacheRDD == null){
  //        actualCacheRDD match{
  //
  //        }
  //      }
  //
  //    }
  //
  //  }





  /**
    * 截获上传的job,对此job的代码进行分析和转换
    */
  private def analyze[T, U](finalRDD: RDD[T],
                            func: (TaskContext, Iterator[T]) => U,
                            partitions: Seq[Int],
                            resultHandler: (Int, U) => Unit): RDD[T] = {
    println("start analyze the RDD chain")
    DAGAnalyzer.appName = this.appName
    DAGAnalyzer.formPhase(finalRDD, func, partitions, resultHandler, this)
    DAGAnalyzer.clear()
    null
  }

}

