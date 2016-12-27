package org.apache.spark.examples.iceke

import org.apache.spark.{SparkContext, SparkConf}

/**
  * Created by iceke on 16/12/27.
  */
object LabTest2 {
  def main(args: Array[String]) {
    if (args.length < 1) {
      System.err.println("Usage: SparkPageRank <file> <iter> <out>")
      System.exit(1)
    }

    val sparkConf = new SparkConf().setAppName("LabTest").setMaster(args(3))
    val iters = if (args.length > 1) args(1).toInt else 10
    val ctx = new SparkContext(sparkConf)
    val lines = ctx.textFile(args(0))
    val links = lines.map { s =>
      val parts = s.split("\\s+")
      (parts(0).toInt, parts(1).toInt)
    }

    val index1 = links.map(_._1)
    val index2 = links.map(_._2)

    val ice = index1.zip(index2)

    val result = ice.groupByKey()

    result.saveAsTextFile(args(2))
    ctx.stop()
  }


}
