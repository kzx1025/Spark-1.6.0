package org.apache.spark.examples.iceke

import org.apache.spark.{SparkContext, SparkConf}

/**
  * Created by iceke on 17/1/18.
  */
object SparkPR {
  def main(args: Array[String]) {
    if (args.length < 1) {
      System.err.println("Usage: SparkPageRank <file> <iter> <out>")
      System.exit(1)
    }

    val sparkConf = new SparkConf().setAppName(args(3)).setMaster(args(4))
    val iters = if (args.length > 1) args(1).toInt else 10
    val ctx = new SparkContext(sparkConf)
    val lines = ctx.textFile(args(0))
    val text = lines.map{ s =>
      val parts = s.split("\\s+")
      (parts(0).toInt, parts(1).toInt)
    }

    println("!!!!!!!!!!!!!!text length:" + text.count())

    val links = text.groupByKey().cache()
    println("!!!!!!!!!!!!!!text length:" +links.count())
    var ranks = links.mapValues(v => 1.0)

    for (i <- 1 to iters) {
      val contribs = links.join(ranks)
        .values.flatMap{ case (urls, rank) =>
        val size = urls.size
        urls.map(url => (url, rank / size))
      }
      ranks = contribs.reduceByKey(_ + _)
        .mapValues(0.15 + 0.85 * _)
    }

    ranks.saveAsTextFile(args(2))
    //ranks.foreach(t => println(t._1 + ":" + t._2))

    ctx.stop()
  }


}
