package cn.edu.hust.grid.example

import org.apache.spark.{DecaContext, SparkConf}

/**
  * Created by iceke on 17/10/17.
  */
object SparkPR {
  def main(args: Array[String]) {

    val sparkConf = new SparkConf().setAppName("SparkPR").setMaster("local")
      .set("spark.serializer", "org.apache.spark.serializer.KryoSerializer")
      .set("spark.shuffle.spill", "false")
      .set("spark.shuffle.manager", "tungsten-sort")
    val iters = 1
    // val ctx = new SparkContext(sparkConf)
    val ctx = new DecaContext(sparkConf)
    val lines = ctx.textFile("data/PR-13m-part.txt")
    val text = lines.map { s =>
      val parts = s.split("\\s+")
      (parts(0).toInt, parts(1).toInt)
    }


    val links = text.groupByKey().cache()
    var ranks = links.mapValues(v => 1.0)


    for (i <- 1 to iters) {
      val contribs = links.join(ranks)
        .values.flatMap { case (urls, rank) =>
        val size = urls.size
        urls.map(url => (url, rank / size))
      }
      ranks = contribs.reduceByKey(_ + _)
        .mapValues(0.15 + 0.85 * _)
    }

    // ranks.saveAsTextFile("data/pr_result")
    ranks.foreach(n => println(n))

    ctx.stop()

  }

}
