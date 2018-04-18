package cn.edu.hust.grid.example

import org.apache.spark.{DecaContext, SparkConf, SparkContext}



object SparkWC {
  def main(args: Array[String]){
    val sparkConf = new SparkConf().setAppName("SparkWC")
      .setMaster("local")
      .set("spark.serializer", "org.apache.spark.serializer.KryoSerializer")
      .set("spark.shuffle.spill", "false")
      .set("spark.shuffle.manager", "tungsten-sort")
    // val sparkContext = new DecaContext(sparkConf)
    val sparkContext = new DecaContext(sparkConf)
    val startTime = System.currentTimeMillis
    val lines = sparkContext.textFile("data/PR-13m-part.txt")

    val words = lines.filter(_.contains("1")).map((_,1))

    val results = words.reduceByKey(_+_)
    // results.saveAsTextFile("data/wc_result")
    results.foreach(a => println(a))
    val duration = System.currentTimeMillis - startTime
    println("Duration is " + duration / 1000.0 + " seconds")
  }

}
