package cn.edu.hust.grid.example

import org.apache.spark.{DecaContext, SparkConf}

object TestCacheOptimization {
  def main(args: Array[String]): Unit = {
    val sparkConf = new SparkConf().setAppName("TestCacheOptimization")
      .setMaster("local").
      set("spark.serializer", "org.apache.spark.serializer.KryoSerializer")
    val dc = new DecaContext(sparkConf)
    val textFile = dc.textFile("data/CacheData")
    val input=textFile.flatMap(line=>line.split(" "))
    val result1 = input.map(x => x+"1").cache()
    val result2 = result1.map(x => x + 1)
    result2.foreach(x => println(x))
  }
}
