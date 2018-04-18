package cn.edu.hust.grid.example

import org.apache.spark.{DecaContext, SparkConf, SparkContext}

/**
  * create with cn.edu.hust.grid.example
  * USER: husterfox
  */
object ShuffleResearch {
  def main(args: Array[String]): Unit = {
    val conf = new SparkConf(false).setAppName("ShuffleResearch").setMaster("local")
    val sc = new DecaContext(conf)
    val dataFile = sc.textFile("/Users/husterfox/Downloads/datalog").flatMap(_.split(" ")).foreach(println(_))
    sc.stop()
  }
}
