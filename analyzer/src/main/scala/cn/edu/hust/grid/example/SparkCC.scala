package cn.edu.hust.grid.example

import org.apache.spark.{DecaContext, SparkConf}

object SparkCC {
  def main(args:Array[String]){

    val sparkConf = new SparkConf().setAppName("SparkCC").setMaster("local")
    val ctx = new DecaContext(sparkConf)
    val lines = ctx.textFile("data/PR-13m-part.txt")
    val iterations = 1

    val edges = lines.map{ s =>
      val parts = s.split("\\s+")
      (parts(0).toInt, parts(1).toInt)
    }

    val g = edges.groupByKey().cache()

    var messages = g.map( eMsg => {
      (eMsg._1,eMsg._1)
    })

    for( i <- 1 to iterations){

      val newVertices = g.join(messages).values.flatMap( value => {
        value._1.map(vtx => (vtx,math.min(vtx,value._2)))
      })

      messages = newVertices.reduceByKey((v1,v2) => math.min(v1,v2))

    }

    messages.saveAsTextFile("data/cc_result")

  }


}
