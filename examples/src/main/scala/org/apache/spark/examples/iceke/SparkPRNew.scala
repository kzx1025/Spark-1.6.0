package org.apache.spark.examples.iceke

import org.apache.spark.rdd.{RDD, ShuffledRDD}
import org.apache.spark.util.collection.CompactBuffer
import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by iceke on 17/1/17.
  */
object SparkPRNew {
  private val ordering = implicitly[Ordering[Int]]

  def main(args: Array[String]) {

    val sparkConf = new SparkConf().setAppName(args(0)).setMaster(args(4))
    val iters = args(1).toInt
    val ctx = new SparkContext(sparkConf)
    val startTime = System.nanoTime()
    val lines = ctx.textFile(args(2))
    val links = lines.map{ s =>
      val parts = s.split("\\s+")
      (parts(0).toInt, parts(1).toInt)
    }.groupByKey().
      asInstanceOf[ShuffledRDD[Int, _, _]].
      setKeyOrdering(ordering).
      asInstanceOf[RDD[(Int, Iterable[Int])]].cache()
    var ranks = links.mapValues(v => 1.0)

    for(i <- 1 to iters){

      val contribs = links.zipPartitions(ranks) {
        case (link, vertices) =>
          new Iterator[(Int, Double)] {
            var keyRecord: Int = 0
            var changeVertex = true
            var currentLinkIndex = 0
            var currentContrib = 0.0d
            var currentDestIndex = 0
            var currentDestNum = 0
            var currentDestList: CompactBuffer[Int] = null

            def matchRecord(): Boolean = {
              assert(changeVertex)
              if(!link.hasNext) return false

              var matched = false
              var tempLink = link.next()
              keyRecord = tempLink._1
              while(!matched&&vertices.hasNext){
                val currentVertex = vertices.next()
                while(currentVertex._1>keyRecord){
                  if(!link.hasNext) return false
                  tempLink = link.next()
                  keyRecord = tempLink._1
                }

                if(currentVertex._1==keyRecord){
                  matched = true
                  currentDestNum = tempLink._2.size
                  currentDestList = tempLink._2.asInstanceOf[CompactBuffer[Int]]
                  currentDestIndex = 0
                  currentContrib = currentVertex._2/currentDestNum
                  changeVertex = false
                }
              }
              matched
            }

            def hasNext(): Boolean = !changeVertex || matchRecord()

            def next(): (Int, Double) = {
              if (!hasNext) Iterator.empty.next()
              else{

                if (currentDestIndex == currentDestNum-1) changeVertex = true

                val destId = currentDestList(currentDestIndex)
                currentDestIndex += 1

                (destId,currentContrib)
              }

            }
          }
      }
      ranks = contribs.reduceByKey(_ + _).asInstanceOf[ShuffledRDD[Int, _, _]].
        setKeyOrdering(ordering).
        asInstanceOf[RDD[(Int, Double)]].
        mapValues(0.15 + 0.85 * _)
    }

    //ranks.foreach(t => println(t._1 + ":" + t._2))
    ranks.saveAsTextFile(args(3))

    ctx.stop()

    val endTime = System.nanoTime()
    println("Cost " + (endTime-startTime))
  }

}