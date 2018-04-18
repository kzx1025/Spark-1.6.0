package cn.edu.hust.grid.soot.demo

import cn.edu.hust.grid.soot.optimize.FieldInfo
import cn.edu.hust.grid.soot.template.LoopTemplate
import org.apache.spark.scheduler.{Phase, StageScheduler}

import scala.collection.mutable

object TestSoot {
  def main(args: Array[String]): Unit = {
    //val a: Boolean = true
    val iterableArray = List(1,2,3)

    val tupleValue = new Tuple2(iterableArray,2.3)
    val finalTuple = new Tuple2(5,tupleValue)

    val iter = iterableArray.iterator


    println(iter.next())
   // val f:LoopTemplate = null
    //val list=List(1,2,3)
    //val iter: Iterator[Int] = list.iterator
   // val phase = new Phase(1,null,null)
   // val stageScheduler = new StageScheduler(null)
   // println(list)
  }

}
