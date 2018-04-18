package org.apache.spark.scheduler

import org.apache.spark.rdd.RDD

/**
  * Created by iceke on 17/10/17.
  */
class Phase(val id: Int,
            val finalRDD: RDD[_],
            var parents: List[Phase]
                ) {
  private var parents_2: List[Phase] = parents
  var kind:String = null
  var dataSource: String = "shuffle"

  def setParents(parents:List[Phase]):Unit={
    parents_2 = parents
  }

  def getParents() =parents_2

  def getFinalRDD()=finalRDD


}
