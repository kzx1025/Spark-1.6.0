package org.apache.spark.scheduler

import org.apache.spark.rdd.RDD

class CachePhase(override val id: Int,
                 override val finalRDD: RDD[_],
                 parents: List[Phase]
                ) extends Phase(id,finalRDD,parents) {
  var startRDD:RDD[_] = null
  var isWriteCache: Boolean = true
}
