package cn.edu.hust.grid.soot.optimize

import org.apache.spark.rdd.RDD

import scala.reflect.ClassTag

/**
 * Created by Administrator on 2015/7/20.
 */
class Optimizer {

  def optimize[T: ClassTag](rdd: RDD[T]): Unit = {
    //val context = new Context
    //Tailor(context)
  }

}
