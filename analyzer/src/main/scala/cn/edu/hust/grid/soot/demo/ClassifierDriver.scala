package cn.edu.hust.grid.soot.demo

import cn.edu.hust.grid.soot.optimize.{Classifier, Context}

/**
  * Created by Administrator on 2015/7/20.
  */
object ClassifierDriver {

  def main(args: Array[String]): Unit = {
    val context = new Context("org.apache.spark.flint.demo.ReifierDenseVectorLR", "main")

    val className = "org.apache.spark.flint.demo.ReifierDenseVectorLR$DataPoint"
    context.decomposeWorkingList.enqueue(className)
    Classifier.transform(context)
    println(context.classifyMap.getOrElse(className, "Unknown"))

    println(context.classifyMap.mkString(";"))

    context.writeOutput()
  }

}
