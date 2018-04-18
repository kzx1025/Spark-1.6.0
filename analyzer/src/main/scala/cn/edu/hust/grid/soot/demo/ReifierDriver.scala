package cn.edu.hust.grid.soot.demo

import cn.edu.hust.grid.soot.optimize.{Context, DeepTailor, Flatten, Tailor}

/**
 * Created by Administrator on 2015/7/20.
 */
object ReifierDriver {

  def main(args: Array[String]){
//    val context = new Context("org.apache.spark.flint.demo.ReifierDenseVectorLR", "main")
//
//    Reifier.transform(context)
//
//    Tailor.transform(context)
//
//    val className1 = "org.apache.spark.flint.demo.ReifierDenseVector$DataPoint"
//    context.decomposeWorkingList.enqueue(className1)
//    Classifier.transform(context)
//
//    context.writeOutput()

    val excludePackagesList = List("scala.xml.Node",
    "org.apache.log4j.*",
    "org.slf4j.*" )
    val context = new Context("org.apache.spark.flint.demo.DenseVectorDecomposer","main", excludePackages = excludePackagesList)
    Flatten.transform(context)
    Tailor.transform(context)
    DeepTailor.transform(context)

//    val className = "org.apache.spark.flint.demo.DenseVectorDecomposer$DataPoint"
//    context.decomposeWorkingList.enqueue(className)
//    Classifier.transform(context)
//    context.applicationClasses.foreach(println)
    println("--"+context.applicationClasses.size())
    //context.writeOutput()
  }

}
