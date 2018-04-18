package cn.edu.hust.grid.soot.demo

import cn.edu.hust.grid.soot.optimize.{Context, Tailor}

/**
 * Created by Administrator on 2015/7/20.
 */
object TailorDriver {



  def main(args: Array[String]): Unit = {

    val f = (_: Int) -> 0

    val context = new Context(preload = false)
    context.loadClass("cn.edu.hust.grid.deca.DecaBlockManager$", true)
  //  context.loadClass("cn.edu.hust.grid.deca.DecaIterator", true)
   // val sootClass = context.sootClass("cn.edu.hust.grid.example.SparkLR$$anonfun$main$1$$anonfun$3")
     // println(sootClass.getMethodByName("<clinit>"))
   // context.loadClass("cn.edu.hust.grid.deca.iter.ShuffleData$")
    //context.loadClass("org.apache.spark.rdd.RDD$$anonfun$treeAggregate$1$$anonfun$24")
    context.loadClass("com.sun.xml.bind.annotation.XmlLocation")
    context.loadClass("org.apache.spark.ml.tree.impl.RandomForest$$anonfun$11$$anonfun$apply$10")
    context.loadClass("org.apache.spark.ml.tree.impl.RandomForest$$anonfun$33$$anonfun$apply$20")

    //Tailor.transform(context)

    context.writeJimple()
  }

}
