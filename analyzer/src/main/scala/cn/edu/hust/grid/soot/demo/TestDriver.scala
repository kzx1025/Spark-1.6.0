package cn.edu.hust.grid.soot.demo

import cn.edu.hust.grid.soot.optimize.Context
import soot.jimple.spark.SparkTransformer
import soot.{EntryPoints, SootClass}

/**
 * Created by Administrator on 2015/7/20.
 */
object TestDriver {

  def main(args: Array[String]): Unit = {
    val context = new Context("cn.edu.hust.grid.soot.demo.TestSoot",excludePackages=List("org.spark_project.*","scala.collection.*"),preload = false)
   // context.loadClass("cn.edu.hust.grid.soot.demo.TestSoot", true)
    val mainClass: SootClass = context.sootClass("cn.edu.hust.grid.soot.demo.TestSoot$")

    context.fusionClassList.foreach(println)
    context.scene.setEntryPoints(EntryPoints.v().application())
    val map = new java.util.HashMap[String, String]()
    map.put("enabled", "true")
    map.put("set-impl", "hash")
    map.put("on-fly-cg", "true")
    map.put("propagator", "worklist")
    map.put("dump-answer", "true")
    map.put("dump-html", "true")
    SparkTransformer.v.transform("", map)
    context.writeOutput()
  }

}
