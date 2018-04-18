package cn.edu.hust.grid.soot.optimize

import java.io.File
import java.util

import scala.collection.JavaConversions._

object AutoLoad {
  val classList = new util.ArrayList[String]()

  def record(context: Context): Unit = {
    for (appClass <- context.applicationClasses) {
      // println(appClass.getName)
      classList.add(appClass.getName)
    }
  }

  def packClasses(classNum: Int):Unit={
    val tempContext = new Context(preload = false, classpath =  System.getProperty("java.class.path"))
    var index = 0
    println(classList)
    for (index <- 0 to classNum*2) {
      val className = classList.get(index)
      if (!className.equals("com.sun.xml.bind.annotation.XmlLocation")&& !className.contains("Func")&& !className.contains("Iterator")&& !className.contains("Deca")&& !className.contains("Iterator")&& !className.contains("Iterator")) {
        try {
          tempContext.loadClass(className)
        } catch {
          case _ :Exception=> {
            print(className + ",")
          }
        }
      }
    }
    tempContext.writeOutput(true)
  }

  def loadClasses(): Unit = {
    val tempContext = new Context(preload = false, classpath = "sootOutput" + File.pathSeparator + System.getProperty("java.class.path"))

    for (className <- classList) {
      if (!className.equals("com.sun.xml.bind.annotation.XmlLocation")) {
        try {
          tempContext.loadClass(className)
        } catch {
          case _ => {
            print(className + ",")
          }
        }
      }
    }

    println()


  classList.clear()
  }

}
