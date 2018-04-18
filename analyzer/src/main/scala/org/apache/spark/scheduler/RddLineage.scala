package org.apache.spark.scheduler

import org.apache.spark.rdd.RDD

import scala.collection.mutable

object RddLineage {
  val op=new mutable.HashMap[String,String]()
  val rddtype=new mutable.HashSet[String]()

  def getRddType(rdd:RDD[_]):String={
    rdd.toString().substring(0,rdd.toString().indexOf("["))
  }
  def analyse(rdd:RDD[_]):Unit={
    if(rdd==null)
      return
//    println(rdd.scope.get.name+"["+rdd.creationSite.shortForm+"]")
    print(rdd.toString().split("\\s+")(0)+getScopeName(rdd))
    if(!rdd.scope.isEmpty&&(!op.contains(rdd.scope.get.name))){
      op.put(rdd.scope.get.name,rdd.toString())
    }
    if(!rddtype.contains(getRddType(rdd))){
      rddtype.add(getRddType(rdd))
    }
    transform(rdd)
    println()
  }
  def  transform(rdd:RDD[_]): Unit ={

    val dependences=rdd.dependencies
    if(dependences==null||dependences.size==0){
      return
    }
    var flag=true
    for(dep<-dependences){
      if(flag){
        flag=false
      }else{
        println()
//        println(rdd.scope.get.name+"["+rdd.creationSite.shortForm+"]")
        print(rdd.toString().split("\\s+")(0)+getScopeName(rdd))
      }
      val deprdd=dep.rdd
//        println("<---"+deprdd.scope.get.name+"["+deprdd.creationSite.shortForm+"]")
      print("<---"+deprdd.toString().split("\\s+")(0)+getScopeName(deprdd))
      if(!deprdd.scope.isEmpty&&(!op.contains(deprdd.scope.get.name))){
        op.put(deprdd.scope.get.name,deprdd.toString())
      }
      if(!rddtype.contains(getRddType(deprdd))){
        rddtype.add(getRddType(deprdd))
      }
        transform(deprdd)
        flag=false
    }
  }
  def printOp(): Unit ={
    println("所有算子如下")
    for(opera<-op){
      println(opera._1)
    }
    for(opera<-op){
      println(opera._2)
    }
    println("\n所有rdd类型如下")
    for(ty<-rddtype){
      println(ty)
    }

  }
  def getScopeName(rdd:RDD[_]):String={
    if(!rdd.scope.isEmpty){
      "["+rdd.scope.get.name+"]"
    }else{
      "[None]"
    }

  }
}
