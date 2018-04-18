package cn.edu.hust.grid.soot.optimize

import java.util

import soot.{SootClass, SootMethod}

object TransformCollection {
  //先存成String
  val tempDecaMethodMapStrng=new util.HashMap[String,SootMethod]()
  val originDecaMethodMapStrng=new util.HashMap[String,SootMethod]()
  val originDecaMapStrng=new util.HashMap[String,SootClass]()
  val originTempMapStrng=new util.HashMap[String,SootClass]()
  val decaOriginMapStrng=new util.HashMap[SootClass,SootClass]()
  val decaSetStrng=new util.HashSet[String]()
  val transformedMethodsStrng=new util.HashSet[String]()
  val usedArrayDecaStrng=new util.HashSet[String]()
  val tempOriginMapString=new util.HashMap[SootClass,String]()


  def clear(): Unit ={
    tempOriginMapString.clear()
    originDecaMethodMapStrng.clear()
    originDecaMapStrng.clear()
    originTempMapStrng.clear()
    decaOriginMapStrng.clear()
    decaSetStrng.clear()
    transformedMethodsStrng.clear()
    usedArrayDecaStrng.clear()
    tempOriginMapString.clear()
  }




}
