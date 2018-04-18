package cn.edu.hust.grid.deca.iter


import scala.collection.{IterableLike, mutable}


object ShuffleData {
  var dataType: String = null

  def getTupleFromPR():Tuple2[_,_]={
    val iterableArray = List(1,2,3)
    val tupleValue = new Tuple2(iterableArray,2.3)
    val finalTuple = new Tuple2(5,tupleValue)
    val a = iterableArray.asInstanceOf[Iterable[Int]].iterator.next()
    finalTuple
  }

  def getIntIterValue[T](iterable: Iterable[T]): Int={
    iterable.iterator.next().asInstanceOf[Int]
  }

  def getSeqValue[T](iterItems: IterableLike[T,_]): T = {
    iterItems.iterator.next()
  }
}
