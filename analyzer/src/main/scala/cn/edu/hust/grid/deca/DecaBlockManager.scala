package cn.edu.hust.grid.deca

import cn.edu.hust.grid.deca.iter.DecaCacheIterator

object DecaBlockManager {
  val iter = new DecaCacheIterator()
  //val list = List(1,2,3)
  def getIter(blockId: String): DecaCacheIterator = iter
  def isContainBlock(blockId: String): Boolean = true
  def writeElement(elem: Object):Unit={
    //无需实现
    iter.setElement(elem)
  }

}
