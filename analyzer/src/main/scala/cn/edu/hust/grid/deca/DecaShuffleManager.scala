package cn.edu.hust.grid.deca

import cn.edu.hust.grid.deca.iter.{DecaShuffleIterator}

object DecaShuffleManager {
  val iter = new DecaShuffleIterator()
  def getIter(blockId: String):DecaShuffleIterator = iter
  def writeElement(elem: Object):Unit={
    //无需实现
    iter.setElement(elem)
  }

}
