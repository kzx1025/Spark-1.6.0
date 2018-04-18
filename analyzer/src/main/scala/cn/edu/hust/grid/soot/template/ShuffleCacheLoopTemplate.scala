package cn.edu.hust.grid.soot.template

import cn.edu.hust.grid.deca.iter.DataSourceIterator
import cn.edu.hust.grid.deca.{DecaBlockManager, DecaShuffleManager}
import org.apache.spark.scheduler.DecaTaskContext

class ShuffleCacheLoopTemplate(rddId: Int) {
  def loopFunc[U](taskContext: DecaTaskContext, id: Int, iterator: DataSourceIterator): Unit = {
    val blockId = rddId.toString + id.toString
    val isCache = DecaBlockManager.isContainBlock(blockId)
    if (isCache) {
      val iter = DecaBlockManager.getIter(blockId)
      while (iter.hasNext) {
        val element = iter.next().asInstanceOf[Integer]
        DecaShuffleManager.writeElement(element)
      }
    } else {
      //cacheWrite
      while (iterator.hasNext) {
        val element = iterator.next().asInstanceOf[Integer]
        DecaBlockManager.writeElement(element)
      }
      //cacheRead
      val iter = DecaBlockManager.getIter(blockId)
      while (iter.hasNext) {
        val element = iter.next().asInstanceOf[Integer]
        DecaShuffleManager.writeElement(element)
      }

    }
  }

}
