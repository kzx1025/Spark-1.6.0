package cn.edu.hust.grid.soot.template

import cn.edu.hust.grid.deca.DecaBlockManager
import cn.edu.hust.grid.deca.iter.DataSourceIterator
import org.apache.spark.scheduler.DecaTaskContext

/**
  *  Created by iceke on 17/10/30
  *  Loop模板
  * @param rddId
  */
class CacheLoopTemplate(rddId: Int) {
  def loopFunc[U](taskContext: DecaTaskContext, id: Int, iterator: DataSourceIterator): Int = {
    val blockId = rddId.toString + id.toString
    val isCache = DecaBlockManager.isContainBlock(blockId)
    var result = 0
    if (isCache) {
      val iter = DecaBlockManager.getIter(blockId)
      while (iter.hasNext) {
        val element = iter.next().asInstanceOf[Int]
        result += element
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
        val element = iter.next().asInstanceOf[Int]
        result += element
      }

    }
    result

  }

}
