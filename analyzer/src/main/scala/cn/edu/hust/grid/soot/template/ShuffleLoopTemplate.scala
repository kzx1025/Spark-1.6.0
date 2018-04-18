package cn.edu.hust.grid.soot.template

import cn.edu.hust.grid.deca.DecaShuffleManager
import cn.edu.hust.grid.deca.iter.DataSourceIterator
import org.apache.spark.scheduler.DecaTaskContext

class ShuffleLoopTemplate(rddId: Int){
  def loopFunc[U](taskContext: DecaTaskContext, id: Int, iterator: DataSourceIterator):Unit = {
    while (iterator.hasNext) {
      val element = iterator.next().asInstanceOf[Integer]
      DecaShuffleManager.writeElement(element)
    }

  }

}
