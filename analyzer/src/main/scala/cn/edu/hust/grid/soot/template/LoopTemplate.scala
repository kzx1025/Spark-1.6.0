package cn.edu.hust.grid.soot.template

import cn.edu.hust.grid.deca.iter.DataSourceIterator
import org.apache.spark.scheduler.DecaTaskContext

class LoopTemplate(rddId: Int) {
  def loopFunc[U](taskContext: DecaTaskContext, id: Int, iterator: DataSourceIterator): Int = {
    var result = 0
    while (iterator.hasNext) {
      val element = iterator.next().asInstanceOf[Int]
      result += element
    }
    result
  }
}
