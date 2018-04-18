package cn.edu.hust.grid.deca.iter

class DecaShuffleIterator extends DataSourceIterator {
  var elem: Object = null
  override def next(): Object = {
     elem
  }

  def setElement(elem: Object): Unit = {
    this.elem = elem
  }
}
