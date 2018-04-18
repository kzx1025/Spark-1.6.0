package cn.edu.hust.grid.deca.iter

class DecaCacheIterator {
  var elem: Object = null

  def hasNext(): Boolean = {
    true
  }

  def next(): Object = {
    this.elem
  }

  def setElement(elem: Object): Unit = {
    this.elem = elem
  }

}
