package cn.edu.hust.grid.soot.optimize

object Platform {
  def getInt(`object`: Any, offset: Long) = 0

  def putInt(`object`: Any, offset: Long, value: Int): Unit = {
  }

  def getBoolean(`object`: Any, offset: Long) = true

  def putBoolean(`object`: Any, offset: Long, value: Boolean): Unit = {
  }

  def getByte(`object`: Any, offset: Long): Byte = 0.toByte

  def putByte(`object`: Any, offset: Long, value: Byte): Unit = {
  }

  def getShort(`object`: Any, offset: Long): Short = 0.toShort

  def putShort(`object`: Any, offset: Long, value: Short): Unit = {
  }

  def getLong(`object`: Any, offset: Long) = 0l

  def putLong(`object`: Any, offset: Long, value: Long): Unit = {
  }

  def getFloat(`object`: Any, offset: Long): Float = 0.toFloat

  def putFloat(`object`: Any, offset: Long, value: Float): Unit = {
  }

  def getDouble(`object`: Any, offset: Long): Double = 0.toDouble

  def putDouble(`object`: Any, offset: Long, value: Double): Unit = {
  }

  def getObjectVolatile(`object`: Any, offset: Long): Any = 0.asInstanceOf[Any]

  def putObjectVolatile(`object`: Any, offset: Long, value: Any): Unit = {
  }

  def allocateMemory(size: Long) = 1l

  def freeMemory(address: Long): Unit = {
  }

  def reallocateMemory(address: Long, oldSize: Long, newSize: Long) = 0l

  def setMemory(`object`: Any, offset: Long, size: Long, value: Byte): Unit = {
  }

  def setMemory(address: Long, value: Byte, size: Long): Unit = {
  }

  def copyMemory(src: Any, srcOffset: Long, dst: Any, dstOffset: Long, length: Long): Unit = {
  }

}
