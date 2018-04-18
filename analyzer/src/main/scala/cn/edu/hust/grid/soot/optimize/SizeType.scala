package cn.edu.hust.grid.soot.optimize

/**
 * Created by Administrator on 2015/7/21.
 */
object SizeType extends Enumeration {
  type SizeType = Value
  val STATIC_FIXED_SIZE = Value("STATIC_FIXED_SIZE")
  val RUNTIME_FIXED_SIZE = Value("RUNTIME_FIXED_SIZE")
  val VARIABLE_SIZE = Value("VARIABLE_SIZE")
  val UNDEFINED_SIZE = Value("UNDEFINED_SIZE")
}
