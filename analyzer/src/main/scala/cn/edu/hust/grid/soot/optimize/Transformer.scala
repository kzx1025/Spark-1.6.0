package cn.edu.hust.grid.soot.optimize

/**
 * Created by Administrator on 2015/7/21.
 */
trait Transformer {
  def transform(context: Context): Unit
}
