package cn.edu.hust.grid.soot.optimize

import java.util.ArrayList

/**
 * Created by zx on 15-12-1.
 */
object DeepTailor extends Transformer {

  val tailorMainClassName = new ArrayList[String]

  override def transform(context: Context) {
    if(tailorMainClassName.size() == 0)
      throw OptimizeException("No main class in deep tailor.")
  }

}
