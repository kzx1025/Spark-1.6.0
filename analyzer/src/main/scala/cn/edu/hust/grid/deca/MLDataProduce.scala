package cn.edu.hust.grid.deca


import breeze.linalg.DenseVector
import org.apache.spark.mllib.stat.MultivariateOnlineSummarizer

object MLDataProduce {
  var typeName: String = null

  def getZeroValue():Object={
    typeName match{
      case "org.apache.spark.mllib.stat.MultivariateOnlineSummarizer" =>
        new MultivariateOnlineSummarizer()
      case "scala.Tuple3" =>
        new Tuple3(1,2,3)
      case "breeze.linalg.DenseVector$mcD$sp" =>
        val doubleValue = Array(1.0,2.0)
        new DenseVector(doubleValue)
    }
  }

}
