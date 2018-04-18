package cn.edu.hust.grid.deca

object TimeRecorder{
  var fusionTime: Long = 0L
  var loadClassTime: Long = 0L
  var pointerAnalysisTime: Long = 0L
  var tailorTime: Long = 0L
  var classifyTime: Long =0L
  var decomposeTime: Long = 0L
  var transformTime: Long = 0L
  var totalTime: Long = 0L
  var localNewSiteInfoSize:Int=0
  var writeJimpleTime:Long=0l
  var packTime:Long = 0L
  var writeJimpleNum:Int=0

  var jobID: Int = 0
  var stageID: String = null

  def record():Unit={
    println("!!!!!!!!!!Time info record==> "+"jobId:"+jobID+" stageId:"+stageID+ " fusionTime:"+fusionTime+ " loadClassTime:"+loadClassTime
      + " pointerAnalysisTime:"+pointerAnalysisTime+" tailorTime:"+tailorTime +" classifyTime:"+classifyTime+" decomposeTime:"+decomposeTime+ " transformTime:"+ transformTime
    +" writeJimpleTime:"+(writeJimpleTime+packTime)+" totalTime:"+totalTime+" localNewSiteSize:"+localNewSiteInfoSize+" writeJimpleNum:"+writeJimpleNum)
  }

}
