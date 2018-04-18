package cn.edu.hust.grid.deca

import soot.SootClass

class ShuffleFunc(createCombinerFunc: SootClass, mergeValueFunc: SootClass, mergeCombinerFunc: SootClass) {
  def getCreateCombiner = createCombinerFunc
  def getMergeValue = mergeValueFunc
  def getMergeCombiner = mergeCombinerFunc
}
