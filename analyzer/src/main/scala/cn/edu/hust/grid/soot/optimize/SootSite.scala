package cn.edu.hust.grid.soot.optimize

import soot.{SootClass, SootMethod}
import soot.{Unit => SootUnit, _}

case class SootSite(sootClass: SootClass, method: SootMethod, newUnit: SootUnit, initUnit: SootUnit) {

}
