package cn.edu.hust.grid.soot.optimize

import soot.SootClass

case class FieldInfo(var specificClass: SootClass, var isArray: Boolean, childFieldInfos: java.util.List[FieldInfo]) {

}
