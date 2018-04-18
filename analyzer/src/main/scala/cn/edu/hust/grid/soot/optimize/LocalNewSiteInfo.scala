package cn.edu.hust.grid.soot.optimize

import soot.{SootClass, SootField}
import soot.jimple.internal.JimpleLocal

import scala.collection.mutable

/**
  * Created by iceke on 17/11/10.
  * 用于拆解类和代码转换的信息
  *
  * @param context
  * @param local
  * @param topClass
  * @param genericType
  * @param localNewSite
  * @param fieldsNewSiteMap
  */
case class LocalNewSiteInfo(context: Context,
                            funcClass: SootClass,
                            local: JimpleLocal,
                            topClass: SootClass,
                            var genericType: String,
                            localNewSite: SootSite,
                            fieldInfoMap: mutable.HashMap[SootField, FieldInfo],
                            fieldsNewSiteMap: mutable.HashMap[SootField, SootSite]) {

}
