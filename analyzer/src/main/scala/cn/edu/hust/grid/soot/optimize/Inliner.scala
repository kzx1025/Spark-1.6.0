package cn.edu.hust.grid.soot.optimize

import soot.jimple.toolkits.invoke.{SiteInliner, InlinerSafetyManager}
import soot.jimple.Stmt

import scala.collection.JavaConversions._

/**
 * Created by Administrator on 2015/7/21.
 */
object Inliner extends Transformer {

  override def transform(context: Context): Unit = {
    while(inlineStaticMethods("f", context)) {}
    while(inlineStaticMethods("g", context)) {}
  }

  private def inlineStaticMethods(entryName: String, context: Context): Boolean = {
    val entryMethod = context.sootClass(context.mainClass).getMethodByName(entryName)
    val sitesToInline = entryMethod.getActiveBody.getUnits.map(_.asInstanceOf[Stmt]).
      filter(_.containsInvokeExpr()).map(invoke => (invoke.getInvokeExpr.getMethod, invoke)).
      filter { case (target, invoke) =>
        target.getDeclaringClass.isApplicationClass &&
          target.isStatic &&
          InlinerSafetyManager.ensureInlinability(target, invoke, entryMethod, "")
      }

    var inlined = false
    for ( (inlinee, invokeStmt) <- sitesToInline) {
      if (InlinerSafetyManager.ensureInlinability(inlinee, invokeStmt, entryMethod, "")) {
        inlined = true
        SiteInliner.inlineSite(inlinee, invokeStmt, entryMethod, new java.util.HashMap[String, String]())
        context.packManager.getPack("jb").apply(entryMethod.getActiveBody)
        context.packManager.getPack("jop").apply(entryMethod.getActiveBody)
      }
    }
    inlined
  }
}
