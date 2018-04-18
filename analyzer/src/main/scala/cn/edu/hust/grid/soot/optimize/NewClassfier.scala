package cn.edu.hust.grid.soot.optimize

import java.util

import cn.edu.hust.grid.soot.optimize.SizeType.SizeType
import org.apache.spark.scheduler.DAGAnalyzer
import soot.jimple.FieldRef
import soot.jimple.internal.JAssignStmt
import soot.{ArrayType, PrimType, RefType, SootClass}

import scala.collection.JavaConversions._

/**
  * Created by iceke on 17/11/11.
  * 对local对应的类进行分类，以判别是否能进行拆解
  * 这里fields需要用到确定的子类。而且是特化后的
  */
object NewClassfier {

  def transform(context: Context, localNewSiteInfos: java.util.List[LocalNewSiteInfo]): Unit = {
    val visitClasses = new util.HashSet[SootClass]()
    for (localNewSiteInfo <- localNewSiteInfos) {
      val analyzeClass = localNewSiteInfo.topClass
      if (!((DAGAnalyzer.appName.equals("DecisionTreeClassificationExample") || DAGAnalyzer.appName.equals("RandomForestClassificationExample") || DAGAnalyzer.appName.equals("DecisionTreeRegressionExample")) && analyzeClass.getName.contains("Tuple2"))) {
        if (!visitClasses.contains(analyzeClass)) {
          try {
            if (isRecursiveType(analyzeClass, context, localNewSiteInfo)) {
              context.classifyMap.put(analyzeClass.getName, SizeType.UNDEFINED_SIZE)
            } else {
              directClassify(analyzeClass, context, localNewSiteInfo)
            }
          } catch {
            case e: Exception =>
              println("分类出现错误，暂不处理")
          }
          visitClasses.add(analyzeClass)
        }
      }

    }

  }

  private def internalClassify(className: String, context: Context, localNewSiteInfo: LocalNewSiteInfo): SizeType = {
    context.classifyMap.getOrElse(className, directClassify(context.sootClass(className), context, localNewSiteInfo))
  }

  private def directClassify(analyzeClass: SootClass, context: Context, localNewSiteInfo: LocalNewSiteInfo): SizeType = {
    var sizeType: SizeType = SizeType.UNDEFINED_SIZE
    val classShortName = analyzeClass.getName
    val isPrimeType = classShortName.equals("int") || classShortName.equals("double") ||
      classShortName.equals("float") || classShortName.equals("long")
    if (isPrimeType) {
      return SizeType.STATIC_FIXED_SIZE
    }
    if (analyzeClass.isPhantom || !analyzeClass.isApplicationClass) {
      return SizeType.STATIC_FIXED_SIZE
    }
    val fieldArrayTypes = getFieldArrayTypes(analyzeClass, localNewSiteInfo)
    val numOfArrayType = fieldArrayTypes.size()
    if (numOfArrayType != 0) {
      var sizeOfNoAssignableField: Int = 0
      for (field <- analyzeClass.getFields) {
        if (field.getType.isInstanceOf[ArrayType]) {
          if (isNoAssignableByField(analyzeClass.getName, field.getName, context)) {
            sizeOfNoAssignableField += 1
          }
        }
      }
      if (sizeOfNoAssignableField == numOfArrayType) {
        val isAllStatic = fieldArrayTypes.map(_.getElementType.toString)
          .map(t => context.classifyMap.getOrElse(t, directClassify(context.sootClass(t), context, localNewSiteInfo)))
          .forall(_ == SizeType.STATIC_FIXED_SIZE)
        if (isAllStatic) {
          context.classifyMap.put(analyzeClass.getName, SizeType.RUNTIME_FIXED_SIZE)
          sizeType = SizeType.RUNTIME_FIXED_SIZE
        } else {
          context.classifyMap.put(analyzeClass.getName, SizeType.VARIABLE_SIZE)
          sizeType = SizeType.VARIABLE_SIZE
        }
      } else {
        context.classifyMap.put(analyzeClass.getName, SizeType.VARIABLE_SIZE)
        sizeType = SizeType.VARIABLE_SIZE
      }
    }
    val fieldRefTypes = getFieldRefTypes(analyzeClass, localNewSiteInfo)
    if (fieldRefTypes.size() > 0) {
      val typeInClasses = fieldRefTypes.map(_.getClassName).toSet[String].map(internalClassify(_, context, localNewSiteInfo))
      val isStatic = typeInClasses.forall(_ == SizeType.STATIC_FIXED_SIZE)
      if (isStatic) {
        context.classifyMap.put(analyzeClass.getName, SizeType.STATIC_FIXED_SIZE)
        if (SizeType.STATIC_FIXED_SIZE > sizeType) {
          sizeType = SizeType.STATIC_FIXED_SIZE
        }
        return sizeType
      } else {
        val isRuntime = typeInClasses.filter(_ != SizeType.STATIC_FIXED_SIZE).forall(_ == SizeType.RUNTIME_FIXED_SIZE)
        if (isRuntime) {
          context.classifyMap.put(analyzeClass.getName, SizeType.RUNTIME_FIXED_SIZE)
          if (SizeType.RUNTIME_FIXED_SIZE > sizeType) {
            sizeType = SizeType.RUNTIME_FIXED_SIZE
          }
          return sizeType
        } else {
          val isVariable = typeInClasses.filter(s => if ((s != SizeType.STATIC_FIXED_SIZE) &&
            (s != SizeType.RUNTIME_FIXED_SIZE)) true else false).forall(_ == SizeType.VARIABLE_SIZE)
          if (isVariable) {
            context.classifyMap.put(analyzeClass.getName, SizeType.VARIABLE_SIZE)
            if (SizeType.VARIABLE_SIZE > sizeType) {
              sizeType = SizeType.VARIABLE_SIZE
            }
            return sizeType
          } else {
            context.classifyMap.put(analyzeClass.getName, SizeType.UNDEFINED_SIZE)
            if (SizeType.UNDEFINED_SIZE > sizeType) {
              sizeType = SizeType.UNDEFINED_SIZE
            }
            return sizeType
          }
        }
      }
    }
    sizeType
  }

  private def getFieldRefTypes(analyzeClass: SootClass, localNewSiteInfo: LocalNewSiteInfo): util.List[RefType] = {
    val fieldsType = new util.ArrayList[RefType]()
    val fieldInfoMap = localNewSiteInfo.fieldInfoMap
    for (field <- analyzeClass.getFields) {
      if (fieldInfoMap.contains(field) && !field.getType.isInstanceOf[ArrayType]) {
        val specificClassType = fieldInfoMap(field).specificClass.getType
        if (specificClassType.isInstanceOf[RefType]) {
          fieldsType.add(specificClassType)
        }
      } else {
        if (field.getType.isInstanceOf[RefType] && !field.getType.isInstanceOf[ArrayType]) {
          fieldsType.add(field.getType.asInstanceOf[RefType])
        }
      }
    }
    fieldsType
  }

  private def getFieldArrayTypes(analyzeClass: SootClass, localNewSiteInfo: LocalNewSiteInfo): util.List[ArrayType] = {
    val fieldsType = new util.ArrayList[ArrayType]()
    val fieldInfoMap = localNewSiteInfo.fieldInfoMap
    for (field <- analyzeClass.getFields) {
      if (fieldInfoMap.contains(field)) {
        val specificClassType = fieldInfoMap(field).specificClass.getType
        val isArray = fieldInfoMap(field).isArray
        if (isArray) {
          fieldsType.add(specificClassType.makeArrayType())
        }
      } else {
        if (field.getType.isInstanceOf[ArrayType]) {
          fieldsType.add(field.getType.asInstanceOf[ArrayType])
        }
      }
    }
    fieldsType
  }


  private def isRecursiveType(analyzeClass: SootClass, context: Context, localNewSiteInfo: LocalNewSiteInfo): Boolean = {
    val visited = collection.mutable.HashSet.empty[SootClass]

    val edges = collection.mutable.HashSet.empty[(SootClass, SootClass)]
    var isDAG = true
    val fieldInfoMap = localNewSiteInfo.fieldInfoMap

    def visit(analyzeClass: SootClass): Unit = {
      val classShortName = analyzeClass.getType.toString
      val isPrimeType = classShortName.equals("int") || classShortName.equals("double") ||
        classShortName.equals("float") || classShortName.equals("long")
      if (!isPrimeType && !analyzeClass.isPhantom && analyzeClass.isApplicationClass) {
        visited.add(analyzeClass)
        for (field <- analyzeClass.getFields) {
          var fieldClass: SootClass = null
          var isPrim: Boolean = false
          if (fieldInfoMap.contains(field)) {
            fieldClass = fieldInfoMap(field).specificClass
          } else {
            if (field.getType.isInstanceOf[RefType]) {
              fieldClass = field.getType.asInstanceOf[RefType].getSootClass
              isPrim = false
            } else if (field.getType.isInstanceOf[PrimType]) {
              //原生类型不用处理
              isPrim = true
            } else if (field.getType.isInstanceOf[ArrayType]) {
              fieldClass = context.sootClass(field.getType.asInstanceOf[ArrayType].getElementType.toString)
              isPrim = false
            }
          }
          if (!isPrim) {
            edges.add(analyzeClass, fieldClass)
            if (!visited.contains(fieldClass)) {
              visit(fieldClass)
            }
          }
        }
      }
    }

    visit(analyzeClass)

    var points = visited.map(t => (t, 0))

    def DFSForCircuit(analyzeClass: SootClass): Unit = {
      points = points.filter(_._1.getName.equals(analyzeClass.getName)).+=((analyzeClass, -1))
      for (edge <- edges) {
        if (edge._1.getName.equals(analyzeClass.getName)) {
          if (points.contains((edge._2, -1))) {
            isDAG = false
            return
          } else if (points.contains((edge._2, 0))) {
            DFSForCircuit(edge._2)
          } else {
            return
          }
        }
      }
      points = points.filter(!_._1.getName.equals(analyzeClass.getName)).+=((analyzeClass, 1))

    }

    DFSForCircuit(analyzeClass)
    !isDAG
  }

  /**
    * 判断是否该字段可赋值
    *
    * @param className
    * @param fieldName
    * @param context
    * @return
    */
  private def isNoAssignableByField(className: String, fieldName: String, context: Context): Boolean = {
    val appClass = context.sootClass(className)
    var result = true
    val field = appClass.getFieldByName(fieldName)
    if (field.isFinal)
      result = true
    else {
      for (method <- appClass.getMethods if (!method.getName.contains("<init>")) && (!method.isNative) && (method.hasActiveBody)) {
        for (assign@(_a: JAssignStmt) <- method.getActiveBody.getUnits) {
          val leftOp = assign.getLeftOp
          if (leftOp.isInstanceOf[FieldRef]) {
            val fieldRef = leftOp.asInstanceOf[FieldRef]
            if (fieldRef.getFieldRef.name().equals(fieldName) && fieldRef.getFieldRef.declaringClass().equals(className))
              result = false
          }
        }
      }
    }
    result
  }


}
