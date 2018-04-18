package cn.edu.hust.grid.soot.optimize

import java.io._

import cn.edu.hust.grid.soot.optimize.SizeType._
import soot.jimple.InvokeExpr
import soot.jimple.internal.{AbstractDefinitionStmt, InvokeExprBox}
import soot.jimple.toolkits.callgraph.{CHATransformer, CallGraph, ReachableMethods}
import soot.options.Options
import soot.toolkits.scalar.ConstantValueToInitializerTransformer
import soot.util.{Chain, EscapedWriter, JasminOutputStream}
import soot.{Unit => SootUnit, _}

import scala.collection.JavaConversions._
import scala.collection.mutable

/**
  * Created by Administrator on 2015/7/20.
  */
class Context(
               var mainClass: String = "",
               var entryMethod: String = "",
               includeClasses: Seq[String] = Nil,
               excludePackages: Seq[String] = Nil,
               preload: Boolean = false,
               classpath: String = System.getProperty("java.class.path")) {

  val decomposeWorkingList: mutable.Queue[String] = mutable.Queue.empty[String]
  val fusionClassList: mutable.Queue[String] = mutable.Queue.empty[String]
  val classifyMap: mutable.Map[String, SizeType] = mutable.HashMap.empty[String, SizeType]

  G.reset()
  //println(classpath)
  options.set_soot_classpath(classpath)
  //options.set_throw_analysis(Options.throw_analysis_pedantic)

  addIncludeClasses(includeClasses)
  addExcludePackages(List() ++ excludePackages)

  if (!mainClass.isEmpty) {
    options.classes.add(mainClass)
    options.set_main_class(mainClass)
    options.set_allow_phantom_refs(true)
    options.set_no_bodies_for_excluded(true)
    options.set_whole_program(true)
    options.set_app(true)

    loadNecessaryClasses(preload)

    retrieveAllBodies()
  } else {
    scene.loadBasicClasses()
    if (preload) loadLibClasses()
  }


  private def loadNecessaryClasses(preload: Boolean) {
    scene.loadBasicClasses()
    if (preload) loadLibClasses()
    options.set_dynamic_class(List("java.lang.String"))
    scene.loadDynamicClasses()
    loadAppClasses()
  }

  private def loadLibClasses() {
    for (className <- Context.prelibraryClasses) {
      val c = scene.loadClass(className, SootClass.SIGNATURES)
      c.setLibraryClass()
    }
  }

  private def loadAppClasses() {
    for (className <- Options.v.classes) {
      loadClass(className)
    }

    prepareClasses()
    scene.setDoneResolving()
  }

  private def prepareClasses() {
    val prepareClasses = scene.getClass.getDeclaredMethod("prepareClasses")
    prepareClasses.setAccessible(true)
    prepareClasses.invoke(scene)
    prepareClasses.setAccessible(false)
  }

  private def unsetDoneResolving() {
    val doneResolving = scene.getClass.getDeclaredField("doneResolving")
    doneResolving.setAccessible(true)
    doneResolving.setBoolean(scene, false)
    doneResolving.setAccessible(false)
  }

  private def addIncludeClasses(classes: Seq[String]): Unit = {
    if (options.include().isEmpty) {
      options.set_include(new java.util.ArrayList[String]())
    }
    for (name <- classes) {
      options.include().add(name)
    }
  }

  private def addExcludePackages(packages: Seq[String]): Unit = {
    if (options.exclude().isEmpty) {
      options.set_exclude(new java.util.ArrayList[String]())
    }
    for (name <- packages) {
      options.exclude().add(name)
    }
  }

  def scene: Scene = Scene.v

  def options: Options = Options.v

  def packManager: PackManager = PackManager.v

  def classes: Chain[SootClass] = scene.getClasses

  def applicationClasses: Chain[SootClass] = scene.getApplicationClasses

  def libraryClasses: Chain[SootClass] = scene.getLibraryClasses

  def hierarchy: FastHierarchy = scene.getOrMakeFastHierarchy

  def sootClass(className: String): SootClass = {
    try {
      var result = scene.getSootClassUnsafe(className)
      if (result == null || result.resolvingLevel() < SootClass.BODIES) {
        loadClass(className, true)
        //retrieveAllBodies()
        result = scene.getSootClass(className)
      }
      result
    } catch {
      case e: RuntimeException => throw OptimizeException(e.getMessage)
    }
  }

  def callGraph: CallGraph = {
    try {
      scene.getCallGraph
    } catch {
      case e: RuntimeException => throw OptimizeException(e.getMessage)
    }
  }

  def reachableMethods: ReachableMethods = {
    try {
      scene.getReachableMethods
    } catch {
      case e: RuntimeException => throw OptimizeException(e.getMessage)
    }
  }

  private def retrieveAllBodies() {
    for (sootClass <- applicationClasses.snapshotIterator) {
      for (method <- sootClass.getMethods) {
        if (method.isConcrete) {
          method.retrieveActiveBody
        }
      }
    }
  }

  def removeClass(sootClass: SootClass): Unit = scene.removeClass(sootClass)

  def validateTypeMatch(): Unit = {
    def matchTypes(left: Type, right: Type): Unit = {
      if (left.isInstanceOf[RefLikeType] &&
        left != right &&
        NullType.v != right) {
        throw OptimizeException(left + " does not match " + right)
      }
    }

    for (sootClass <- applicationClasses.iterator) {
      for (method <- sootClass.getMethods) {
        for (assign@(_a: AbstractDefinitionStmt) <- method.getActiveBody.getUnits) {
          val leftType = assign.getLeftOp.getType
          val rightType = assign.getRightOp.getType
          matchTypes(leftType, rightType)
        }

        for (box@(_b: InvokeExprBox) <- method.getActiveBody.getUseBoxes) {
          val invoke = box.getValue.asInstanceOf[InvokeExpr]
          for ((leftType, rightType) <- invoke.getMethod.getParameterTypes.zip(invoke.getArgs.map(_.getType))) {
            matchTypes(leftType, rightType)
          }
        }
      }
    }
  }

  def buildCallGraph(): Unit = {
    val foundMethod = scene.getSootClass(mainClass).
      getMethodByNameUnsafe(entryMethod)
    if (foundMethod == null) throw OptimizeException("does not found entry method")
    scene.loadBasicClasses()
    scene.loadDynamicClasses()
    scene.setEntryPoints(List(foundMethod))
    scene.setReachableMethods(null)

    //validateTypeMatch()
    scene.setCallGraph(null)
    CHATransformer.v.transform()

  }

  def runBodyPacks(): Unit = {
    PackManager.v.runBodyPacks()
  }



  def writeOutput(writeJimple: Boolean = true): Unit = {
    for (appClass <- applicationClasses) {
      val name = appClass.getName
      appClass.setName(name)
      appClass.getType.setClassName(name)
      println(name)
    }

    if (writeJimple) {
      options.set_output_format(Options.output_format_jimple)
      options.set_no_writeout_body_releasing(true)
    //  PackManager.v.writeOutput()
    }
    //options.set_output_dir("flint/target/scala-2.10/classes")
    //options.set_output_format(Options.output_format_class)
    options.set_output_jar(true)
    options.set_no_writeout_body_releasing(true)
    PackManager.v.writeOutput()
  }

  def writeJimple(): Unit={
    for (appClass <- applicationClasses) {
      val name = appClass.getName
      appClass.setName(name)
      appClass.getType.setClassName(name)
      println(name)
    }
    options.set_output_format(Options.output_format_jimple)
    options.set_no_writeout_body_releasing(true)
    PackManager.v.writeOutput()
  }


  def writeOutput(funcClass: SootClass): Unit = {
    options.set_output_format(Options.output_format_jimple)
    val writeMethod = PackManager.v().getClass.getDeclaredMethod("writeClass",funcClass.getClass)
    writeMethod.setAccessible(true)
    writeMethod.invoke(PackManager.v(),funcClass)

    options.set_output_format(Options.output_format_class)
    val writeMethod2 = PackManager.v().getClass.getDeclaredMethod("writeClass",funcClass.getClass)
    writeMethod2.setAccessible(true)
    writeMethod2.invoke(PackManager.v(),funcClass)
  }
  def writeJimple(funcClass:SootClass):Unit={
    options.set_output_format(Options.output_format_jimple)
    val writeMethod = PackManager.v().getClass.getDeclaredMethod("writeClass",funcClass.getClass)
    writeMethod.setAccessible(true)
    writeMethod.invoke(PackManager.v(),funcClass)
  }

  def removeAppClasses(): Unit = {
    for (appClass <- applicationClasses.toList) {
      removeClass(appClass)
    }
  }

  def clear(): Unit = {
    scene.setCallGraph(null)
    scene.setReachableMethods(null)
    removeAppClasses()

    mainClass = ""
    entryMethod = ""
    options.classes.clear()
    options.set_main_class("")

    unsetDoneResolving()
  }

  def reset(_mainClass: String = "", _entryMethod: String = "", needClear: Boolean = true): Unit = {
    if (needClear) clear()

    mainClass = _mainClass
    entryMethod = _entryMethod

    if (!mainClass.isEmpty) {
      options.classes.add(mainClass)
      options.set_main_class(mainClass)

      options.set_allow_phantom_refs(true)

      options.set_whole_program(true)
      options.set_app(true)

      loadAppClasses()
      retrieveAllBodies()
    }
  }

  def loadAppClass(className: String) {
    unsetDoneResolving()
    loadClass(className, true)
    prepareClasses()
    scene.setDoneResolving()
  }

  def loadClass(className: String, retrieveBody: Boolean = false) {
    val c = scene.loadClassAndSupport(className)
    c.setApplicationClass()
    if (retrieveBody) {
      for (method <- c.getMethods) {
        if (method.isConcrete) {
          method.retrieveActiveBody
        }
      }
    }
  }
}

object Context {
  val prelibraryClasses = List("scala.collection.immutable.Iterable",
    "sun.reflect.generics.repository.GenericDeclRepository",
    "java.util.Properties",
    "java.lang.ref.Reference",
    "scala.collection.GenSeqLike",
    "java.lang.NoSuchFieldError",
    "java.lang.UnknownError",
    "org.apache.spark.util.ListenerBus",
    "java.lang.ClassCircularityError",
    "java.lang.Integer",
    "java.lang.Package",
    "org.apache.spark.storage.RDDInfo",
    "java.lang.Thread",
    "scala.reflect.ClassManifestDeprecatedApis",
    "java.util.Hashtable",
    "java.lang.OutOfMemoryError",
    "org.apache.spark.scheduler.LiveListenerBus",
    "scala.collection.mutable.HashTable",
    "scala.collection.mutable.Traversable",
    "org.apache.hadoop.io.FloatWritable",
    "java.io.ObjectInput",
    "java.io.FilterOutputStream",
    "java.lang.CloneNotSupportedException",
    "sun.reflect.ReflectionFactory",
    "java.nio.charset.CharacterCodingException",
    "java.util.regex.PatternSyntaxException",
    "org.apache.spark.Accumulable",
    "java.lang.SecurityManager",
    "scala.collection.immutable.LinearSeq",
    "java.lang.ClassValue$ClassValueMap",
    "scala.Cloneable",
    "java.lang.Float",
    "java.lang.Class$SecurityManagerHelper",
    "org.apache.hadoop.conf.Configuration",
    "sun.reflect.generics.repository.ClassRepository",
    "org.apache.spark.api.java.JavaPairRDD",
    "org.xml.sax.SAXException",
    "java.io.PrintWriter",
    "java.lang.Short",
    "scala.collection.Iterable",
    "scala.collection.generic.GenericTraversableTemplate",
    "org.apache.spark.scheduler.SchedulerBackend",
    "org.apache.spark.TaskContext",
    "scala.Option$WithFilter",
    "java.lang.Long",
    "scala.collection.mutable.FlatHashTable$HashUtils",
    "org.apache.spark.partial.PartialResult",
    "scala.Function1",
    "scala.collection.mutable.IndexedSeq",
    "scala.collection.GenIterableLike",
    "java.lang.Runnable",
    "scala.collection.AbstractMap",
    "java.lang.InterruptedException",
    "java.util.Dictionary",
    "scala.collection.mutable.AbstractMap",
    "scala.collection.mutable.FlatHashTable",
    "java.nio.charset.MalformedInputException",
    "java.lang.Character",
    "org.apache.spark.AccumulableParam",
    "scala.collection.generic.Clearable",
    "scala.collection.GenIterable",
    "org.apache.spark.partial.ApproximateEvaluator",
    "java.lang.StringBuffer",
    "java.util.Comparator",
    "java.lang.reflect.Field",
    "java.io.Closeable",
    "scala.collection.mutable.SetLike",
    "org.apache.spark.api.java.function.Function",
    "scala.collection.LinearSeqLike",
    "scala.collection.generic.Subtractable",
    "sun.reflect.ConstantPool",
    "org.apache.spark.rdd.EmptyRDD",
    "java.net.URI",
    "scala.Some",
    "org.apache.spark.util.AsynchronousListenerBus",
    "java.lang.IllegalAccessException",
    "java.io.OutputStream",
    "java.lang.Class",
    "scala.collection.generic.FilterMonadic",
    "java.io.PrintStream",
    "scala.collection.IndexedSeqLike",
    "org.apache.spark.api.java.function.PairFunction",
    "java.lang.AutoCloseable",
    "scala.collection.immutable.MapLike",
    "org.apache.spark.util.MetadataCleaner",
    "java.lang.RuntimeException",
    "scala.collection.GenMap",
    "java.lang.reflect.AnnotatedElement",
    "org.apache.spark.unsafe.memory.TaskMemoryManager",
    "scala.Function3",
    "java.lang.Comparable",
    "scala.collection.Iterator$GroupedIterator",
    "scala.Product",
    "org.apache.spark.WritableFactory",
    "scala.collection.immutable.Traversable",
    "org.apache.spark.rdd.AsyncRDDActions",
    "java.util.AbstractMap",
    "sun.reflect.generics.factory.GenericsFactory",
    "java.lang.reflect.AccessibleObject",
    "java.io.DataOutput",
    "java.lang.NoSuchMethodError",
    "scala.collection.mutable.Seq",
    "scala.collection.mutable.Map",
    "java.lang.VirtualMachineError",
    "scala.collection.Map",
    "java.lang.VerifyError",
    "org.apache.spark.rdd.PairRDDFunctions",
    "scala.util.Either",
    "scala.Predef$$less$colon$less",
    "scala.concurrent.Awaitable",
    "org.apache.spark.SimpleFutureAction",
    "org.apache.spark.scheduler.SparkListenerBus",
    "scala.math.Ordering",
    "scala.collection.Traversable",
    "org.apache.hadoop.io.BytesWritable",
    "org.apache.spark.Partitioner",
    "scala.collection.Iterator",
    "scala.collection.CustomParallelizable",
    "org.apache.spark.rdd.DoubleRDDFunctions",
    "scala.collection.generic.GenericSetTemplate",
    "java.lang.ref.FinalReference",
    "org.apache.hadoop.mapred.JobConf",
    "java.lang.reflect.Member",
    "org.apache.spark.api.java.AbstractJavaRDDLike",
    "org.apache.spark.Accumulator",
    "scala.collection.IndexedSeqOptimized",
    "java.io.ObjectOutput",
    "java.lang.IllegalArgumentException",
    "scala.Function2",
    "java.lang.Class$ReflectionData",
    "java.io.ObjectInputStream",
    "scala.collection.immutable.Seq",
    "java.io.ObjectOutputStream",
    "java.util.Set",
    "scala.collection.mutable.StringBuilder",
    "java.lang.AbstractStringBuilder",
    "scala.collection.immutable.List",
    "org.apache.spark.util.TimeStampedWeakValueHashMap",
    "org.apache.spark.FutureAction",
    "java.util.Collection",
    "scala.collection.GenSet",
    "java.lang.StackOverflowError",
    "scala.collection.AbstractSeq",
    "java.util.Map",
    "org.apache.spark.scheduler.SparkListener",
    "org.apache.spark.api.java.function.Function2",
    "org.apache.spark.ui.jobs.JobProgressListener",
    "scala.Enumeration$Value",
    "java.lang.StackTraceElement",
    "java.lang.ref.Finalizer",
    "scala.collection.AbstractIterator",
    "scala.collection.immutable.Map",
    "org.apache.spark.scheduler.TaskScheduler",
    "scala.collection.mutable.AbstractIterable",
    "java.io.InvalidObjectException",
    "java.util.WeakHashMap",
    "java.io.UnsupportedEncodingException",
    "org.apache.spark.scheduler.DAGScheduler",
    "org.apache.spark.SparkContext",
    "java.lang.Boolean",
    "org.apache.spark.broadcast.Broadcast",
    "scala.collection.TraversableOnce",
    "scala.collection.GenMapLike",
    "scala.runtime.Nothing$",
    "org.apache.hadoop.io.LongWritable",
    "scala.collection.mutable.Cloneable",
    "org.apache.spark.util.CallSite",
    "org.apache.spark.rdd.OrderedRDDFunctions",
    "java.util.List",
    "scala.collection.GenTraversableOnce",
    "org.apache.spark.rdd.RDD",
    "java.net.URL",
    "sun.reflect.generics.repository.AbstractRepository",
    "scala.collection.generic.Shrinkable",
    "scala.collection.GenSetLike",
    "scala.collection.generic.Growable",
    "org.apache.spark.rdd.SequenceFileRDDFunctions",
    "java.io.Externalizable",
    "scala.Equals",
    "scala.collection.GenTraversableLike",
    "scala.collection.immutable.Vector",
    "java.lang.Error",
    "java.io.Serializable",
    "scala.collection.LinearSeqOptimized",
    "scala.collection.MapLike",
    "java.lang.ClassFormatError",
    "scala.collection.mutable.MapLike",
    "java.lang.IllegalMonitorStateException",
    "scala.concurrent.Future",
    "scala.collection.mutable.BufferLike",
    "scala.collection.mutable.Builder",
    "java.lang.Double",
    "scala.collection.Seq",
    "org.apache.hadoop.io.Writable",
    "java.io.StreamCorruptedException",
    "java.lang.Throwable",
    "java.lang.NoSuchFieldException",
    "scala.collection.Parallelizable",
    "java.io.FileNotFoundException",
    "java.lang.ref.SoftReference",
    "org.apache.spark.SparkConf",
    "java.util.concurrent.TimeoutException",
    "org.apache.spark.Partition",
    "scala.collection.immutable.Stream",
    "scala.collection.SeqLike",
    "java.io.Flushable",
    "scala.collection.mutable.IndexedSeqLike",
    "scala.collection.immutable.Set",
    "java.lang.Exception",
    "java.util.InvalidPropertiesFormatException",
    "scala.runtime.Null$",
    "java.lang.ArrayStoreException",
    "java.net.URISyntaxException",
    "org.apache.spark.storage.StorageLevel",
    "java.lang.reflect.TypeVariable",
    "java.lang.ArrayIndexOutOfBoundsException",
    "java.io.NotActiveException",
    "java.lang.NumberFormatException",
    "scala.collection.AbstractTraversable",
    "org.apache.spark.Logging",
    "scala.collection.script.Scriptable",
    "java.lang.ClassLoader",
    "java.io.ObjectStreamConstants",
    "java.lang.InheritableThreadLocal",
    "java.lang.AssertionError",
    "org.apache.spark.rdd.RDD$$anonfun$reduce$1",
    "scala.runtime.AbstractFunction1",
    "java.lang.IncompatibleClassChangeError",
    "scala.math.Equiv",
    "scala.reflect.OptManifest",
    "org.apache.spark.api.java.JavaRDDLike",
    "java.lang.IndexOutOfBoundsException",
    "java.lang.Throwable$PrintStreamOrWriter",
    "java.lang.reflect.Method",
    "java.lang.Number",
    "java.lang.InstantiationException",
    "java.io.DataInput",
    "scala.PartialFunction",
    "org.apache.hadoop.io.DoubleWritable",
    "java.lang.reflect.Type",
    "scala.math.Ordered",
    "java.lang.ClassCastException",
    "java.lang.reflect.InvocationTargetException",
    "scala.math.Numeric",
    "org.apache.spark.api.java.JavaRDD",
    "org.apache.spark.SparkStatusTracker",
    "scala.collection.SetLike",
    "java.lang.ThreadDeath",
    "java.lang.IllegalAccessError",
    "java.lang.Object",
    "scala.None$",
    "java.lang.InternalError",
    "sun.reflect.annotation.AnnotationType",
    "org.apache.hadoop.io.Text",
    "java.lang.NullPointerException",
    "java.util.concurrent.atomic.AtomicInteger",
    "scala.collection.AbstractIterable",
    "java.lang.reflect.GenericDeclaration",
    "java.lang.String",
    "scala.collection.mutable.HashSet",
    "scala.collection.mutable.SeqLike",
    "java.util.concurrent.atomic.AtomicBoolean",
    "java.lang.reflect.Constructor",
    "scala.collection.BufferedIterator",
    "org.apache.spark.mapreduce.SparkHadoopMapReduceUtil",
    "java.io.Writer",
    "java.lang.SecurityException",
    "org.apache.spark.metrics.MetricsSystem",
    "org.apache.spark.api.java.JavaPairRDD$",
    "scala.Product2",
    "scala.collection.mutable.Buffer",
    "scala.collection.GenSeq",
    "java.lang.InstantiationError",
    "scala.Immutable",
    "org.apache.spark.executor.TaskMetrics",
    "scala.collection.TraversableLike",
    "org.apache.spark.storage.StorageStatus",
    "java.lang.NegativeArraySizeException",
    "scala.collection.mutable.Iterable",
    "java.io.ObjectStreamField",
    "scala.collection.GenTraversable",
    "scala.collection.mutable.HashMap",
    "scala.collection.immutable.VectorPointer",
    "java.io.InputStream",
    "scala.collection.IndexedSeq",
    "java.lang.Void",
    "java.lang.ArithmeticException",
    "scala.collection.immutable.StringLike",
    "java.lang.UnsatisfiedLinkError",
    "scala.collection.generic.CanBuildFrom",
    "scala.collection.LinearSeq",
    "scala.collection.generic.HasNewBuilder",
    "scala.collection.mutable.HashTable$HashUtils",
    "java.lang.CharSequence",
    "java.util.EventListener",
    "java.io.IOException",
    "java.lang.ExceptionInInitializerError",
    "java.lang.ClassNotFoundException",
    "scala.Function0",
    "scala.runtime.AbstractFunction0",
    "org.slf4j.Logger",
    "scala.Mutable",
    "org.apache.hadoop.io.BooleanWritable",
    "org.apache.hadoop.io.IntWritable",
    "org.apache.spark.WritableConverter",
    "java.lang.Appendable",
    "scala.collection.mutable.Set",
    "org.apache.spark.util.TaskCompletionListener",
    "scala.collection.IterableLike",
    "org.apache.hadoop.io.WritableComparable",
    "java.security.ProtectionDomain",
    "java.lang.Class$EnclosingMethodInfo",
    "scala.collection.immutable.IndexedSeq",
    "java.lang.AbstractMethodError",
    "scala.Option",
    "java.lang.annotation.Annotation",
    "java.net.MalformedURLException",
    "java.lang.ReflectiveOperationException",
    "scala.collection.mutable.AbstractSeq",
    "java.lang.Cloneable",
    "java.lang.Byte",
    "scala.Tuple2",
    "java.lang.Iterable",
    "org.apache.spark.AccumulatorParam",
    "org.apache.spark.SparkEnv",
    "scala.collection.Set",
    "org.apache.spark.ExecutorAllocationClient",
    "scala.collection.mutable.AbstractSet",
    "scala.runtime.AbstractFunction2",
    "scala.math.PartialOrdering",
    "java.lang.NoClassDefFoundError",
    "scala.Serializable",
    "scala.Function4",
    "org.apache.hadoop.io.BinaryComparable",
    "org.apache.spark.rpc.RpcEndpointRef",
    "java.lang.ThreadLocal",
    "java.lang.NoSuchMethodException",
    "java.lang.LinkageError",
    "scala.reflect.ClassTag")
}
