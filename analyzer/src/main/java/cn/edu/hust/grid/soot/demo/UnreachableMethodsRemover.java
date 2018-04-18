package cn.edu.hust.grid.soot.demo;

import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

/**
 * Created by Administrator on 2015/7/21.
 */
public class UnreachableMethodsRemover extends SceneTransformer
{

    protected void internalTransform(String phaseName, Map options){

        // make list of all unreachable methods
        ArrayList<SootMethod> methodList = new ArrayList<SootMethod>();

        Iterator getClassesIt = Scene.v().getApplicationClasses().iterator();
        while (getClassesIt.hasNext()) {
            SootClass appClass = (SootClass)getClassesIt.next();

            Iterator getMethodsIt = appClass.getMethods().iterator();
            while (getMethodsIt.hasNext()) {
                SootMethod method = (SootMethod)getMethodsIt.next();
                //System.out.println("adding  method: "+method);
                if (!Scene.v().getReachableMethods().contains(method)){
                    methodList.add(method);
                }
            }
        }

        // tag unused methods
        Iterator<SootMethod> unusedIt = methodList.iterator();
        while (unusedIt.hasNext()) {
            SootMethod unusedMethod = unusedIt.next();
            unusedMethod.getDeclaringClass().removeMethod(unusedMethod);

        }
    }

}
