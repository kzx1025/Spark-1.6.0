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
public class UnreachableClassesRemover extends SceneTransformer
{

    protected void internalTransform(String phaseName, Map options){

        // make list of all unreachable methods
        ArrayList<SootClass> classList = new ArrayList<SootClass>();

        Iterator getClassesIt = Scene.v().getApplicationClasses().iterator();
        while (getClassesIt.hasNext()) {
            SootClass appClass = (SootClass)getClassesIt.next();

            if (appClass.getFieldCount() == 0 && appClass.getMethodCount() == 0) {
                classList.add(appClass);
            }

        }

        // tag unused methods
        Iterator<SootClass> unusedIt = classList.iterator();
        while (unusedIt.hasNext()) {
            SootClass unusedClass = unusedIt.next();
            Scene.v().removeClass(unusedClass);
        }
    }

}
