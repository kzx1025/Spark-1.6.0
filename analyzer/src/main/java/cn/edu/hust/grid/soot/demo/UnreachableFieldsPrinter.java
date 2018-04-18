package cn.edu.hust.grid.soot.demo;

import soot.*;
import soot.jimple.FieldRef;
import soot.tagkit.ColorTag;
import soot.tagkit.StringTag;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

/**
 * Created by Administrator on 2015/7/21.
 */
public class UnreachableFieldsPrinter extends SceneTransformer
{

    protected void internalTransform(String phaseName, Map options){

        // make list of all fields
        ArrayList<SootField> fieldList = new ArrayList<SootField>();

        Iterator getClassesIt = Scene.v().getApplicationClasses().iterator();
        while (getClassesIt.hasNext()) {
            SootClass appClass = (SootClass)getClassesIt.next();
            //System.out.println("class to check: "+appClass);
            Iterator getFieldsIt = appClass.getFields().iterator();
            while (getFieldsIt.hasNext()) {
                SootField field = (SootField)getFieldsIt.next();
                //System.out.println("adding field: "+field);
                fieldList.add(field);
            }
        }

        // from all bodies get all use boxes and eliminate used fields
        getClassesIt = Scene.v().getApplicationClasses().iterator();
        while (getClassesIt.hasNext()) {
            SootClass appClass = (SootClass)getClassesIt.next();
            Iterator mIt = appClass.getMethods().iterator();
            while (mIt.hasNext()) {
                SootMethod sm = (SootMethod)mIt.next();
                //System.out.println("checking method: "+sm.getName());
                if (!sm.hasActiveBody()) continue;
                if (!Scene.v().getReachableMethods().contains(sm)) continue;
                Body b = sm.getActiveBody();

                Iterator usesIt = b.getUseBoxes().iterator();
                while (usesIt.hasNext()) {
                    ValueBox vBox = (ValueBox)usesIt.next();
                    Value v = vBox.getValue();
                    if (v instanceof FieldRef) {
                        FieldRef fieldRef = (FieldRef)v;
                        SootField f = fieldRef.getField();

                        if (fieldList.contains(f)) {
                            int index = fieldList.indexOf(f);
                            fieldList.remove(index);
                            System.out.println("field: "+f + " used in " + sm);
                        }

                    }
                }

            }
        }

        // tag unused fields
        Iterator<SootField> unusedIt = fieldList.iterator();
        while (unusedIt.hasNext()) {
            SootField unusedField = unusedIt.next();
            //unusedField.addTag(new StringTag("Field "+unusedField.getName()+" is not used!", "Unreachable Fields"));
            //unusedField.addTag(new ColorTag(ColorTag.RED, true, "Unreachable Fields"));
            System.out.println("unused field: "+unusedField);

        }
    }

}
