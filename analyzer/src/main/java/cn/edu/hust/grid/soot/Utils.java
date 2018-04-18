package cn.edu.hust.grid.soot;

import soot.Body;
import soot.SootField;
import soot.Value;
import soot.util.Chain;

import java.io.File;
import java.util.Iterator;

/**
 * Created by peicheng on 15-8-4.
 */
public class Utils {
    public static final Body cloneSootBody(Body b) {
        return (Body) b.clone();
    }

    public static final Value cloneSootValue(Value v) {
        return (Value) v.clone();
    }

    public static final SootField cloneSootField(SootField s) {
        return new SootField(s.getName(), s.getType(), s.getModifiers());
    }

    public static final boolean ContainSameNameOfSootField(Chain<SootField> fields, String fieldName) {
        Iterator<SootField> iterator = fields.iterator();
        while (iterator.hasNext()) {
            SootField sf = iterator.next();
            if (sf.getName().equals(fieldName))
                return true;
        }
        return false;
    }

    public static boolean deleteDirectory(String sPath) {
        //如果sPath不以文件分隔符结尾，自动添加文件分隔符
        if (!sPath.endsWith(File.separator)) {
            sPath = sPath + File.separator;
        }
        File dirFile = new File(sPath);
        //如果dir对应的文件不存在，或者不是一个目录，则退出
        if (!dirFile.exists() || !dirFile.isDirectory()) {
            return false;
        }
        boolean flag = true;
        //删除文件夹下的所有文件(包括子目录)
        File[] files = dirFile.listFiles();
        for (int i = 0; i < files.length; i++) {
            //删除子文件
            if (files[i].isFile()) {
                flag = deleteFile(files[i].getAbsolutePath());
                if (!flag) break;
            } //删除子目录
            else {
                flag = deleteDirectory(files[i].getAbsolutePath());
                if (!flag) break;
            }
        }
        if (!flag) return false;
        //删除当前目录
        if (dirFile.delete()) {
            return true;
        } else {
            return false;
        }
    }

    public static boolean deleteFile(String sPath) {
        boolean flag = false;
        File file = new File(sPath);
        // 路径为文件且不为空则进行删除
        if (file.isFile() && file.exists()) {
            file.delete();
            flag = true;
        }
        return flag;
    }

}
