package cn.edu.hust.grid.deca;

/**
 * 专门存放字段类型的类，目前只包括原生类型
 */
public class FieldTypeName {
    private static final String INTKEY = "INTEGER";
    private static final String LONGKEY = "LONG";
    private static final String DOUBLEKEY = "DOUBLE";
    private static final String STRINGKEY = "STRING";

    private static final String INT="int";
    private static final String LONG="long";
    private static final String DOUBLE="double";
    private static final String STRING="string";

    public static String getFieldTypeName(String key){
        String value=null;
        if (INTKEY.equals(key)) {
            value = getINT();
        } else if (LONGKEY.equals(key)) {
            value = getLONG();
        } else if (DOUBLEKEY.equals(key)) {
            value = getDOUBLE();
        } else if (STRINGKEY.equals(key)) {
            value = getSTRING();
        }
        return value;
    }


    public static String getINT() {
        return INT;
    }

    public static String getLONG() {
        return LONG;
    }

    public static String getDOUBLE() {
        return DOUBLE;
    }

    public static String getSTRING() {
        return STRING;
    }
}
