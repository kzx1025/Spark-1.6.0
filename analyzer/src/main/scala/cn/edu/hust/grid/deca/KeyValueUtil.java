package cn.edu.hust.grid.deca;

import cn.edu.hust.grid.soot.optimize.FieldInfo;
import org.json.JSONArray;
import org.json.JSONObject;
import soot.SootField;

import java.util.*;

/**
 * {
 "keyType":[
 {
 "topClassTag":<类全限定名称>,                        //顶层类名称，用于记录拆解的类名
 "numClassField":<number>,                            //非原生类型的json对象数量
 "numPrimitiveField":<number>,                        //原生类型的json对象数量
 "primitiveFieldClassTag":[<原生类型0>,<原生类型1>,...],//原生类型的信息
 "classFieldClassTag":[{ "topClassTag":<类全限定名称>,  //非原生类型按照上一层的处理逻辑
 "numClassField":<number>,
 "numPrimitiveField":<number>,
 ...逻辑同上一层...
 },
 {...},
 {...}]
 }

 ],
 "valueType":[
 {
 "topClassTag":<类全限定名称>,
 "numClassField":<number>,
 "numPrimitiveField":<number>,
 "primitiveFieldClassTag":[<原生类型0>,<原生类型1>,...],
 "classFieldClassTag":[{ "topClassTag":<类全限定名称>,
 "numClassField":<number>,
 "numPrimitiveField":<number>,
 ...逻辑同上一层...
 },
 {...},
 {...}]
 }
 }
 结构说明：第一层是一个花括号括号，即JsonObject对象，然后这个对象里面有两个JsonArray数组，分别是keyType和valueType。
 第二层以keyType的JsonArray为例说明，里面有五个属性，“topClassTag”，“numClassField”，“numPrimitiveField”，
 “primitiveFieldClassTag”，“classFieldClassTag”
 第三层对于classFieldClassTag的JsonArray，数组里面的每一个元素都按照上一层的处理逻辑处理
 例子：以WC为例说明：
 {"valueType":[
 {"classFieldClassTag":[],               //没有非原生类型
 "numPrimitiveField":1,                 //原生类型字段的数量为1
 "numClassField":0,                     //非原生类型的字段的数量为0
 "primitiveFieldClassTag":["int"],      //原生类型的字段数量为1，是int类型
 "topClassTag":"java.lang.Object"       //顶层类的类名是：java.lang.Object
 }
 ],
 "keyType":[
 {"classFieldClassTag":[],               //没有非原生类型
 "numPrimitiveField":1,                 //原生类型字段的数量为1
 "numClassField":0,                     //非原生类型的字段的数量为0
 "primitiveFieldClassTag":["string"],   //原生类型的字段数量为1，是string类型
 "topClassTag":"java.lang.Object"       //顶层类的类名是：java.lang.Object
 }
 ]
 }
 */
public class KeyValueUtil {
    /**
     * 获取key和value的信息
     * 如果不是_1 _2的格式 说明不是shuffle的fieldInfoMap 则我们返回null
     * @param fieldInfoMap  包含字段和字段信息的map
     * @return 若fieldInfoMap不为空，返回包含key和Value的信息的Json对象，否则返回null
     */
    public static String putKeyAndValueType(Map<SootField, FieldInfo> fieldInfoMap) {
        JSONObject jsonObject = new JSONObject();
        if (fieldInfoMap == null) {
            return null;
        }
        FieldInfo keyFieldInfo = null, valueFieldInfo = null;
        String keyDeclaredClassName = null, valueDeclaredClassName = null;
        Iterator<Map.Entry<SootField, FieldInfo>> fieldInfoMapIterator = fieldInfoMap.entrySet().iterator();
        while (fieldInfoMapIterator.hasNext()) {
            Map.Entry<SootField, FieldInfo> fieldInfoTuple = fieldInfoMapIterator.next();
            if ("_1".equals(fieldInfoTuple.getKey().getName())) {
                keyFieldInfo = fieldInfoTuple.getValue();
                keyDeclaredClassName = fieldInfoTuple.getKey().getType().toString();
            } else if ("_2".equals(fieldInfoTuple.getKey().getName())) {
                valueFieldInfo = fieldInfoTuple.getValue();
                valueDeclaredClassName = fieldInfoTuple.getKey().getType().toString();
            } else {
                return null;
            }
        }
        //添加keyTypeInfo到jsonObject
        List<Object> keyTypeInfo = getTypeInfo(keyFieldInfo, keyDeclaredClassName);
        jsonObject.put("keyType", keyTypeInfo);

        //添加valueTypeInfo到jsonObject
        List<Object> valueTypeInfo = getTypeInfo(valueFieldInfo, valueDeclaredClassName);
        jsonObject.put("valueType", valueTypeInfo);

        System.out.println(jsonObject.toString());

        return jsonObject.toString();
    }

    /**
     * 统计字段的信息
     * @param fieldInfo      字段信息
     * @param declaredClass  字段的topClass
     * @return  若字段信息不为空，返回包含字段信息的List，否则返回null
     */
    public static List<Object> getTypeInfo(FieldInfo fieldInfo, String declaredClass) {
        if (fieldInfo == null) {
            return null;
        }
        List<Object> typeInfoList = new ArrayList<Object>();
        Map<String, Object> typeInfoMap = new HashMap<String, Object>();
        List<String> primitiveFieldClassTagList = new ArrayList<String>();
        List<Object> classFieldClassTagList = new ArrayList<Object>();

        int numClassFiled = 0;
        int numPrimitiveField = 0;


        String type = fieldInfo.specificClass().getShortName();
        type = type.toUpperCase();
        if (FieldTypeName.getFieldTypeName(type) != null) {
            primitiveFieldClassTagList.add(FieldTypeName.getFieldTypeName(type));
            numPrimitiveField++;
        } else {
            numClassFiled++;
            for (int i = 0; i < fieldInfo.childFieldInfos().size(); i++) {
                classFieldClassTagList.add(getTypeInfo(fieldInfo.childFieldInfos().get(i), fieldInfo.specificClass().getName()));
            }
        }
        typeInfoMap.put("topClassTag", declaredClass);
        typeInfoMap.put("numPrimitiveField", numPrimitiveField);
        typeInfoMap.put("numClassFiled", numClassFiled);
        typeInfoMap.put("primitiveFieldClassTag", primitiveFieldClassTagList);
        typeInfoMap.put("classFieldClassTag", classFieldClassTagList);
        typeInfoList.add(typeInfoMap);
        return typeInfoList;
    }

    /**
     * a example for parseJson
     * @param jsonInfo
     */
    public static void parseJson(String jsonInfo) {
        if (jsonInfo == null) {
            return;
        }
        JSONObject jsonObject = new JSONObject(jsonInfo);
        JSONArray keyTypeList = jsonObject.getJSONArray("keyType");
        JSONObject keyTypeMap = keyTypeList.getJSONObject(0);
        String topClassTag = keyTypeMap.getString("topClassTag");
        int numPrimitiveField = keyTypeMap.getInt("numPrimitiveField");
        int numClassField = keyTypeMap.getInt("numClassField");

        System.out.println(topClassTag + ":" + numClassField + ":" + numPrimitiveField);
        JSONArray primitiveFieldClassTagList = keyTypeMap.getJSONArray("primitiveFieldClassTag");
        System.out.println("primitiveFieldClassTag:");
        for (int i = 0; i < primitiveFieldClassTagList.length(); i++) {
            System.out.println(primitiveFieldClassTagList.get(i));
        }
        JSONArray classFieldClassTagList = keyTypeMap.getJSONArray("classFieldClassTag");
        for (int i = 0; i < classFieldClassTagList.length(); i++) {
            parseJson(classFieldClassTagList.get(i).toString());
        }
    }
}
