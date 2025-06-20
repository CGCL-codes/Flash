package pascal.taie.analysis.dataflow.analysis.methodsummary.Utils;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.dataflow.analysis.ContrAlloc;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Contr;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.Strings;

import java.util.ArrayList;
import java.util.List;

public class ContrUtil {

    public static final int iTHIS = -1;

    public static final int iPOLLUTED = -2;

    public static final int iNOT_POLLUTED = -3;

    public static final String sTHIS = "this";

    public static final String sPOLLUTED = "polluted";

    public static final String sNOT_POLLUTED = "null";

    public static final String sParam = "param";

    private static final Logger logger = LogManager.getLogger(ContrUtil.class);

    public static String int2String(int i) {
        if (i >= 0) return sParam + "-" + i;
        else if (i == iTHIS) return sTHIS;
        else if (i == iPOLLUTED) return sPOLLUTED;
        else return sNOT_POLLUTED;
    }

    public static int string2Int(String s) {
        try {
            if (s == null || s.equals(sNOT_POLLUTED)) return iNOT_POLLUTED;
            else if (s.contains(sPOLLUTED)) return iPOLLUTED;
            else if (s.contains(sTHIS)) return iTHIS;
            else if (s.contains(sParam)) return Strings.extractParamIndex(s);
        } catch (Exception e) {
            logger.info("[-] error parsing {}", s);
        }
        return iNOT_POLLUTED;
    }

    public static List<Integer> string2Int(List<String> values) {
        List<Integer> ret = new ArrayList<>();
        values.forEach(value -> ret.add(string2Int(value)));
        return ret;
    }

    public static boolean needUpdateInMerge(String oldV, String newV) {
        boolean oldc = isControllable(oldV);
        boolean newc = isControllable(newV);
        if (oldV == null) {
            return !newV.equals(sNOT_POLLUTED);
        } else if (newV.startsWith("new") && !oldV.contains("new") && !oldc) { // BeanShell
            return true;
        } else {
            if (!oldc && !newc) {
                return hasCS(newV);
            } else {
                return !oldc && newc;
            }
        }
    }

    /**
     * return whether value has constant string
     */
    public static boolean hasCS(String value) {
        if (value.contains("+")) {
            int start = 0;
            for (int i = 0; i < value.length(); i++) {
                if (value.charAt(i) == '+') {
                    String part = value.substring(start, i);
                    if (isConstString(part)) {
                        return true;
                    }
                    start = i + 1;
                }
            }
            String lastPart = value.substring(start);
            return isConstString(lastPart);
        } else {
            return isConstString(value);
        }
    }

    public static String getCS(String value) {
        if (value.contains("+")) {
            String ret = "";
            String[] parts = value.split("\\+");
            for (String part : parts) {
                if (isConstString(part)) {
                    ret = ret + part;
                }
            }
            return ret;
        } else {
            return value;
        }
    }

    public static boolean needUpdateInAppend(String left, String right) {
        return !right.equals(ContrUtil.sNOT_POLLUTED) && (isControllable(left) != isControllable(right) || (hasCS(right) && !right.equals(left)));
    }

    public static boolean isControllable(Contr contr) {
        return contr != null && isControllable(contr.getValue());
    }

    public static boolean isControllable(String value) {
        return string2Int(value) >= iPOLLUTED;
    }

    public static boolean isControllableParam(Contr contr) {
        if (contr == null) return false;
        else return isControllableParam(contr.getValue());
    }

    public static boolean isControllableParam(String value) {
        return string2Int(value) > iTHIS;
    }

    public static boolean isCallSite(String value) {
        return string2Int(value) >= iTHIS;
    }

    public static boolean isThis(String value) {
        return string2Int(value) == iTHIS;
    }

    private static boolean isConstString(String value) {
        return !isControllable(value) && !value.equals(sNOT_POLLUTED);
    }

    public static String convert2Reg(String v) {
        if (v.contains("+")) {
            StringBuilder ret = new StringBuilder();
            String[] parts = v.split("\\+");
            for (String p : parts) {
                if (isControllable(p) && !ret.toString().endsWith(".*")) {
                    ret.append(".*");
                } else {
                    ret.append(p);
                }
            }
            return ret.toString();
        } else if (isControllable(v)) {
            return ".*";
        } else if (!v.equals(sNOT_POLLUTED)) {
            return v;
        } else {
            return "";
        }
    }

    public static CSObj getObj(Pointer p, String value, HeapModel heapModel, Context context, CSManager csManager) {
        ContrAlloc alloc = new ContrAlloc(p, value);
        Obj obj = heapModel.getMockObj(Descriptor.CONTR_DESC, alloc, p.getType());
        return csManager.getCSObj(context, obj);
    }

    public static boolean isSerializableType(Type type) {
        if (type instanceof ClassType ct) {
            return ct.getJClass().isSerializable();
        } else if (type instanceof ArrayType at) {
            if (at.elementType() instanceof ClassType et) return et.getJClass().isSerializable();
            else return isSerializableType(at.elementType());
        } else if (type instanceof PrimitiveType) {
            return true;
        } else {
            return false;
        }
    }

    public static boolean allControllable(List<Integer> values) {
        return !values.contains(iNOT_POLLUTED);
    }

    public static String replaceContr(String old, String contr) {
        if (hasCS(old)) {
            String[] parts = old.split("\\+");
            String replace = parts[0];
            String left = replace;
            for (int i = 1; i < parts.length; i++) {
                String right = parts[i];
                if (needUpdateInAppend(left, right)) {
                    replace += "+" + (isControllable(right) ? contr : right);
                    left = right;
                }
            }
            return replace;
        } else {
            return contr;
        }
    }
}
