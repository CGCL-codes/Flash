package pascal.taie.analysis.dataflow.analysis.methodsummary.Utils;

import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.language.classes.JMethod;

public class PUtil {

    /**
     * the container method of a pointer
     */
    public static JMethod getPointerMethod(Pointer p) {
        if (p instanceof CSVar var) return var.getVar().getMethod();
        else if (p instanceof InstanceField iField) return iField.getBaseVar().getVar().getMethod();
        else if (p instanceof ArrayAccess array) return array.getBase().getMethod();
        else return null;
    }

}
