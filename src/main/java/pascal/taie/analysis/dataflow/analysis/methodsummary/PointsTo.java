package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.TypeSystem;

import static pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.PUtil.getPointerMethod;

public class PointsTo {

    private Contr mergedContr;

    private TypeSystem typeSystem = World.get().getTypeSystem();

    public PointsTo() {
    }

    public static PointsTo make() {
        return new PointsTo();
    }

    /**
     * merget the contr
     */
    public boolean add(Contr contr) {
        if (contr == null) return false;
        if (mergedContr == null) {
            mergedContr = contr;
            return true;
        } else {
            if (mergedContr.isNew() && contr.isNew()) {
                if ((typeSystem.isSubtype(contr.getType(), mergedContr.getType()) && !mergedContr.getType().equals(contr.getType()))
                        || (ContrUtil.isControllable(contr) && !ContrUtil.isControllable(mergedContr))) {
                    mergedContr = contr;
                    return true;
                } else if (!typeSystem.isSubtype(mergedContr.getType(), contr.getType())) {
                    mergedContr.addNewType(contr.getType()); // for new objects that are not in sub-class
                    return true;
                }
            } else if (ContrUtil.needUpdateInMerge(mergedContr.getValue(), contr.getValue())) {
                mergedContr = contr;
                return true;
            }
        }

        JMethod method = getPointerMethod(contr.getOrigin()); // prefer string rather than map, Click
        if (ContrUtil.isControllableParam(mergedContr) && ContrUtil.isControllableParam(contr)) {
            int op = ContrUtil.string2Int(mergedContr.getValue());
            int np = ContrUtil.string2Int(contr.getValue());
            if (isParamType(method, op, "java.util.Map")
                    && isParamType(method, np, "java.lang.String")
                    && ContrUtil.hasCS(contr.getValue())
                    && !ContrUtil.hasCS(mergedContr.getValue())) {
                mergedContr = contr;
                return true;
            }
        }
        return false;
    }

    private boolean isParamType(JMethod method, int oc, String type) {
        try {
            return method.getParamTypes().get(oc).getName().equals(type);
        } catch (Exception e) {
            return false;
        }
    }

    public void add(PointsTo pointsTo) {
        add(pointsTo.getMergedContr());
    }

    public Contr getMergedContr() {
        return mergedContr;
    }

    public boolean isEmpty() {
        return mergedContr == null;
    }

    public void setValue(String s) {
        mergedContr.setValue(s);
    }
}
