package pascal.taie.analysis.pta.core.solver;

import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.Type;

public class SpecialType implements Transfer {

    private Type type;

    public SpecialType(Type type) {
        this.type = type;
    }

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        return null;
    }

    public Type getType() {
        return type;
    }

}
