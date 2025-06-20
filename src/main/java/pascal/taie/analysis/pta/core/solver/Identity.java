package pascal.taie.analysis.pta.core.solver;

import pascal.taie.analysis.pta.pts.PointsToSet;

public enum Identity implements Transfer {

    INSTANCE;

    public static Transfer get() {
        return INSTANCE;
    }

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        return input;
    }

}
