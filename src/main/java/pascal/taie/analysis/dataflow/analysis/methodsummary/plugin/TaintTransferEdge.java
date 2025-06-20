package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.solver.OtherEdge;

public class TaintTransferEdge extends OtherEdge {

    private boolean isNewTransfer;

    public TaintTransferEdge(Pointer source, Pointer target, boolean isNewTransfer) {
        super(source, target);
        this.isNewTransfer = isNewTransfer;
    }

    public boolean isNewTransfer() {
        return this.isNewTransfer;
    }
}
