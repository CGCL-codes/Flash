package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.pta.core.cs.element.Pointer;

public record ContrAlloc(Pointer pointer, String contr) {

    @Override
    public String toString() {
        return pointer.toString() + "/" + contr;
    }
}
