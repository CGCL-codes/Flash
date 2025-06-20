package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.language.classes.JMethod;

public record TaintTransfer(JMethod method, IndexRef from, IndexRef to, String type, boolean isNewTransfer) {

    @Override
    public String toString() {
        return method + ": " + from + " -> " + to + "(" + type + ")";
    }

}
