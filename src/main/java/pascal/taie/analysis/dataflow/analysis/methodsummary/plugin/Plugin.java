package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.language.classes.JMethod;

import java.util.Stack;

public interface Plugin {

    Plugin DUMMY = new Plugin() {};

    /**
     * Invoked when analysis starts.
     */
    default void onStart() {
    }

    /**
     * Invoked when analysis finishes.
     */
    default void onFinish() {
    }


    default void onNewInit(JMethod method) {
    }

    /**
     * first analyze deserialization-related methods
     */
    default void onNewDeser(JMethod method) {
    }
}
