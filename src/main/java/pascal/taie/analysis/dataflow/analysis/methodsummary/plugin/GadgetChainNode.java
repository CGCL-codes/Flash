package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.analysis.graph.callgraph.Edge;

import java.util.*;

public class GadgetChainNode {

    private Set<Edge> nexts;

    public String name;

    public GadgetChainNode(String name) {
        this.name = name;
        this.nexts = new HashSet<>();
    }

    public void addNext(Edge edge) {
        nexts.add(edge);
    }

    public boolean isLeaf() {
        return nexts.isEmpty();
    }

    public Set<Edge> getNexts() {
        return nexts;
    }

    @Override
    public String toString() {
        return name;
    }
}
