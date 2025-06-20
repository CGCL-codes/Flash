package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;

import java.util.*;

/**
 * Graph that only contains gadget node
 */

public class GadgetChainGraph {

    private Map<String, GadgetChainNode> adjList;

    private static int PATH_COLLECT_TIME = World.get().getOptions().getGCGraph_COLLECT_TIME() * 1000;

    private static final Logger logger = LogManager.getLogger(GadgetChainGraph.class);

    private final LRUCache<String, Set<List<Edge>>> pathCache = new LRUCache<>(1000);

    public GadgetChainGraph() {
        this.adjList = new HashMap<>();
    }

    public boolean addPath(List<Edge> path) {
        boolean add = false;
        int size = path.size();
        for (int i = 0; i < size; i++) {
            String node = CSCallGraph.getCaller(path.get(i)).toString();
            if (!adjList.containsKey(node)) {
                add = true;
                adjList.put(node, new GadgetChainNode(node));
            }
            addEdge(node, path.get(i));
        }
        String sink = CSCallGraph.getCallee(path.get(size - 1)).toString();
        if (!adjList.containsKey(sink)) {
            add = true;
            adjList.put(sink, new GadgetChainNode(sink));
        }
        return add;
    }

    private void addEdge(String from, Edge edge) {
        adjList.get(from).addNext(edge);
    }

    public Set<List<Edge>> collectPath(String from) {
        if (pathCache.containsKey(from)) {
            return pathCache.get(from);
        }
        Set<List<Edge>> paths = new HashSet<>();
        List<Edge> path = new ArrayList<>();
        long startTime = System.currentTimeMillis();
        for (Edge edge : adjList.get(from).getNexts()) {
            Set<String> visited = new HashSet<>();
            visited.add(from);
            String callee = CSCallGraph.getCallee(edge).toString();
            dfsCollectPaths(callee, edge, visited, path, paths, startTime);
        }
//        long endTime = System.currentTimeMillis();
//        logger.info("collect {} path in {}s", paths.size() , (endTime - startTime) / 1000);
        pathCache.put(from, paths);
        return paths;
    }

    private void dfsCollectPaths(String current, Edge edge, Set<String> visited, List<Edge> path, Set<List<Edge>> paths, long startTime) {
        if (visited.contains(current) || !adjList.containsKey(current) || System.currentTimeMillis() - startTime > PATH_COLLECT_TIME) return; // System.currentTimeMillis() - startTime > PATH_COLLECT_TIME

        visited.add(current);
        path.add(edge);
        boolean isSink = adjList.get(current).isLeaf();

        if (isSink) {
            paths.add(new ArrayList<>(path));
        } else if (path.size() == GCCollectorInProcess.MAX_LEN) {
            path.remove(path.size() - 1);
            visited.remove(current);
            return;
        }

        for (Edge nextEdge : adjList.get(current).getNexts()) {
            String callee = CSCallGraph.getCallee(nextEdge).toString();
            dfsCollectPaths(callee, nextEdge, visited, path, paths, startTime);
        }

        path.remove(path.size() - 1);
        visited.remove(current);
    }

    public boolean containsNode(String key) {
        return adjList.containsKey(key);
    }
}

