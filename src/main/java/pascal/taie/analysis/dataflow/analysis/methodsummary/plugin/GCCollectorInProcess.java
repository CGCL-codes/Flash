package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.Strings;
import pascal.taie.util.collection.Lists;

import java.io.*;
import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * collect gadget chains during analyze by summary
 */

public class GCCollectorInProcess {

    private static final Logger logger = LogManager.getLogger(GCCollectorInProcess.class);

    private CSCallGraph csCallGraph;

    private TypeSystem typeSystem;

    private String output;

    public static final int MAX_LEN = World.get().getOptions().getGC_MAX_LEN();

    private Set<List<String>> GCs;

    private PrintWriter pw;

    private Stack<Edge> edgeStack;

    private GadgetChainGraph gcGraph;

    private Map<String, Set<Stack<Edge>>> tempGCMap;

    private ClassHierarchy hierarchy;

    public GCCollectorInProcess(CSCallGraph csCallGraph, String out_path) {
        super();
        this.gcGraph = new GadgetChainGraph();
        this.GCs = new HashSet<>();
        this.edgeStack = new Stack<>();
        this.csCallGraph = csCallGraph;
        this.typeSystem = World.get().getTypeSystem();
        this.output = out_path;
        this.tempGCMap = new HashMap<>();
        this.hierarchy = World.get().getClassHierarchy();
        try {
            File output_file = new File(World.get().getOptions().getOutputDir(), this.output);
            this.pw = new PrintWriter(new BufferedWriter(new FileWriter(output_file)));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void popEdge(JMethod method) {
        if (!edgeStack.isEmpty()) {
            Edge e = edgeStack.peek();
            JMethod callee = ((CSMethod) e.getCallee()).getMethod();
            if (method.equals(callee)) edgeStack.pop();
        }
    }

    public void pushCallEdge(Edge callEdge, boolean isInStack) {
        JMethod callee = CSCallGraph.getCallee(callEdge);
        String calleeSig = callee.toString();
        if (callee.isSink()) {
            recordGC(callEdge, callee);
        } else if (isInStack) {
            List<Edge> edgeList = backPropagate(callEdge, edgeStack, 1); // process after the summary is set
            if (!edgeList.isEmpty()) {
                Stack<Edge> edges = list2Stack(edgeList);
                tempGCMap.putIfAbsent(callee.toString(), new HashSet<>());
                tempGCMap.get(callee.toString()).add(edges);
            }
        } else if (callee.hasSummary()) {
            if (gcGraph.containsNode(calleeSig)) {
                Set<List<Edge>> toSinkEdges = gcGraph.collectPath(calleeSig);
                linkGC(callEdge, toSinkEdges, edgeStack);
            }
        } else {
            edgeStack.push(callEdge);
        }
    }

    public void handleTempGC(String key) {
        if (tempGCMap.containsKey(key)) {
            Set<Stack<Edge>> edgeLists = tempGCMap.remove(key);
            if (gcGraph.containsNode(key)) {
                Set<List<Edge>> toSinkEdges = gcGraph.collectPath(key);
                edgeLists.forEach(edges -> {
                    Edge edge = edges.pop();
                    linkGC(edge, toSinkEdges, edges);
                });
            }
        }
    }

    /**
     * handle to sink edge
     */
    private void recordGC(Edge sinkEdge, JMethod sink) {
        List<Integer> tcList = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());
        List<Edge> gcEdgeList = backPropagate(tcList, sinkEdge, edgeStack, 0);
        if (gcEdgeList.isEmpty()) return;

        if (!startWithSource(gcEdgeList)) {
            updateToSinkGC(gcEdgeList, false);
        } else {
            updateToSinkGC(gcEdgeList, true);
            if (!typeCheck(gcEdgeList)) return;
            List<Edge> simplyGC = simplyGC(gcEdgeList);
            if (addGC(simplyGC)) {
                logAndWrite(simplyGC);
            }
        }
    }

    /**
     * return the minimal usable partial gadget
     */
    private List<Edge> backPropagate(List<Integer> tcList, Edge initEdge, Stack<Edge> edges, int sinkLen) {
        List<Edge> edgeList = new ArrayList<>();
        List<Integer> tempNewTC = getNewTCList(tcList, initEdge.getCSIntContr());
        if (!ContrUtil.allControllable(tempNewTC)) return edgeList;
        edgeList.add(initEdge);
        int range = MAX_LEN - sinkLen - 1;
        for (int i = 0; i < range; i ++) {
            Edge lastEdge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(lastEdge);
            if (caller.isSource() || i == edges.size()) break;
            Edge newEdge = edges.get(edges.size() - i - 1);
            if (caller.getName().equals("<clinit>")
                    || !caller.equals(CSCallGraph.getCallee(newEdge))) break; // ignore class static initializer
            tempNewTC = getNewTCList(tempNewTC, newEdge.getCSIntContr());
            if (!ContrUtil.allControllable(tempNewTC)) break;
            edgeList.add(newEdge);
        }
        List<Edge> ret = filterEdgeList(edgeList);
        return ret;
    }

    private List<Edge> backPropagate(Edge initEdge, Stack<Edge> edges, int sinkLen) {
        List<Edge> edgeList = new ArrayList<>();
        edgeList.add(initEdge);
        int range = MAX_LEN - sinkLen - 1;
        for (int i = 0; i < range; i ++) {
            Edge lastEdge = edgeList.get(i);
            JMethod caller = CSCallGraph.getCaller(lastEdge);
            if (caller.isSource() || i == edges.size()) break;
            Edge newEdge = edges.get(edges.size() - i - 1);
            if (caller.getName().equals("<clinit>")
                    || !caller.equals(CSCallGraph.getCallee(newEdge))) break;
            edgeList.add(newEdge);
        }
        List<Edge> ret = filterEdgeList(edgeList);
        return ret;
    }

    private List<Edge> simplyGC(List<Edge> edgeList) {
        List<Edge> gcEdgeList = new ArrayList<>(edgeList);
        Collections.reverse(gcEdgeList);
        List<String> subSigList = new ArrayList<>();
        List<Edge> simplyGC = new ArrayList<>();
        String source = CSCallGraph.getCaller(gcEdgeList.get(0)).toString();
        for (int i = 0; i < gcEdgeList.size(); i++) {
            Edge edge = gcEdgeList.get(i);
            String gadget = CSCallGraph.getCaller(edge).toString();
            String subSig = getSubSignature(gadget);
            if (subSigList.contains(subSig)) {
                int from = subSigList.lastIndexOf(subSig);
                if (from != 0) {
                    int end = subSigList.size();
                    Edge fromEdge = simplyGC.get(from - 1);
                    if (fromEdge.getKind() != CallKind.STATIC) {
                        List<Integer> tcList = getTCList(gadget, edgeList);
                        if (tcList != null) {
                            List<Edge> sourceEdgeList = new ArrayList<>(simplyGC.subList(0, from));
                            Collections.reverse(sourceEdgeList);
                            Map<String, List<Integer>> tcMap = recoveryTCMap(sourceEdgeList, tcList);
                            if (tcMap.containsKey(source)) {
                                Lists.clearList(subSigList, from, end);
                                Lists.clearList(simplyGC, from - 1, end);
                                CSCallSite csCallSite = (CSCallSite) fromEdge.getCallSite();
                                CSMethod csCallee = csCallGraph.getCSMethod(gadget);
                                Edge replaceEdge = new Edge<>(fromEdge.getKind(), csCallSite, csCallee, fromEdge.getCSContr(), fromEdge.getLineNo(), fromEdge.getTypeList());
                                csCallGraph.addEdge(replaceEdge);
                                simplyGC.add(replaceEdge);
                            }
                        }
                    }
                }
            }
            subSigList.add(subSig);
            simplyGC.add(edge);
        }
        return simplyGC;
    }

    private List<Integer> getTCList(String tcKey, List<Edge> edgeList) {
        JMethod sink = CSCallGraph.getCallee(edgeList.get(0));

        List<Edge> subEdgeList = new ArrayList<>();
        for (Edge edge : edgeList) {
            if (CSCallGraph.getCallee(edge).toString().equals(tcKey)) {
                break;
            } else {
                subEdgeList.add(edge);
            }
        }

        List<Integer> sinkTC = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());
        Map<String, List<Integer>> tcMap = recoveryTCMap(subEdgeList, sinkTC);
        return tcMap.getOrDefault(tcKey, null);
    }

    private List<Integer> recoveryTCList(String tcKey, List<Edge> edgeList) {
        JMethod sink = CSCallGraph.getCallee(edgeList.get(0));

        List<Edge> subEdgeList = new ArrayList<>();
        for (Edge edge : edgeList) {
            if (CSCallGraph.getCallee(edge).toString().equals(tcKey)) {
                break;
            } else {
                subEdgeList.add(edge);
            }
        }

        List<Integer> sinkTC = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());
        Map<String, List<Integer>> tcMap = recoveryTCMap(subEdgeList, sinkTC);
        return tcMap.getOrDefault(tcKey, null);
    }

    private List<Integer> getNewTCList(List<Integer> tcList, List<Integer> csIntContr) {
        List<Integer> tempTC = new ArrayList<>();
        for (int i = 0; i < tcList.size(); i++) {
            Integer tc = tcList.get(i);
            Integer newTC = tc > ContrUtil.iPOLLUTED ? csIntContr.get(tc + 1) : ContrUtil.iPOLLUTED;
            if (!tempTC.contains(newTC)) tempTC.add(newTC);
        }
        return tempTC;
    }

    private List<Edge> filterByCaller(Edge edge, List<Edge> callers) {
        String filter = edge.getFilterByCaller();
        String value = filter.split(":")[1];
        List<Edge> empty = new ArrayList<>();
        if (filter.contains("name")) {
            if (callers.size() == 0) {
                return empty;
            } else {
                Edge caller = callers.get(0);
                String invokeTarget = ((CSCallSite) caller.getCallSite()).getCallSite().getInvokeExp().getMethodRef().getName();
                if (!invokeTarget.equals(value)) {
                    return empty;
                } else {
                    return callers;
                }
            }
        } else {
            int idx = Strings.extractParamIndex(value) + 1;
            List<Edge> ret = new ArrayList<>();
            for (int i = 0; i < callers.size(); i++) {
                Edge caller = callers.get(i);
                String edgeValue = (String) caller.getCSContr().get(idx);
                if (ContrUtil.hasCS(edgeValue) || ContrUtil.isThis(edgeValue)) {
                    String nameReg = ContrUtil.convert2Reg(edgeValue);
                    boolean hasStar = nameReg.contains("*");
                    if (nameReg.contains("[")) break;
                    Pattern pattern = Pattern.compile(nameReg);
                    String callee = CSCallGraph.getCallee(edge).getName();
                    boolean match = hasStar ? pattern.matcher(callee).find() : callee.equals(nameReg);
                    if (match) ret.addAll(callers.subList(i, callers.size()));
                    break;
                } else if (ContrUtil.isControllableParam(edgeValue)) {
                    idx = Strings.extractParamIndex(edgeValue) + 1;
                    ret.add(caller);
                } else {
                    break;
                }
            }
            return ret;
        }
    }

    private boolean typeCheck(List<Edge> edgeList) {
        List<Edge> gcEdgeList = new ArrayList<>(edgeList);
        Collections.reverse(gcEdgeList);

        List<Type> passType = null;
        for (int i = 0; i < gcEdgeList.size(); i++) {
            Edge edge = gcEdgeList.get(i);
            JMethod invokeRef = CSCallGraph.getInvokeRef(edge);
            JMethod callee = CSCallGraph.getCallee(edge);
            if (invokeRef.hasImitatedBehavior()) return true;
            if (callee.isInvoke()) return filterCast(gcEdgeList, i + 1);
            List<Type> paramsType = getParamsType(callee);
            List<Integer> edgeContr = edge.getCSIntContr();
            passType = getNewPassType(edgeContr, edge.getTypeList(), passType, paramsType);

            if (!typeSystem.hasSubRelation(paramsType, passType)) {
                return false;
            }
        }
        return true;
    }

    private boolean filterCast(List<Edge> gcEdgeList, int i) { // no cast in dynamic proxy
        List<Edge> tempEdgeList = gcEdgeList.subList(0, i);
        Collections.reverse(tempEdgeList);
        List<Integer> tc = new ArrayList<>();
        tc.add(-1);
        for (Edge tmp : tempEdgeList) {
            if (tmp.isCasted(tc.get(0) + 1)) return false;
            tc = getNewTCList(tc, tmp.getCSIntContr());
        }
        return true;
    }

    private String getSubSignature(String method) {
        String sub = method.split(":")[1];
        return sub.substring(1, sub.length() - 1);
    }

    private List<Type> getParamsType(JMethod method) {
        List<Type> ret = new ArrayList<>(method.getParamTypes());
        ret.add(0, method.getDeclaringClass().getType());
        return ret;
    }

    private Map<String, List<Integer>> recoveryTCMap(List<Edge> edgeList, List<Integer> tcList) {
        Map<String, List<Integer>> tempTCMap = new HashMap<>();
        for (Edge edge : edgeList) {
            tcList = getNewTCList(tcList, edge.getCSIntContr());
            if (!ContrUtil.allControllable(tcList)) return tempTCMap;
            JMethod sGadget = CSCallGraph.getCaller(edge);
            tempTCMap.put(sGadget.toString(), tcList);
        }
        return tempTCMap;
    }

    private List<Type> getNewPassType(List<Integer> edgeContr, List<Type> edgeType, List<Type> passType, List<Type> paramsType) {
        List<Type> ret = new ArrayList<>();
        for (int i = 0; i < edgeContr.size(); i++) {
            int c = edgeContr.get(i);
            if (c > ContrUtil.iTHIS) {
                ret.add(passType != null ? passType.get(c + 1) : edgeType.get(i));
            } else if (c == ContrUtil.iTHIS) {
                ret.add(edgeType.get(i));
            } else {
                ret.add(paramsType.get(i));
            }
        }
        return ret;
    }

    private Stack<Edge> list2Stack(List<Edge> edgeList) {
        Stack<Edge> stack = new Stack<>();
        stack.addAll(edgeList);
        Collections.reverse(stack);
        return stack;
    }

    private boolean addGC(List<Edge> gcEdgeList) {
        List<Edge> copy = new ArrayList<>(gcEdgeList);
        Collections.reverse(copy);
        List<String> gc = getGCList(copy);
        return GCs.add(gc);
    }

    private List<String> getGCList(List<Edge> edgeList) {
        ArrayList<String> gc = new ArrayList<>();
        for (int i = 0; i < edgeList.size(); i++) {
            Edge edge = edgeList.get(i);
            JMethod m = CSCallGraph.getCaller(edge);
            String key = m.toString();
            gc.add(key);
        }
        Collections.reverse(gc);
        gc.add(CSCallGraph.getCallee(edgeList.get(0)).toString());
        return gc;
    }

    private boolean startWithSource(List<Edge> gc) {
        return CSCallGraph.getCaller(gc.get(gc.size() - 1)).isSource();
    }

    private void linkGC(Edge callEdge, Set<List<Edge>> toSinkGCs, Stack<Edge> edges) {
        for (List<Edge> toSinkGC : toSinkGCs) {
            List<Edge> gcEdgeList = new ArrayList<>(toSinkGC);
            Collections.reverse(gcEdgeList);
            int gcSize = gcEdgeList.size();
            List<Integer> tcList = recoveryTCList(CSCallGraph.getCaller(gcEdgeList.get(gcSize - 1)).toString(), gcEdgeList);
            if (tcList == null) continue;

            List<Edge> sourceEdgeList = backPropagate(tcList, callEdge, edges, gcSize);
            if (sourceEdgeList.isEmpty()) continue;

            gcEdgeList.addAll(sourceEdgeList);
            List<Edge> filterGCList = filterEdgeList(gcEdgeList);
            if (filterGCList.size() <= gcSize) continue;

            if (!startWithSource(filterGCList)) {
                updateToSinkGC(filterGCList, false);
            } else {
                updateToSinkGC(filterGCList, true);
                if (!typeCheck(filterGCList)) return;
                List<Edge> simplyGC = simplyGC(filterGCList);
                if (addGC(simplyGC)) {
                    logAndWrite(simplyGC);
                }
            }
        }
    }

    /**
     * add gadget node to gcGraph
     */
    private boolean updateToSinkGC(List<Edge> gc, boolean startWithSource) {
        List<Edge> edgeList = new ArrayList<>(gc);
        Collections.reverse(edgeList);
        if (edgeList.size() >= MAX_LEN || (startWithSource && edgeList.size() > 1)) {
            edgeList = edgeList.subList(1, edgeList.size());
        }
        return gcGraph.addPath(edgeList);
    }

    private List<Edge> filterEdgeList(List<Edge> edgeList) {
        List<Edge> ret = new ArrayList<>();
        for (int i = 0; i < edgeList.size(); i++) {
            Edge edge = edgeList.get(i);
            ret.add(edge);
            if (edge.needFilterByCaller()) {
                List<Edge> callers = edgeList.subList(i + 1, edgeList.size());
                List<Edge> temp = filterByCaller(edge, callers);
                if (temp.size() < callers.size()) {
                    ret.addAll(temp);
                    break;
                }
            }
        }
        return ret;
    }

    private void logAndWrite(List<Edge> gcEdgeList){
        try {
            int gcSize = gcEdgeList.size();
            for (int i = 0; i < gcSize; i++) {
                Edge edge = gcEdgeList.get(i);
                String caller = CSCallGraph.getCaller(edge).toString();
                StringBuilder line = new StringBuilder(caller);
                line.append("->").append(edge.getCSIntContr());
                String writeLine = line.toString();
                logger.info(writeLine);
                pw.println(writeLine);
            }
            String sink = CSCallGraph.getCallee(gcEdgeList.get(gcSize - 1)).toString();
            logger.info(sink);
            pw.println(sink);
            logger.info("");
            pw.println("");
            pw.flush();
        } catch (Exception e) {
            logger.info(e);
        }
    }

    public void finish() {
        logger.info("total gadget chains : {}", GCs.size());
        pw.println("total gadget chains : " + GCs.size());
        pw.flush();
    }
}
