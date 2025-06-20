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
 * collect gadget chains after analyze
 */

public class GCCollectorAfterProcess implements Plugin {

    private static final Logger logger = LogManager.getLogger(GCCollectorAfterProcess.class);

    private CSCallGraph csCallGraph;

    private TypeSystem typeSystem;

    private String output;

    public static final int MAX_LEN = World.get().getOptions().getGC_MAX_LEN();

    public int SINK_MAX_TIME;

    private Set<List<String>> GCs;

    private PrintWriter pw;

    private Map<String, Set<List<String>>> dedupMap;

    private static double LCS_Threshold = World.get().getOptions().getLCS_THRESHOLD();

    public GCCollectorAfterProcess(CSCallGraph csCallGraph, String db_path) {
        super();
        this.csCallGraph = csCallGraph;
        this.typeSystem = World.get().getTypeSystem();
        this.output = db_path;
        this.GCs = new HashSet<>();
        this.dedupMap = new HashMap<>();
        try {
            File output_file = new File(World.get().getOptions().getOutputDir(), this.output);
            this.pw = new PrintWriter(new BufferedWriter(new FileWriter(output_file)));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void onFinish() {
        Set<JMethod> sinks = World.get().getSinks();
        for (JMethod sink : sinks) {
            logger.info("backward from {}", sink.toString());
            getGCs(sink);
        }
        logger.info("total gadget chains : {}", GCs.size());
        pw.println("total gadget chains : " +  GCs.size());
        pw.flush();
    }

    private void getGCs(JMethod sink) {
        List<Edge> current = new ArrayList<>();
        List<Integer> sinkTC = Arrays.stream(sink.getSink()).boxed().collect(Collectors.toList());

        Set<Edge<CSCallSite, CSMethod>> edges = new HashSet<>(csCallGraph.edgesInTo(sink));
        int c = 0;
        for (Edge<CSCallSite, CSMethod> edge : edges) {
            List<Integer> newTCList = getNewTCList(sinkTC, edge.getCSIntContr());
            if (!ContrUtil.allControllable(newTCList)) continue;
            c += 1;
        }
        if (c == 0) return;
        for (Edge<CSCallSite, CSMethod> edge : edges) {
            SINK_MAX_TIME = (World.get().getOptions().getSINK_MAX_TIME() * 1000) / c; // avoid searching from just one path
            long startTime = System.currentTimeMillis();
            backDFS(sink, edge, current, new HashSet<>(), sinkTC, startTime);
        }
    }

    /**
     * search gadget chains in DFS and filter by controllability (Tabby)
     */
    private void backDFS(JMethod callee, Edge curEdge, List<Edge> curGC, Set<JMethod> visited, List<Integer> TCList, Long startTime) {
        if (!visited.add(callee) || System.currentTimeMillis() - startTime > SINK_MAX_TIME) return;
        List<Integer> newTCList = getNewTCList(TCList, curEdge.getCSIntContr());
        if (!ContrUtil.allControllable(newTCList)) {
            visited.remove(callee);
            return;
        }
        JMethod caller = CSCallGraph.getCaller(curEdge);
        curGC.add(curEdge);
        if (caller.isSource()) {
            List<Edge> gc = new ArrayList<>(curGC);
            if (!filterEdge(gc) && typeCheck(gc)) {
                List<Edge> simplyGC = simplyGC(gc);
                List<String> gcStr = getGCString(simplyGC);
                if (dedup(gcStr) && GCs.add(gcStr)) {
                    logAndWrite(simplyGC);
                }
            }
        } else if (curGC.size() == MAX_LEN) {
            visited.remove(callee);
            curGC.remove(curGC.size() - 1);
            return;
        } else {
            Set<Edge<CSCallSite, CSMethod>> edges = new HashSet<>(csCallGraph.edgesInTo(caller));
            for (Edge<CSCallSite, CSMethod> edge : edges) {
                backDFS(caller, edge, curGC, visited, newTCList, startTime);
            }
        }
        visited.remove(callee);
        curGC.remove(curGC.size() - 1);
    }

    /**
     * in a source-sink pair, using LCS and subSignature to du-dup gadget chains
     */
    private boolean dedup(List<String> gcStr) {
        String key = gcStr.get(0) + "#" + gcStr.get(gcStr.size() - 1);
        List<String> value = getSubSignature(gcStr);

        dedupMap.putIfAbsent(key, new HashSet<>());

        for (List<String> sub : dedupMap.get(key)) {
            if (computeLCS(sub, value) >= LCS_Threshold) {
                return false;
            }
        }

        dedupMap.get(key).add(value);
        return true;
    }

    public static int computeLCSLength(List<String> list1, List<String> list2) {
        int m = list1.size();
        int n = list2.size();
        int[][] dp = new int[m + 1][n + 1];

        for (int i = 1; i <= m; i++) {
            String s1 = list1.get(i - 1);
            for (int j = 1; j <= n; j++) {
                String s2 = list2.get(j - 1);
                if (s1.equals(s2)) {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
                }
            }
        }

        return dp[m][n];
    }

    /**
     * similarity of two gadget chains
     */
    public static double computeLCS(List<String> list1, List<String> list2) {
        if (list1.isEmpty() || list2.isEmpty()) return 0.0;
        int lcsLength = computeLCSLength(list1, list2);
        return (2.0 * lcsLength) / (list1.size() + list2.size());
    }

    private List<String> getSubSignature(List<String> gcStr) {
        List<String> subSigList = new ArrayList<>();
        for (String gc : gcStr) {
            subSigList.add(getSubSignature(gc));
        }
        return subSigList;
    }

    private List<String> getGCString(List<Edge> gcEdgeList) {
        List<String> gc = new ArrayList<>();
        for (int i = 0; i < gcEdgeList.size(); i++) {
            Edge edge = gcEdgeList.get(i);
            String caller = CSCallGraph.getCaller(edge).toString();
            gc.add(caller);
        }
        String sink = CSCallGraph.getCallee(gcEdgeList.get(gcEdgeList.size() - 1)).toString();
        gc.add(sink);
        return gc;
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

    private boolean filterEdge(List<Edge> edgeList) {
        for (int i = 0; i < edgeList.size(); i++) {
            Edge edge = edgeList.get(i);
            if (edge.needFilterByCaller()) {
                List<Edge> callers = edgeList.subList(i + 1, edgeList.size());
                return filterByCaller(edge, callers);
            }
        }
        return false;
    }

    /**
     * simply intermediate gadget
     */
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

    private List<Integer> getNewTCList(List<Integer> tcList, List<Integer> csIntContr) {
        List<Integer> tempTC = new ArrayList<>();
        for (int i = 0; i < tcList.size(); i++) {
            Integer tc = tcList.get(i);
            Integer newTC = tc > ContrUtil.iPOLLUTED ? csIntContr.get(tc + 1) : ContrUtil.iPOLLUTED;
            if (!tempTC.contains(newTC)) tempTC.add(newTC);
        }
        return tempTC;
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

    /**
     * filter edge containing reflection or invoke
     */
    private boolean filterByCaller(Edge edge, List<Edge> callers) {
        String filter = edge.getFilterByCaller();
        String value = filter.split(":")[1];
        if (filter.contains("name")) {
            if (callers.size() == 0) {
                return true;
            } else {
                String name = value.split("#")[0];
                int idx = Strings.extractParamIndex(value.split("#")[1]) + 1;
                for (int i = 0; i < callers.size(); i++) {
                    Edge caller = callers.get(i);
                    String edgeValue = (String) caller.getCSContr().get(idx);
                    if (ContrUtil.isControllableParam(edgeValue)) {
                        idx = Strings.extractParamIndex(edgeValue) + 1;
                    } else if (ContrUtil.isControllable(edgeValue)) {
                        return false;
                    } else if (!ContrUtil.isControllable(edgeValue)) {
                        String invokeTarget = ((CSCallSite) caller.getCallSite()).getCallSite().getInvokeExp().getMethodRef().getName();
                        return !invokeTarget.equals(name);
                    }
                }
            }
        } else {
            int idx = Strings.extractParamIndex(value) + 1;
            for (int i = 0; i < callers.size(); i++) {
                Edge caller = callers.get(i);
                String edgeValue = (String) caller.getCSContr().get(idx);
                if (ContrUtil.hasCS(edgeValue) || ContrUtil.isThis(edgeValue)) {
                    String nameReg = ContrUtil.convert2Reg(edgeValue);
                    boolean hasStar = nameReg.contains("*");
                    Pattern pattern;
                    try {
                        pattern = Pattern.compile(nameReg);
                    } catch (Exception e) {
                        return true;
                    }
                    String callee = CSCallGraph.getCallee(edge).getName();
                    boolean match = hasStar ? pattern.matcher(callee).find() : callee.equals(nameReg);
                    if (!match) return true;
                    break;
                } else if (ContrUtil.isControllableParam(edgeValue)) {
                    idx = Strings.extractParamIndex(edgeValue) + 1;
                } else {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * filter gc by type
     */
    private boolean typeCheck(List<Edge> edgeList) {
        List<Edge> gcEdgeList = new ArrayList<>(edgeList);
        Collections.reverse(gcEdgeList);

        List<Type> passType = null;
        for (int i = 0; i < gcEdgeList.size(); i++) {
            Edge edge = gcEdgeList.get(i);

            JMethod callee = CSCallGraph.getCallee(edge);
            JMethod invokeRef = CSCallGraph.getInvokeRef(edge);
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
}
