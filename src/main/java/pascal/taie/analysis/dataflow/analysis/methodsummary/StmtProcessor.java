package pascal.taie.analysis.dataflow.analysis.methodsummary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.AnalysisManager;
import pascal.taie.analysis.dataflow.analysis.ContrAlloc;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.CompositePlugin;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.TaintTransfer;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.TaintTransferEdge;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.ConstantObj;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.*;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.*;
import pascal.taie.util.InvokeUtils;
import pascal.taie.util.Strings;
import pascal.taie.util.collection.Sets;

import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;

import static pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.PUtil.getPointerMethod;

/**
 * core logic of our analysis
 */

public class StmtProcessor {

    /**
     * the results fo demand-driven analysis
     */
    private ContrFact drivenMap;

    private Visitor visitor;

    private CSCallGraph csCallGraph;

    private PointerFlowGraph pointerFlowGraph;

    private HeapModel heapModel;

    private CSManager csManager;

    private StackManger stackManger;

    private Context context; // empty context for now

    private TypeSystem typeSystem;

    private int lineNumber;

    private CSVar thisVar;

    private JMethod curMethod;

    private static final Logger logger = LogManager.getLogger(StmtProcessor.class);

    private boolean isFilterNonSerializable =  World.get().getOptions().isFilterNonSerializable();

    private CompositePlugin plugin;

    private boolean mayCreateRoute;

    private static Set<String> proxySkipClasses = Set.of(
            "java.io.ObjectInput",
            "java.util.Map$Entry",
            "java.util.Iterator"
    );

    private static Set<String> primitiveClasses = Set.of(
            "java.lang.Long",
            "java.lang.Integer",
            "java.lang.Float",
            "java.lang.Double",
            "java.lang.Byte",
            "java.lang.Short",
            "java.lang.Boolean"
    );

    public StmtProcessor(StackManger stackManger, CSCallGraph callGraph, PointerFlowGraph pointerFlowGraph, HeapModel heapModel, CSManager csManager, Context context, CompositePlugin plugin) {
        this.drivenMap = new ContrFact();
        this.visitor = new Visitor();
        this.stackManger = stackManger;
        this.csCallGraph = callGraph;
        this.pointerFlowGraph = pointerFlowGraph;
        this.heapModel = heapModel;
        this.csManager = csManager;
        this.context = context;
        this.typeSystem = World.get().getTypeSystem();
        this.curMethod = stackManger.curMethod();
        this.plugin = plugin;
        this.lineNumber = -1;
        this.mayCreateRoute = false;
    }

    public void setThis(CSVar thisVar) {
        this.thisVar = thisVar;
    }

    public void setFact(ContrFact fact) {
        this.drivenMap = fact;
    }

    public ContrFact getFact() {
        return this.drivenMap;
    }

    private Contr getOrAddContr(Pointer p) {
        if (!containsContr(p)) {
            Contr ret = Contr.newInstance(p);
            return ret;
        } else {
            return drivenMap.get(p);
        }
    }

    private boolean containsContr(Pointer p) {
        return drivenMap.contains(p);
    }

    private void updateContr(Pointer k, Contr v) {
        if (k!= null && v != null && curMethod.equals(getPointerMethod(k))) {
            drivenMap.update(k, v);
        }
    }

    public void addPFGEdge(CSObj from, Pointer to, FlowKind kind, int lineNumber) {
        if (from != null && to != null) {
            addPFGEdge(new PointerFlowEdge(kind, from, to), Identity.get(), lineNumber);
        }
    }

    public void addPFGEdge(Pointer from, Pointer to, FlowKind kind, int lineNumber) {
        if (from != null && to != null) {
            addPFGEdge(new PointerFlowEdge(kind, from, to), Identity.get(), lineNumber);
        }
    }

    public void addPFGEdge(PointerFlowEdge edge, Transfer transfer, int lineNumber) {
        edge.addTransfer(transfer);
        edge.setLineNumber(lineNumber);
        if (pointerFlowGraph.addEdge(edge) != null) varsToReQuery(edge.target(), new HashSet<>());
    }

    /**
     * remove the cached results in drivenMap, as they need to requery
     */
    private void varsToReQuery(Pointer p, HashSet<Pointer> visited) {
        if (Objects.equals(getPointerMethod(p), curMethod) && visited.add(p)) {
            if (containsContr(p)) {
                drivenMap.remove(p);
                p.setReQuery(true);
            }
            for (PointerFlowEdge outEdge : p.getOutEdges()) {
                varsToReQuery(outEdge.target(), visited);
            }
        }
    }

    public void process(Stmt stmt) {
        this.lineNumber = stmt.getLineNumber();
        stmt.accept(visitor);
        if (stackManger.isInIf() && stackManger.isIfEnd(stmt)) stackManger.popIf();
        if (stackManger.containsInstanceOfEnd(stmt)) stackManger.removeInstanceOfEnd(stmt);
    }

    private class Visitor implements StmtVisitor<Void> {

        public Visitor() {
        }

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            CSObj from = csManager.getCSObj(context, obj);
            CSVar to = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(from, to, FlowKind.NEW, lineNumber);
            return null;
        }

        @Override
        public Void visit(AssignLiteral stmt) {
            Literal literal = stmt.getRValue();
            Type type = literal.getType();
            CSVar to = csManager.getCSVar(context, stmt.getLValue());
            to.setAssigned();
            if (type instanceof ClassType) {
                // here we only generate objects of ClassType
                Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
                addPFGEdge(csManager.getCSObj(context, obj), to, FlowKind.NEW, lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var rvalue = stmt.getRValue();
            if (!isIgnored(rvalue.getType())) {
                CSVar from = csManager.getCSVar(context, rvalue);
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(from, to, FlowKind.LOCAL_ASSIGN, lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(Cast stmt) {
            CastExp cast = stmt.getRValue();
            if (!isIgnored(cast.getCastType())) {
                CSVar from = csManager.getCSVar(context, cast.getValue());
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(new PointerFlowEdge(FlowKind.CAST, from, to), new SpecialType(cast.getCastType()), lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            Var lValue = stmt.getLValue();
            if (!isIgnored(lValue.getType())) {
                JField field = stmt.getFieldRef().resolve();
                if (field == null) return null;
                CSVar to = csManager.getCSVar(context, stmt.getLValue());
                if (stmt.isStatic()) {
                    // first analyze a class's static initializer
                    JMethod clinit = field.getDeclaringClass().getClinit();
                    if (clinit != null && !stackManger.containsMethod(clinit)) AnalysisManager.runMethodAnalysis(clinit);
                    StaticField sfield = csManager.getStaticField(field);
                    addPFGEdge(sfield, to, FlowKind.STATIC_LOAD, lineNumber);
                } else {
                    CSVar base = csManager.getCSVar(context, ((InstanceFieldAccess) stmt.getFieldAccess()).getBase());
                    InstanceField iField = csManager.getInstanceField(base, field);
                    addPFGEdge(iField, to, FlowKind.INSTANCE_LOAD, lineNumber);
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            Var rValue = stmt.getRValue();
            if (!isIgnored(rValue.getType())) {
                JField field = stmt.getFieldRef().resolve();
                if (field == null) return null;
                CSVar from = csManager.getCSVar(context, rValue);
                if (stmt.isStatic()) {
                    StaticField sfield = csManager.getStaticField(field);
                    addPFGEdge(from, sfield, FlowKind.STATIC_STORE, lineNumber);
                } else {
                    CSVar base = csManager.getCSVar(context, ((InstanceFieldAccess) stmt.getFieldAccess()).getBase());
                    InstanceField iField = csManager.getInstanceField(base, field);
                    PointerFlowEdge edge = new PointerFlowEdge(FlowKind.INSTANCE_STORE, from, iField);
                    addPFGEdge(edge, Identity.get(), lineNumber);
                    boolean isSameIfMethod = Objects.equals(curMethod, stackManger.getCurIfMethod());
                    int ifStart = isSameIfMethod ? stackManger.getIfStart() : -1;
                    int ifEnd = isSameIfMethod ? stackManger.getIfEnd() : -1;
                    pointerFlowGraph.addIfRange(edge, ifStart, ifEnd, curMethod);
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            Var lValue = stmt.getLValue();
            if (!isIgnored(lValue.getType())) {
                CSVar to = csManager.getCSVar(context, lValue);
                CSVar base = csManager.getCSVar(context, stmt.getArrayAccess().getBase());
                ArrayIndex varArray = csManager.getArrayIndex(base);
                addPFGEdge(varArray, to, FlowKind.INSTANCE_LOAD, lineNumber);
            }
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            Var rValue = stmt.getRValue();
            if (!isIgnored(rValue.getType())) {
                CSVar from = csManager.getCSVar(context, rValue);
                CSVar base = csManager.getCSVar(context, stmt.getArrayAccess().getBase());
                ArrayIndex varArray = csManager.getArrayIndex(base);
                addPFGEdge(from, varArray, FlowKind.INSTANCE_STORE, lineNumber);
                if (getContr(base) != null) {
                    Pointer to = drivenMap.get(base).getOrigin();
                    addPFGEdge(from, to, FlowKind.ELEMENT_STORE, lineNumber);
                }
            }
            return null;
        }

        @Override
        public Void visit(If stmt) {
            CSVar ifVar = csManager.getCSVar(context, stmt.getCondition().getOperand1()); // TODO consider ifVar as the left operand for now
            Contr ifContr = getContr(ifVar);
            if (ContrUtil.isControllable(ifContr) || curMethod.getInvokeDispatch(ifVar) != null) {
                stackManger.pushIf(stmt, curMethod);
            } else if (stackManger.containsInstanceOfRet(ifVar)) {
                Pointer p = stackManger.removeInstanceOfRet(ifVar);
                Var cmpVar = stmt.getCondition().getOperand2();
                if (cmpVar.isConst() && cmpVar.getConstValue() instanceof IntLiteral i && i.getValue() == 0) {
                    stackManger.putInstanceOfEnd(stmt.getTarget(), p);
                }
            }
            return null;
        }

        @Override
        public Void visit(InstanceOf stmt) {
            InstanceOfExp exp = stmt.getRValue();
            CSVar checkedVar = csManager.getCSVar(context, exp.getValue());
            Contr checkedContr = getContr(checkedVar);
            ReferenceType checkedType = exp.getCheckedType();
            if (ContrUtil.isControllable(checkedContr) && !isIgnored(checkedType)) {
                CSVar retVar = csManager.getCSVar(context, stmt.getLValue());
                stackManger.putInstanceOfInfo(retVar, checkedVar, checkedType);
            }
            return null;
        }

        @Override
        public Void visit(Return stmt) {
            Var ret = stmt.getValue();
            if (ret == null || isIgnored(ret.getType())) {
                String oldV = curMethod.getSummary("return");
                if (oldV == null) curMethod.setSummary("return", "null+null");
            } else {
                String oldV = curMethod.getSummary("return");
                CSVar retVar = csManager.getCSVar(context, ret);
                String newV = getContrValue(retVar);
                newV = newV + "+" + (containsContr(retVar) ? drivenMap.get(retVar).getType() : "null");
                if (ContrUtil.needUpdateInMerge(oldV, newV)) {
                    curMethod.setSummary("return", newV);
                }
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            InvokeExp invokeExp = stmt.getInvokeExp();
            if (stmt.isDynamic()) return null;
            JMethod ref = invokeExp.getMethodRef().resolve();
            if (isIgnored(ref)) return null;
            List<CSVar> callSiteVars = getCallsiteVars(invokeExp);
            CSVar base = callSiteVars.get(0);
            List<Contr> csContr = getCallSiteContr(callSiteVars);
            List<String> csContrValue = getCallSiteContrValue(csContr);
            if (isIgnoredCallSite(csContrValue, ref, stmt.getContainer().getDeclaringClass().getType())) return null;
            Set<JMethod> callees = new HashSet<>();
            if (stmt.isInterface()) processProxy(stmt, csContr, csContrValue);
            if (ref.isTransfer()) {
                processTransfer(ref, stmt);
                return null;
            }
            processReceiver(ref, base, csContrValue);
            if (ref.hasImitatedBehavior()) {
                processBehavior(ref, stmt, callSiteVars, csContr, csContrValue);
                return null;
            }
            if (ref.isSink()) {
                if (!filterSink(ref, base)) return null;
                addWL(stmt, ref, csContr, csContrValue);
                return null;
            }
            callees.addAll(getCallees(stmt, csContr, ref.getDeclaringClass().getType()));
            for (JMethod callee : callees) {
                if (!isThis(base)) plugin.onNewDeser(callee);
                addWL(stmt, callee, csContr, csContrValue);
            }
            sideEffects(stmt, callees, callSiteVars, base, csContrValue);
            return null;
        }
    }

    /**
     * can be ignored during deserialization analysis
     */
    private boolean isIgnoredCallSite(List<String> csContr, JMethod ref, Type containerType) {
        if (!ref.isConstructor() && ref.getParamTypes().stream().anyMatch(p -> p.getName().equals("java.lang.String"))) return false; // 字符串操作
        else if (ref.getName().equals("equals") && !ref.getDeclaringClass().getName().equals("java.lang.String") && !ContrUtil.isControllable(csContr.get(1))) return true;
        else if (typeSystem.isSubtype(typeSystem.getType("java.io.ObjectInputStream"), containerType)
                && csContr.get(0).startsWith(ContrUtil.sTHIS)) return true;
        else return csContr.stream().allMatch(s -> !ContrUtil.isControllable(s));
    }

    /**
     * pollute the receiver when handle <init>
     */
    private void processReceiver(JMethod ref, CSVar base, List<String> csContr) {
        Contr baseContr = drivenMap.get(base);
        if (baseContr == null || ContrUtil.isControllable(baseContr)) return;
        if (ref.isConstructor()) {
            for (int i = 1; i < csContr.size(); i++) {
                String contr = csContr.get(i);
                if (ContrUtil.isControllable(contr)) {
                    baseContr.setValue(contr);
                    break;
                }
            }
        }
    }

    /**
     * apply the summary to the callsite
     */
    private void sideEffects(Invoke stmt, Set<JMethod> callees, List<CSVar> callSiteVars, CSVar base, List<String> csContrValue) { // 处理返回值以及对参数的影响
        Var ret = stmt.getResult();
        CSVar csRet = null;
        Contr retContr = null;
        if (ret != null && !isIgnored(ret.getType())) {
            csRet = csManager.getCSVar(context, ret);
            retContr = getOrAddContr(csRet);
        }
        String actionType = "assign";
        for (JMethod callee : callees) {
            if (isIgnored(callee)) continue;
            if (stackManger.containsMethod(callee)) { // ignore recursive
                if (retContr != null) {
                    for (String contr : csContrValue) {
                        if (ContrUtil.isControllable(contr)) {
                            retContr.updateValue(contr, actionType);
                            break;
                        }
                    }
                    updateContr(csRet, retContr);
                }
                continue;
            }
            Map<String, String> summary = callee.getSummaryMap();
            for (String sKey : summary.keySet()) {
                String sValue = summary.get(sKey);
                if (sValue.contains(":")) {
                    actionType = sValue.substring(0, sValue.indexOf(":"));
                    sValue = sValue.substring(sValue.indexOf(":") + 1, sValue.length());
                }
                if (sKey.equals("return")) { // return
                    if (retContr == null || !ContrUtil.needUpdateInMerge(retContr.getValue(), sValue)) continue;
                    String retValue = sValue.substring(0, sValue.lastIndexOf("+"));
                    String retType = sValue.substring(sValue.lastIndexOf("+") + 1);
                    if (!retType.equals("null")) retContr.setType(typeSystem.getType(retType));
                    if (ContrUtil.isCallSite(retValue)) {
                        Contr fromContr = getCallSiteCorrespondContr(retValue, callSiteVars, base);
                        retContr.updateValue(fromContr, actionType);
                        csRet.setAssigned();
                        if (fromContr.getOrigin() instanceof ArrayIndex a) { // templatesImpl
                            addPFGEdge(a.getArrayVar(), retContr.getOrigin(), FlowKind.SUMMARY_ASSIGN, lineNumber);
                        } else if (fromContr.getOrigin() instanceof InstanceField i) {
                            addPFGEdge(i.getBaseVar(), retContr.getOrigin(), FlowKind.SUMMARY_ASSIGN, lineNumber);
                        }
                    } else {
                        retContr.updateValue(retValue, actionType);
                    }
                    updateContr(csRet, retContr);
                } else if (ContrUtil.isCallSite(sKey)) {
                    Contr toContr = getCallSiteCorrespondContr(sKey, callSiteVars, base);
                    if (toContr == null || Objects.equals(toContr.getName(), "%nullconst")) continue;
                    String target = toContr.getValue();
                    if (ContrUtil.isCallSite(sValue)) {
                        Contr fromContr = getCallSiteCorrespondContr(sValue, callSiteVars, base);
                        toContr.updateValue(fromContr, actionType);
                        polluteBase(toContr);
                        if (ContrUtil.isCallSite(target) && !toContr.isIntra()) {
                            if (useFiled(thisVar, target)) addPFGEdge(fromContr.getOrigin(), toContr.getOrigin(), FlowKind.SUMMARY_ASSIGN, lineNumber);
                            else if (fromContr != null) {
                                String target_summary = actionType.equals("append") && curMethod.getName().equals("append") ? "append:" + fromContr.getValue() : fromContr.getValue(); // Click TODO improve this
                                curMethod.setSummary(target, target_summary);
                            }
                        }
                    } else {
                        toContr.updateValue(sValue, actionType);
                        if (ContrUtil.isCallSite(target) && !toContr.isIntra()) curMethod.setSummary(target, sValue);
                    }
                    updateContr(toContr.getOrigin(), toContr);
                }
            }
        }
    }

    private void addWL(Invoke stmt, JMethod callee, List<Contr> edgeContr, List<String> edgeContrValue) {
        if (!isIgnored(callee) && (callee.isSink() || (!callee.isTransfer() && !callee.hasImitatedBehavior()))) {
            List<Type> edgeType = getCallSiteType(edgeContr);
            Edge callEdge = getCallEdge(stmt, callee, edgeContrValue, edgeType);
            filterByCaller(stmt, callEdge, edgeContrValue);
            setEdgeCasted(callEdge, edgeContr);
            boolean inStack = stackManger.containsMethod(callee);
            if (csCallGraph.addEdge(callEdge)) stackManger.pushCallEdge(callEdge, inStack);
            if (!inStack) AnalysisManager.runMethodAnalysis(callee);
        }
    }

    private void setEdgeCasted(Edge callEdge, List<Contr> callSiteContr) {
        for (int i = 0; i < callSiteContr.size(); i++) {
            Contr contr = callSiteContr.get(i);
            if (contr != null && contr.isCasted()) callEdge.setCasted(i);
        }
    }

    private boolean filterSink(JMethod ref, CSVar base) { // reduce FP
        if (ref.toString().equals("<java.lang.Class: java.lang.Object newInstance()>")) {
            Contr contr = getContr(base);
            if (contr != null && contr.getOrigin() instanceof InstanceField iField
                    && iField.getField().getGSignature() != null) {
                String gSignature = iField.getField().getGSignature().toString();
                if (gSignature.contains("extends")) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean isTransient(Contr ret) {
        if (ret.getOrigin() instanceof InstanceField iField) {
            return Modifier.hasTransient(iField.getField().getModifiers()) && !stackManger.isRestoredField(iField.getField());
        } else {
            return ret.isTransient();
        }
    }

    private boolean isIgnored(Type type) {
        return (type instanceof PrimitiveType && !(type instanceof CharType)) || type instanceof NullType || (type instanceof ClassType ct && primitiveClasses.contains(ct.getName()));
    }

    private boolean isIgnored(JMethod method) {
        return method == null || method.isIgnored() || method.getDeclaringClass().isMethodIgnored();
    }

    private boolean isThis(Pointer pointer) {
        if (pointer instanceof CSVar var) {
            return var.getVar().getName().equals("%this");
        } else {
            return false;
        }
    }

    private List<Contr> getCallSiteContr(List<CSVar> callSiteVars) {
        List<Contr> contrList = new ArrayList<>();
        callSiteVars.forEach(var -> contrList.add(getContr(var)));
        return contrList;
    }

    private List<String> getCallSiteContrValue(List<Contr> callSiteContrs) {
        List<String> list = new ArrayList<>();
        callSiteContrs.forEach(contr -> list.add(getContrValue(contr)));
        return list;
    }

    private List<Type> getCallSiteType(List<Contr> csContr) {
        List<Type> ret = new ArrayList<>();
        csContr.forEach(contr-> ret.add(contr != null ? contr.getType() : null));
        return ret;
    }

    private List<CSVar> getCallsiteVars(InvokeExp invokeExp) {
        List<CSVar> vars = new ArrayList<>();
        invokeExp.getArgs().stream()
                .map(arg -> csManager.getCSVar(context, arg))
                .forEach(arg -> vars.add(arg));
        CSVar base = null;
        if (invokeExp instanceof InvokeInstanceExp instanceExp) {
            base = csManager.getCSVar(context, instanceExp.getBase());
        }
        vars.add(0, base);
        return vars;
    }

    private String getContrValue(Pointer p) {
        Contr contr = getContr(p);
        return getContrValue(contr);
    }

    private String getContrValue(Contr c) {
        return c != null ? c.getValue() : ContrUtil.sNOT_POLLUTED;
    }

    /**
     * get the contr fact of a pointer
     */
    private Contr getContr(Pointer p) {
        if (p != null && !isIgnored(p.getType())) {
            if (containsContr(p) && !p.isReQuery()) {
                Contr query = drivenMap.get(p);
                if (stackManger.containsInstanceOfType(p)) {
                    Contr checkedContr = query.copy();
                    checkedContr.setType(stackManger.getInstanceofType(p));
                    return checkedContr;
                }
                checkParamIdx(query);
                return query;
            } else if (p instanceof CSVar var && getConstString(var.getVar()) != null) { // handle constant string
                Contr cs = getOrAddContr(p);
                cs.setConstString(getConstString(var.getVar()));
                updateContr(p, cs);
                return cs;
            } else {
                Contr query = findPointsTo(p).getMergedContr();
                checkParamIdx(query);
                updateContr(p, query);
                if (p.isReQuery()) p.setReQuery(false);
                if (p instanceof InstanceField field
                        && Modifier.hasTransient(field.getField().getModifiers())
                        && ContrUtil.isControllable(query) && isUnderSource()) {
                    stackManger.addRestoredField(field.getField());
                }
                if (query != null && stackManger.containsInstanceOfType(p)) {
                    Contr checkedContr = query.copy();
                    checkedContr.setType(stackManger.getInstanceofType(p));
                    return checkedContr;
                }
                return query;
            }
        }
        return null;
    }

    private boolean isUnderSource() {
        return curMethod.isSource() || (stackManger.mSize() > 1 && stackManger.getMethod(2).isSource());
    }

    private void checkParamIdx(Contr query) { // TODO to refine
        if (ContrUtil.isControllableParam(query)) {
            int idx = Strings.extractParamIndex(query.getValue());
            if (idx >= curMethod.getParamCount()) {
                query.setValue(query.getValue().replace(ContrUtil.sParam + "-" + idx, ContrUtil.sTHIS));
            }
        }
    }

    private Type getContrType(Contr contr) {
        if (contr.getType() instanceof ArrayType at) {
            if (contr.getArrayElements().size() != 0) {
                Type max = null;
                for (Contr e : contr.getArrayElements()) {
                    if (max == null || typeSystem.isSubtype(max, e.getType())) max = e.getType();
                }
                return max;
            } else {
                return at.elementType();
            }
        } else {
            return contr.getType();
        }
    }

    private String getConstString(Var var) {
        if (var.isConst() && var.getConstValue() instanceof StringLiteral s) {
            return s.getString();
        } else {
            return null;
        }
    }

    private Edge getCallEdge(Invoke callSite, JMethod callee, List<String> csContr, List<Type> edgeType) {
        CSCallSite csCallSite = csManager.getCSCallSite(context, callSite);
        CSMethod csCallee = csManager.getCSMethod(context, callee);
        return new Edge<>(CallGraphs.getCallKind(callSite), csCallSite, csCallee, csContr, lineNumber, edgeType);
    }

    /**
     * based on receiver to use pointer analysis or cha
     */
    private Set<JMethod> getCallees(Invoke stmt, List<Contr> csContr, Type refType) {
        Set<JMethod> ret = new HashSet<>();
        Contr baseContr = csContr.get(0);
        if (baseContr == null || isThis(baseContr.getOrigin())) {
            ret.addAll(CallGraphs.resolveCalleesOf(stmt));
        } else {
            if (baseContr.isNew()) { // pointer analysis
                baseContr.getNewType().forEach(type -> ret.add(CallGraphs.resolveCallee(type, stmt)));
            } else { // CHA
                Set<JMethod> chaTargets = CallGraphs.resolveCalleesOf(stmt);
                ret.addAll(filterCHA(chaTargets, baseContr, refType));
            }
        }
        Set<JMethod> callees = new HashSet<>(ret.stream()
                .filter(Objects::nonNull)
                .collect(Collectors.toSet()));

        return callees;
    }

    private Contr getCallSiteCorrespondContr(String value, List<CSVar> callSiteVars, CSVar base) {
        if (!value.contains("+")) {
            return getCallSiteCorrespondSingleContr(value, callSiteVars, base);
        } else {
            String[] singles = value.split("\\+");
            List<Contr> contrs = new ArrayList<>();
            StringBuilder replaceValue = new StringBuilder();
            for (int i = 0; i < singles.length; i++) {
                String single = singles[i];
                if (ContrUtil.hasCS(single) || single.equals(ContrUtil.sNOT_POLLUTED)) {
                    replaceValue.append(single);
                } else {
                    Contr contr = getCallSiteCorrespondSingleContr(single, callSiteVars, base);
                    if (i != 0 && contr.getValue().startsWith(replaceValue.toString())) {
                        replaceValue.append(contr.getValue().replace(replaceValue.toString(), ""));
                    } else {
                        replaceValue.append(contr.getValue());
                    }
                    contrs.add(contr);
                }
                if (i != singles.length - 1) replaceValue.append("+");
            }
            Contr contr = contrs.get(0); // TODO improve this
            contr.setValue(replaceValue.toString());
            return contr;
        }
    }

    private Contr getCallSiteCorrespondSingleContr(String value, List<CSVar> callSiteVars, CSVar base) {
        Pointer origin;
        String contrValue = ContrUtil.sNOT_POLLUTED;
        boolean isIntra = false;
        if (value.contains(ContrUtil.sTHIS)) {
            if (base != null) {
                if (value.contains("-") && !value.endsWith("-this$0")) { // this.f = xxx
                    String fieldName = Strings.extractFieldName(value);
                    origin = getCorrespondFieldVar(base, fieldName);
                    Contr baseContr = getContr(base);
                    if (baseContr != null && baseContr.isNew()) isIntra = true;
                    String baseValue = getContrValue(baseContr);
                    contrValue = baseValue.endsWith(ContrUtil.sNOT_POLLUTED) ? baseValue : baseValue + "-" + fieldName;
                } else { // this = xx
                    origin = base;
                    contrValue = getContrValue(base);
                }
            } else { // static call
                return getOrAddContr(null);
            }
        } else if (value.contains(ContrUtil.sPOLLUTED)) {
            origin = null;
            contrValue = ContrUtil.sPOLLUTED;
        } else {
            int paramIdx = ContrUtil.string2Int(value) + 1;
            CSVar origin_p = callSiteVars.get(paramIdx);
            if (value.lastIndexOf("-") > 5) {
                String fieldName = Strings.extractFieldName(value);
                origin = getCorrespondFieldVar(origin_p, fieldName);
                Contr baseContr = getContr(origin_p);
                String baseValue = getContrValue(baseContr);
                contrValue = baseValue.endsWith(ContrUtil.sNOT_POLLUTED) ? baseValue : baseValue + "-" + fieldName;
            } else {
                origin = origin_p;
            }
        }
        Contr ret;
        if (containsContr(origin)) {
            ret = drivenMap.get(origin).copy();
        } else {
            ret = getOrAddContr(origin);
            if (!isFilterNonSerializable || !isTransient(ret)) ret.setValue(contrValue);
        }
        if (isIntra) ret.setIntra();
        return ret;
    }

    private Pointer getCorrespondFieldVar(CSVar base, String fieldName) {
        JField field = base.getVar().getClassField(fieldName);
        if (field != null) {
            InstanceField iFiled = csManager.getInstanceField(base, field);
            return iFiled;
        } else {
            return base;
        }
    }

    /**
     * querying by LDFT
     */
    private PointsTo findPointsTo(Pointer pointer) {
        PointsTo pt = PointsTo.make();
        if (stackManger.containsQuery(pointer)) return pt;
        stackManger.pushQuery(pointer);

        LinkedList<Pointer> workList = new LinkedList<>();
        workList.add(pointer);
        Set<Pointer> marked = Sets.newSet();

        while (!workList.isEmpty()) {
            Pointer p = workList.poll();
            if (containsContr(p) && !p.isReQuery()) {
                pt.add(drivenMap.get(p));
                continue;
            }
            for (PointerFlowEdge pfe : p.getInEdges()) {
                Pointer source = pfe.source();
                switch (pfe.kind()) {
                    case NEW, NEW_CONTR -> {
                        Contr newContr = Contr.newInstance(p);
                        Obj obj = pfe.sourceObj().getObject();
                        newContr.setType(obj.getType());
                        if (obj instanceof MockObj mockObj && mockObj.getDescriptor().string().equals("Controllable")) {
                            newContr.setValue(((ContrAlloc) mockObj.getAllocation()).contr());
                        } else if (obj instanceof ConstantObj co && co.getAllocation() instanceof ClassLiteral cl) {
                            newContr.setType(cl.getTypeValue());
                        } else {
                            String newType = "new " + obj.getType();
                            newContr.setValue(newType);
                            newContr.setNew();
                        }
                        pt.add(newContr);
                    }
                    case LOCAL_ASSIGN, SUMMARY_ASSIGN, INSTANCE_STORE -> propagate(source, marked, workList);
                    case CAST -> {
                        Contr from = getContr(source);
                        if (from != null && (ContrUtil.isControllable(from) || from.isNew())) {
                            SpecialType st = pfe.getSpecialTransfer();
                            Contr contr = from.copy();
                            contr.setCasted();
                            contr.setType(st.getType());
                            if (from.isNew()) {
                                contr.setValue("new " + st.getType());
                                contr.addNewType(st.getType());
                            }
                            pt.add(contr);
                        }
                    }
                    case STATIC_LOAD, STATIC_STORE -> pt.add(findPointsTo(source));
                    case INSTANCE_LOAD -> {
                        CSVar base = null;
                        Set<PointerFlowEdge> matchEdges = null;
                        String fieldName = null;
                        Contr contr = Contr.newInstance(source);
                        if (source instanceof InstanceField iField) {
                            base = iField.getBaseVar();
                            fieldName = iField.getField().getName();
                            matchEdges = pointerFlowGraph.getMatchEdges(iField.getField());
                        } else if (source instanceof ArrayIndex arrayIndex) {
                            base = arrayIndex.getArrayVar();
                            fieldName = "arr";
                            matchEdges = pointerFlowGraph.getMatchEdges(base.getVar().getMethod().getDeclaringClass(), base.getType());
                            contr.setType(p.getType()); // element type
                        }
                        if (!processAlias(source, matchEdges, pt, pfe.getLineNumber(), fieldName)) {
                            Contr baseContr = getContr(base);
                            if (ContrUtil.isControllable(baseContr)) {
                                if (source instanceof ArrayIndex) {
                                    contr.setValue(baseContr.getValue() + "-" + fieldName);
                                } else if (!isFilterNonSerializable || (contr.isSerializable() && !contr.isTransient())) {
                                    if (fieldName.equals("this$0")) contr.setValue(baseContr.getValue()); // Class.this的一种访问形式
                                    else contr.setValue(baseContr.getValue() + "-" + fieldName);
                                }
                            }
                            pt.add(contr);
                        }
                    }
                    case ELEMENT_STORE -> {
                        Contr arrContr = getOrAddContr(p);
                        if (source != null) {
                            arrContr.addArrElement(getContr(source));
                        } else if (pfe.sourceObj() != null) {
                            Obj obj = pfe.sourceObj().getObject();
                            if (obj instanceof MockObj mockObj && mockObj.getDescriptor().string().equals("Controllable")) arrContr.setValue(((ContrAlloc) mockObj.getAllocation()).contr());
                        }
                        updateContr(p, arrContr);
                        pt.add(arrContr);
                    }
                    case OTHER -> {
                        if (pfe instanceof TaintTransferEdge tte) {
                            tte.getTransfers().forEach(t -> {
                                Contr from = getContr(source);
                                if (from != null && (ContrUtil.isControllable(from) || from.isNew() || from.getCS() != null)) {
                                    Type type = t instanceof SpecialType st ? st.getType() : tte.target().getType();
                                    Contr contr = from.copy();
                                    contr.setType(type);
                                    if (tte.isNewTransfer()) contr.setNew();
                                    pt.add(contr);
                                }
                            });
                        }
                    }
                }
            }
        }
        stackManger.popQuery();
        return pt;
    }

    private void propagate(Pointer p, Set<Pointer> marked, LinkedList<Pointer> workList) {
        if (marked.add(p)) {
            workList.addFirst(p);
        }
    }

    /**
     * proxy dispatch
     */
    private void processProxy(Invoke stmt, List<Contr> csContr, List<String> csContrValue) {
        MethodRef methodRef = stmt.getMethodRef();
        String className = methodRef.getDeclaringClass().getName();
        String methodName = methodRef.getName();

        if (proxySkipClasses.contains(className) || methodName.equals("iterator")) {
            return;
        }
        Contr baseContr = csContr.get(0);
        if (baseContr != null && ContrUtil.isCallSite(baseContr.getValue()) && !baseContr.isCasted()) {
            for (JMethod callee : World.get().getInvocationHandlerMethod()) {
                if (ContrUtil.isControllable(baseContr)) plugin.onNewDeser(callee);
                addWL(stmt, callee, csContr, getDynamicProxyEdge(csContrValue));
            }
        }
    }

    private boolean processAlias(Pointer source, Set<PointerFlowEdge> matchEdges, PointsTo pt, int lineNumber, String fieldName) {
        boolean ret = false;
        for (PointerFlowEdge matchEdge : matchEdges) {
            Pointer matchSource = matchEdge.source();
            Pointer matchTarget = matchEdge.target();
            if (same(source, matchTarget)) {
                JMethod targetMethod = getPointerMethod(matchTarget);
                if (targetMethod == null || targetMethod.getName().equals("<init>")) continue;
                String ifRange = pointerFlowGraph.getIfRange(matchEdge);
                if (!ifRange.equals("-1")) {
                    int ifStart = Integer.parseInt(ifRange.split("->")[0]);
                    int ifEnd = Integer.parseInt(ifRange.split("->")[1]);
                    JMethod ifContainer = pointerFlowGraph.getIfContainer(matchEdge);
                    if (curMethod.equals(ifContainer) && (lineNumber >= ifEnd || lineNumber <= ifStart)) continue;
                }
                Contr aliasContr = findPointsTo(matchSource).getMergedContr();
                boolean changed = pt.add(aliasContr);
                if (!ret) ret = changed;
                if (changed && !Objects.equals(getPointerMethod(source), targetMethod) // If the source variable does not belong to the current method, the parameter source may not be consistent
                        && !pt.isEmpty()
                        && ContrUtil.isControllableParam(pt.getMergedContr())) {
                    String value = pt.getMergedContr().getValue();
                    pt.setValue(source instanceof InstanceField ? ContrUtil.replaceContr(value, ContrUtil.sTHIS + "-" + fieldName) : ContrUtil.replaceContr(value, ContrUtil.sPOLLUTED));
                }
            }
        }
        return ret;
    }

    /**
     * propagate controllability
     */
    private void processTransfer(JMethod ref, Invoke callSite) {
        Set<TaintTransfer> transfers = ref.getTransfer();
        for (TaintTransfer transfer : transfers) {
            Var toVar = InvokeUtils.getVar(callSite, transfer.to().index());
            if (toVar == null) continue;
            Var fromVar = InvokeUtils.getVar(callSite, transfer.from().index());
            CSVar to = csManager.getCSVar(context, toVar);
            CSVar from = csManager.getCSVar(context, fromVar);
            Contr fromContr = getContr(from);
            if (fromContr != null && (ContrUtil.isControllable(fromContr) || fromContr.getCS() != null || fromContr.isNew())) {
                String stype = transfer.type();
                Type type = stype.equals("from") ? fromContr.getType() : typeSystem.getType(stype);
                addPFGEdge(new TaintTransferEdge(from, to, transfer.isNewTransfer()), new SpecialType(type), lineNumber);
            }
            if (ref.toString().equals("<java.lang.reflect.Method: java.lang.String getName()>")) mayCreateRoute = true;
        }
    }

    /**
     * special behavior such as adding reflection jump edge, model javaBean API
     */
    private void processBehavior(JMethod method, Invoke stmt, List<CSVar> callSiteVars, List<Contr> csContr, List<String> csContrValue) {
        Map<String, String> imitatedBehavior = method.getImitatedBehavior();
        if (imitatedBehavior.containsKey("jump")) {
            String target = imitatedBehavior.get("jump");
            switch (target) {
                case "constructor" -> {
                    int idx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    Contr fromContr = csContr.get(idx);
                    if (fromContr == null) return;
                    if (method.isSink()) { // forName as a sink
                        Contr loaderContr = csContr.get(callSiteVars.size() - 1);
                        if (ContrUtil.isControllable(fromContr) && ContrUtil.isControllable(loaderContr)
                                && typeSystem.isSubtype(typeSystem.getType("java.net.URLClassLoader"), loaderContr.getType())) {
                            addWL(stmt, method, csContr, csContrValue);
                            return;
                        }
                    }
                    String clzName;
                    Set<JMethod> callees;
                    Type expandArgType = null;
                    List<Type> argTypes;
                    String mName;
                    if (isStringType(fromContr.getType())) {
                        clzName = ContrUtil.convert2Reg(fromContr.getValue());
                        argTypes = new ArrayList<>();
                        mName = "<clinit>";
                    } else {
                        int pidx = InvokeUtils.toInt(imitatedBehavior.get("paramIdx")) + 1;
                        Contr paramContr = csContr.get(pidx);
                        ArrayList<Contr> argContrs = paramContr != null ? paramContr.getArrayElements() : new ArrayList<>();
                        if (argContrs.isEmpty() && ContrUtil.isControllable(paramContr)) expandArgType = getContrType(paramContr);
                        argTypes = argContrs.stream().map(Contr::getType).toList();
                        clzName = fromContr.getOrigin().getType().getName();
                        if (clzName.equals("java.lang.Class")) clzName = "java.lang.Object";
                        mName = "<init>";
                    }
                    callees = World.get().filterMethods(mName, clzName, argTypes, ContrUtil.isControllableParam(fromContr), isFilterNonSerializable, expandArgType);
                    if (callees.size() > 1) logger.info("[+] {} possible init target in {}", callees.size(), curMethod);
                    for (JMethod init : callees) {
                        List<String> edgeContr = new ArrayList<>();
                        edgeContr.add(csContrValue.get(0));
                        int pSize = init.getIR().getParams().size(); // jump edge
                        List<String> copied = Collections.nCopies(pSize, csContrValue.get(1));
                        edgeContr.addAll(copied);
                        addWL(stmt, init, csContr, edgeContr);
                    }
                    if (method.getName().equals("newInstance") && stmt.getResult() != null) {
                        CSVar retVar = csManager.getCSVar(context, stmt.getResult());
                        Contr retContr = getContr(retVar);
                        if (retContr == null) retContr = Contr.newInstance(retVar);
                        if (ContrUtil.isControllable(fromContr) && !ContrUtil.isControllable(retContr)) {
                            retContr.setValue(fromContr.getValue());
                            updateContr(retVar, retContr);
                        }
                    }
                }
                case "inference" -> {
                    int idx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    int ridx = InvokeUtils.toInt(imitatedBehavior.get("recIdx")) + 1;
                    int pidx = InvokeUtils.toInt(imitatedBehavior.get("paramIdx")) + 1;
                    if (isOneInEdge(callSiteVars.get(idx), csContrValue.get(idx))) return;
                    Contr nameContr = csContr.get(idx);
                    if (nameContr == null) return;
                    String nameValue = nameContr.getValue();
                    if (nameValue.startsWith(ContrUtil.sParam)) {
                        stmt.setFilterByCaller("edge:" + nameValue);
                    }
                    String nameReg = ContrUtil.convert2Reg(nameValue);
                    Contr paramContr = csContr.get(pidx);
                    boolean expandArg = false;
                    Type expandArgType = null;
                    ArrayList<Contr> argContrs = paramContr != null ? paramContr.getArrayElements() : new ArrayList<>();
                    if (argContrs.isEmpty() && ContrUtil.isControllable(paramContr)) {
                        expandArg = true;
                        expandArgType = getContrType(paramContr);
                    }
                    List<Type> argTypes = argContrs.stream().map(Contr::getType).toList();
                    Contr recvContr = csContr.get(ridx);
                    if (recvContr == null) return;
                    Set<JMethod> callees = World.get().filterMethods(nameReg, recvContr.getType(), argTypes, ContrUtil.isControllableParam(recvContr), isFilterNonSerializable, expandArgType); // for example getxxx
                    if (callees.size() > 1) logger.info("[+] {} possible invoke target in {}", callees.size(), curMethod);
                    if (nameReg.equals(".*")) callees.addAll(World.get().getInvocationHandlerMethod());
                    for (JMethod callee : callees) {
                        List<String> edgeContr = new ArrayList<>();
                        edgeContr.add(csContrValue.get(ridx));
                        if (callee.isInvoke()) {
                            edgeContr.add(csContrValue.get(ridx));
                            edgeContr.add(nameValue);
                            edgeContr.add(csContrValue.get(pidx));
                        } else {
                            if (expandArg) {
                                callee.getIR().getParams().forEach(p -> edgeContr.add(paramContr.getValue()));
                            } else {
                                argContrs.forEach(argContr -> edgeContr.add(argContr.getValue()));
                            }
                        }
                        addWL(stmt, callee, csContr, edgeContr);
                    }
                }
                case "get" -> {
                    int getIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    String fromValue = csContrValue.get(getIdx);
                    if (ContrUtil.isControllable(fromValue) && stmt.getResult() != null) {
                        Pointer p = csManager.getCSVar(context, stmt.getResult());
                        Contr retContr = getOrAddContr(p);
                        retContr.setValue("get+" + fromValue);
                        updateContr(p, retContr);
                    }
                }
                case "set" -> {
                    int setIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    String fromValue = csContrValue.get(setIdx);
                    if (ContrUtil.isControllable(fromValue) && stmt.getResult() != null) {
                        Pointer p = csManager.getCSVar(context, stmt.getResult());
                        Contr retContr = getOrAddContr(p);
                        retContr.setValue("set+" + fromValue);
                        updateContr(p, retContr);
                    }
                }
                case "run" -> {
                    int fromIdx = InvokeUtils.toInt(imitatedBehavior.get("fromIdx")) + 1;
                    Contr contr = csContr.get(fromIdx);
                    if (contr == null) return;
                    JMethod callee = CallGraphs.resolveCalleesOf(contr.getJClass(), "java.lang.Object run()");
                    if (callee != null) {
                        List<Contr> edgeContr = csContr.subList(fromIdx, csContr.size());
                        List<String> edgeContrValue = csContrValue.subList(fromIdx, csContr.size());
                        addWL(stmt, callee, edgeContr, edgeContrValue);
                        sideEffects(stmt, Set.of(callee), callSiteVars, callSiteVars.get(fromIdx), csContrValue);
                    }
                }
            }
        } else if (imitatedBehavior.containsKey("action")) {
            String behavior = imitatedBehavior.get("action");
            switch (behavior) {
                case "replace" -> {
                    if (csContrValue.stream().allMatch(s -> ContrUtil.hasCS(s))) {
                        try {
                            Class c = Class.forName(method.getDeclaringClass().getName());
                            Class[] paramTypes = new Class[2];
                            for (int i = 0; i < method.getParamCount(); i++) {
                                paramTypes[i] = Class.forName(method.getParamType(i).getName());
                            }
                            Method rep = c.getDeclaredMethod(method.getName(), paramTypes);
                            String s = ContrUtil.getCS(csContrValue.get(0));
                            String replacedValue = (String) rep.invoke(s, ContrUtil.getCS(csContrValue.get(1)), ContrUtil.getCS(csContrValue.get(2)));
                            CSVar base = callSiteVars.get(0);
                            Contr replacedContr = getContr(base);
                            replacedContr.setValue(replacedValue);
                            updateContr(base, replacedContr);
                        } catch (Exception e) {
                            logger.info("[-] {} error when replacing in {}", curMethod);
                        }
                    }
                }
                case "polluteRec" -> {
                    CSVar base = callSiteVars.get(0);
                    Contr baseContr = csContr.get(0);
                    if (baseContr != null) {
                        for (int i = 1; i < callSiteVars.size(); i++) {
                            String contr = csContrValue.get(i);
                            if (ContrUtil.isControllable(contr)) {
                                baseContr.setValue(contr);
                                updateContr(base, baseContr);
                                CSObj csFrom = ContrUtil.getObj(callSiteVars.get(i), contr, heapModel, context, csManager);
                                addPFGEdge(csFrom, base, FlowKind.ELEMENT_STORE, lineNumber);
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    private boolean isOneInEdge(Pointer p, String contr) {
        if (ContrUtil.isControllableParam(contr)) return false;
        if (p.getInEdges().size() == 1) {
            for (PointerFlowEdge edge : p.getInEdges()) {
                if (edge.source() != null && edge.source().getInEdges().size() == 0) {
                    if (edge.source() instanceof InstanceField iField && pointerFlowGraph.getMatchEdges(iField.getField()).size() != 0) return false;
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * construc proxy jump edge
     */
    private List<String> getDynamicProxyEdge(List<String> csContr) {
        List<String> invokeEdge = new ArrayList<>();
        invokeEdge.add(csContr.get(0));
        invokeEdge.add(csContr.get(0));
        invokeEdge.add(ContrUtil.sNOT_POLLUTED);
        for (int i = 1; i < csContr.size(); i++) {
            String v = csContr.get(i);
            if (ContrUtil.isControllable(v)) {
                invokeEdge.add(v);
                break;
            }
        }
        if (invokeEdge.size() == 3) invokeEdge.add(ContrUtil.sNOT_POLLUTED);
        return invokeEdge;
    }

    private boolean same(Pointer p1, Pointer p2) {
        if (p1 == null || p2 == null) return false;
        if (Objects.equals(p1, p2)) return true;
        if (p1 instanceof InstanceField f1 && p2 instanceof InstanceField f2) {
            JField f1Field = f1.getField();
            JField f2Field = f2.getField();
            return f1Field.equals(f2Field) && sameBase(f1.getBaseVar(), f2.getBaseVar());
        } else if (p1 instanceof ArrayIndex a1 && p2 instanceof ArrayIndex a2) {
            return sameBase(a1.getArrayVar(), a2.getArrayVar());
        }
        return false;
    }

    private boolean sameBase(CSVar var1, CSVar var2) {
        if (Objects.equals(var1, var2)) return true;
        if (isThis(var1) && isThis(var2) && Objects.equals(var1.getType(), var2.getType())) return true;
        return false;
    }

    /**
     * refined CHA to reduce FP
     */
    private Collection<? extends JMethod> filterCHA(Set<JMethod> methods, Contr baseContr, Type refType) {
        if (methods.size() <= 1) return methods;
        Type type = baseContr.getType();
        boolean ignoredType = !typeSystem.isSubtype(refType, type);
        boolean isConstruct = baseContr.isSerializable() && ContrUtil.isControllable(baseContr) && baseContr.getOrigin() instanceof CSVar var && var.isAssigned();
        return methods.stream()
                .filter(method -> isFilterNonSerializable ? (method.getDeclaringClass().isSerializable() ? true : isConstruct) : true)
                .filter(method -> ignoredType || typeSystem.isSubtype(type, method.getDeclaringClass().getType()))
                .filter(method -> !method.isPrivate())
                .collect(Collectors.toSet());
    }

    private void filterByCaller(Invoke stmt, Edge callEdge, List<String> edgeContr) {
        if (mayCreateRoute) {
            if (stackManger.isInIf()) {
                ConditionExp conditionExp = stackManger.getIfCondition(curMethod);
                if (conditionExp != null) {
                    CSVar ifVar = csManager.getCSVar(context, conditionExp.getOperand1());
                    String invokeDispatch = curMethod.getInvokeDispatch(ifVar);
                    if (invokeDispatch != null) {
                        callEdge.setFilterByCaller("name:" + invokeDispatch);
                    }
                    if (stmt.getMethodRef().toString().equals("<sun.reflect.annotation.AnnotationInvocationHandler: java.lang.Boolean equalsImpl(java.lang.Object)>")
                            || stmt.getMethodRef().toString().equals("<java.rmi.server.RemoteObjectInvocationHandler: boolean equals(java.lang.Object)>")) { // TODO improve this
                        callEdge.setFilterByCaller("name: equals#param-1");
                    }
                }
            }
            List<Var> args = stmt.getInvokeExp().getArgs();
            if (args.size() == 1 && stmt.getLValue() != null) {
                String constString = getConstString(args.get(0));
                if (edgeContr.get(0).startsWith(ContrUtil.sParam) && constString != null) {
                    curMethod.addInvokeDispatch(csManager.getCSVar(context, stmt.getLValue()), constString + "#" + edgeContr.get(0));
                }
            }
        }
        if (stmt.isFilterByCaller()) {
            callEdge.setFilterByCaller(stmt.getFilterByCaller());
        }
    }

    private void polluteBase(Contr contr) {
        Pointer origin = contr.getOrigin();
        if (origin instanceof InstanceField iField) {
            CSVar base = iField.getBaseVar();
            if (containsContr(base) && ContrUtil.isControllable(contr)) {
                Contr old = drivenMap.get(base);
                if (old != null && !ContrUtil.isControllable(old)) {
                    old.setValue(contr.getValue());
                    updateContr(base, old);
                }
            }
        }
    }

    /**
     * summary for this.f, param-i
     */
    public void complementSummary(List<Var> params, Var tv) {
        if (tv != null) {
            CSVar thisVar = csManager.getCSVar(context, tv);
            tv.getUsedFields().forEach(field -> {
                if (!isIgnored(field.getType())) {
                    InstanceField to = csManager.getInstanceField(thisVar, field);
                    if (to.getInEdges().size() > 0) {
                        String key = tv.getName().substring(1) + "-" + field.getName();
                        String oldV = curMethod.getSummary(key);
                        String newV = getContrValue(to);
                        if (ContrUtil.needUpdateInMerge(oldV, newV)) {
                            curMethod.setSummary(key, newV);
                        }
                    }
                }
            });
        }
        for (int i = 0; i < params.size(); i++) {
            CSVar param = csManager.getCSVar(context, params.get(i));
            if (param.getInEdges().size() > 1) {
                param.removePFG(FlowKind.NEW_CONTR); // remove the initial controllable edge
                drivenMap.remove(param);
                String key = "param-" + i;
                String oldV = curMethod.getSummary(key);
                String newV = getContrValue(param);
                if (ContrUtil.needUpdateInMerge(oldV, newV)) curMethod.setSummary(key, newV);
            }
        }
    }

    private boolean isStringType(Type type) {
        return type.getName().equals("java.lang.String");
    }

    private boolean useFiled(CSVar csVar, String target) {
        if (csVar == null) return false;
        List<StoreField> storeFields = csVar.getVar().getStoreFields();
        for (StoreField storeField : storeFields) {
            JField field = storeField.getFieldRef().resolve();
            if (isIgnored(field.getType())) continue;
            String key = thisVar.getVar().getName().substring(1) + "-" + field.getName();
            if (key.equals(target)) return true;
        }
        return false;
    }

}
