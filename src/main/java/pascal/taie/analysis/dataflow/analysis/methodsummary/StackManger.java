package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.GCCollectorInProcess;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;
import java.util.*;

/**
 * manger for important data during analysis such as method stack, query stack, and so on
 */
public class StackManger {

    private Stack<JMethod> methodStack;

    private Stack<Pointer> queryStack;

    private Stack<If> ifStack; // for simple condition handle

    private Map<If, JMethod> ifContainer;

    private Map<CSVar, Pointer> instanceOfRet;

    private Map<Pointer, Type> instanceOfType;

    private Map<Stmt, Pointer> instanceOfEnd;

    private GCCollectorInProcess gcCollector;

    private Set<JField> restoredField;

    public StackManger(CSCallGraph csCallGraph) {
        this.methodStack = new Stack<>();
        this.queryStack = new Stack<>();
        this.ifStack = new Stack<>();
        this.ifContainer = new HashMap<>();
        this.instanceOfEnd = new HashMap<>();
        this.instanceOfRet = new HashMap<>();
        this.instanceOfType = new HashMap<>();
        this.restoredField = new HashSet<>();
        this.gcCollector= new GCCollectorInProcess(csCallGraph, World.get().getOptions().getGC_OUT());
    }

    public void pushMethod(JMethod method) {
        methodStack.push(method);
    }

    public void popMethod() {
        JMethod m = methodStack.pop();
        gcCollector.popEdge(m);
    }

    public boolean containsMethod(JMethod method) {
        return methodStack.contains(method);
    }

    public JMethod curMethod() {
        return methodStack.peek();
    }

    public void pushQuery(Pointer pointer) {
        queryStack.push(pointer);
    }

    public void popQuery() {
        queryStack.pop();
    }

    public boolean containsQuery(Pointer pointer) {
        return queryStack.contains(pointer);
    }

    public void pushIf(If ifStmt, JMethod method) {
        ifStack.push(ifStmt);
        ifContainer.put(ifStmt, method);
    }

    public boolean isInIf() {
        return !ifStack.isEmpty();
    }

    public boolean isIfEnd(Stmt stmt) {
        return getCurIf().getTarget().equals(stmt);
    }

    public void popIf() {
        If ifStmt = ifStack.pop();
        ifContainer.remove(ifStmt);
    }

    public ConditionExp getIfCondition(JMethod m) {
        If ifStmt = getCurIf();
        JMethod container = ifContainer.get(ifStmt);
        return Objects.equals(container, m) ? ifStmt.getCondition() : null;
    }

    public If getCurIf() {
        return ifStack.peek();
    }

    public JMethod getCurIfMethod() {
        return isInIf() ? ifContainer.getOrDefault(getCurIf(), null) : null;
    }

    public int getIfStart() {
        return isInIf() ? getCurIf().getLineNumber() : -1;
    }

    public int getIfEnd() {
        return isInIf() ? getCurIf().getTarget().getLineNumber() : -1;
    }

    public void putInstanceOfInfo(CSVar retVar, CSVar checkedVar, ReferenceType type) {
        instanceOfRet.put(retVar, checkedVar);
        instanceOfType.put(checkedVar, type);
    }

    public boolean containsInstanceOfRet(CSVar var) {
        return instanceOfRet.containsKey(var);
    }

    public Pointer removeInstanceOfRet(CSVar var) {
        return instanceOfRet.remove(var);
    }

    public void putInstanceOfEnd(Stmt end, Pointer p) {
        instanceOfEnd.put(end, p);
    }

    public boolean containsInstanceOfEnd(Stmt stmt) {
        return instanceOfEnd.containsKey(stmt);
    }

    public void removeInstanceOfEnd(Stmt stmt) {
        Pointer p = instanceOfEnd.get(stmt);
        instanceOfType.remove(p);
        instanceOfEnd.remove(stmt);
    }

    public boolean containsInstanceOfType(Pointer p) {
        return instanceOfType.containsKey(p);
    }

    public Type getInstanceofType(Pointer p) {
        return instanceOfType.get(p);
    }

    public int mSize() {
        return methodStack.size();
    }

    public void pushCallEdge(Edge callEdge, boolean inStack) {
        if (World.get().getOptions().isCOLLECTGC_INPROCESS()) gcCollector.pushCallEdge(callEdge, inStack);
    }

    public void finish() {
        if (World.get().getOptions().isCOLLECTGC_INPROCESS()) gcCollector.finish();
    }

    public void handleTempGC(String key) {
        if (World.get().getOptions().isCOLLECTGC_INPROCESS()) gcCollector.handleTempGC(key);
    }

    public JMethod getMethod(int i) {
        return methodStack.get(mSize() - i);
    }

    public void addRestoredField(JField field) {
        restoredField.add(field);
    }

    public boolean isRestoredField(JField field) {
        return restoredField.contains(field);
    }
}
