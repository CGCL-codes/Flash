/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.language.type.Type;
import pascal.taie.util.Hashes;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Represents call edges in the call graph.
 *
 * @param <CallSite> type of call sites
 * @param <Method>   type of methods
 */
public class Edge<CallSite, Method> {

    private final CallKind kind;

    private final CallSite callSite;

    private final Method callee;

    private final int hashCode;

    private final List<String> csContr;

    private final Integer lineNumber;

    private String filterByCaller;

    private List<Type> typeList;

    private Set<Integer> casted;

    public Edge(CallKind kind, CallSite callSite, Method callee, List<String> csContr, Integer lineNumber, List<Type> typeList) {
        this.kind = kind;
        this.callSite = callSite;
        this.callee = callee;
        this.csContr = csContr;
        this.lineNumber = lineNumber;
        this.filterByCaller = "";
        this.typeList = typeList;
        this.casted = new HashSet<>();
        hashCode = Hashes.hash(kind, callSite, callee, getCSIntContr());
    }

    /**
     * @return kind of the call edge.
     */
    public CallKind getKind() {
        return kind;
    }

    /**
     * @return String representation of information for this edge.
     * By default, the information represents the {@link CallKind},
     * and other subclasses of {@link Edge} may contain additional content.
     */
    public String getInfo() {
        return kind.name();
    }

    /**
     * @return the call site (i.e., the source) of the call edge.
     */
    public CallSite getCallSite() {
        return callSite;
    }

    /**
     * @return the callee method (i.e., the target) of the call edge.
     */
    public Method getCallee() {
        return callee;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        Edge<?, ?> edge = (Edge<?, ?>) o;
        return Objects.equals(kind, edge.kind)
                && Objects.equals(callSite, edge.callSite)
                && Objects.equals(callee, edge.callee)
                && Objects.equals(getCSIntContr(), edge.getCSIntContr());
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public String toString() {
        return "[" + getInfo() + "]" + callSite + "-" + getCSIntContr() + "->" + callee;
    }

    public List<Integer> getCSIntContr() {
        return ContrUtil.string2Int(csContr);
    }

    public List<String> getCSContr() {
        return csContr;
    }

    public Integer getLineNo() {
        return lineNumber;
    }

    public void setFilterByCaller(String value) {
        filterByCaller = value;
    }

    public boolean needFilterByCaller() {
        return !filterByCaller.equals("");
    }

    public String getFilterByCaller() {
        return filterByCaller;
    }

    public List<Type> getTypeList() {
        return typeList;
    }

    public void setCasted(int i) {
        casted.add(i);
    }

    public boolean isCasted(int i) {
        return casted.contains(i);
    }
}
