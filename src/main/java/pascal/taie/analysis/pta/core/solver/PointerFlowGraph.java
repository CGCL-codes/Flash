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

package pascal.taie.analysis.pta.core.solver;

import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.TwoKeyMap;
import pascal.taie.util.collection.Views;
import pascal.taie.util.graph.Edge;
import pascal.taie.util.graph.Graph;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Represents pointer flow graph in context-sensitive pointer analysis.
 */
public class PointerFlowGraph implements Graph<Pointer> {

    private final CSManager csManager;

    private Map<JField, Set<PointerFlowEdge>> fieldMatchEdges;

    private TwoKeyMap<JClass, Type, Set<PointerFlowEdge>> arrayMatchEdges;

    private Map<PointerFlowEdge, String> ifRangeMap;

    private Map<PointerFlowEdge, JMethod> ifContainer;

    public PointerFlowGraph(CSManager csManager) {
        this.csManager = csManager;
        this.fieldMatchEdges = Maps.newMap();
        this.arrayMatchEdges = Maps.newTwoKeyMap();
        this.ifRangeMap = Maps.newMap();
        this.ifContainer = Maps.newMap();
    }

    /**
     * Adds a pointer flow edge and returns the edge in the PFG.
     * If the edge to add already exists, then
     * <ul>
     *     <li>if the edge is of {@link FlowKind#OTHER},
     *     returns the existing edge;
     *     <li>otherwise, returns {@code null}, meaning that the edge
     *     does not need to be processed again.
     * </ul>
     */
    public PointerFlowEdge addEdge(PointerFlowEdge edge) {
        if (edge.kind() == FlowKind.INSTANCE_STORE) {
            if (edge.target() instanceof InstanceField iField) {
                JField field = iField.getField();
                fieldMatchEdges.computeIfAbsent(field, f -> new HashSet<>()).add(edge);
            } else if (edge.target() instanceof ArrayIndex varArray) {
                CSVar base = varArray.getArrayVar();
                Type type = base.getType();
                JClass jClass = base.getVar().getMethod().getDeclaringClass();
                if (arrayMatchEdges.containsKey(jClass, type)) {
                    arrayMatchEdges.get(jClass, type).add(edge);
                } else {
                    Set<PointerFlowEdge> set = new HashSet<>();
                    set.add(edge);
                    arrayMatchEdges.put(jClass, type, set);
                }
            }
        }
        return edge.target().addEdge(edge);
    }

    @Override
    public Set<? extends Edge<Pointer>> getInEdgesOf(Pointer node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<PointerFlowEdge> getOutEdgesOf(Pointer pointer) {
        return pointer.getOutEdges();
    }

    public Stream<Pointer> pointers() {
        return csManager.pointers();
    }

    @Override
    public Set<Pointer> getPredsOf(Pointer node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<Pointer> getSuccsOf(Pointer node) {
        return Views.toMappedSet(node.getOutEdges(),
                PointerFlowEdge::target);
    }

    @Override
    public Set<Pointer> getNodes() {
        return pointers().collect(Collectors.toUnmodifiableSet());
    }

    public Set<PointerFlowEdge> getMatchEdges(JField field) {
        return fieldMatchEdges.getOrDefault(field, Set.of());
    }

    public Set<PointerFlowEdge> getMatchEdges(JClass jClass, Type type) {
        return arrayMatchEdges.getOrDefault(jClass, type, Set.of());
    }

    public void addIfRange(PointerFlowEdge edge, int ifStart, int ifEnd, JMethod method) {
        if (ifStart != -1 && ifEnd != -1) {
            String ifRange = ifStart + "->" + ifEnd;
            ifRangeMap.put(edge, ifRange);
            ifContainer.put(edge, method);
        }
    }

    public String getIfRange(PointerFlowEdge edge) {
        return ifRangeMap.getOrDefault(edge, "-1");
    }

    public JMethod getIfContainer(PointerFlowEdge edge) {
        return ifContainer.getOrDefault(edge, null);
    }
}
