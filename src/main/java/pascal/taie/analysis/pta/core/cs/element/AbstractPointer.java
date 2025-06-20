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

package pascal.taie.analysis.pta.core.cs.element;

import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.core.solver.PointerFlowEdge;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.util.collection.ArraySet;
import pascal.taie.util.collection.HybridIndexableSet;
import pascal.taie.util.collection.Sets;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Stream;

abstract class AbstractPointer implements Pointer {

    private PointsToSet pointsToSet;

    private final int index;

    private final Set<Pointer> predecessors = new HybridIndexableSet<>(true);

    private final Set<CSObj> newObjs = new HybridIndexableSet<>(true);

    private final ArrayList<PointerFlowEdge> outEdges = new ArrayList<>(4);

    private final ArrayList<PointerFlowEdge> inEdges = new ArrayList<>(4);

    private Set<Predicate<CSObj>> filters = Set.of();

    private boolean reQuery = false;

    protected AbstractPointer(int index) {
        this.index = index;
    }

    @Override
    public int getIndex() {
        return index;
    }

    @Override
    public PointsToSet getPointsToSet() {
        return pointsToSet;
    }

    @Override
    public void setPointsToSet(PointsToSet pointsToSet) {
        this.pointsToSet = pointsToSet;
    }

    @Override
    public void addFilter(Predicate<CSObj> filter) {
        if (filters.isEmpty()) {
            filters = Sets.newHybridSet();
        }
        filters.add(filter);
    }

    @Override
    public Set<Predicate<CSObj>> getFilters() {
        return filters;
    }

    @Override
    public Set<CSObj> getObjects() {
        PointsToSet pts = getPointsToSet();
        return pts == null ? Set.of() : pts.getObjects();
    }

    @Override
    public Stream<CSObj> objects() {
        return getObjects().stream();
    }

    @Override
    public PointerFlowEdge addEdge(PointerFlowEdge edge) {
        assert edge.target() == this;
        Pointer source = edge.source();
        CSObj sourceObj = edge.sourceObj();
        if (source != null && predecessors.add(source)) {
            inEdges.add(edge);
            source.addOutEdge(edge);
            return edge;
        } else if (sourceObj != null && newObjs.add(sourceObj)) {
            inEdges.add(edge);
            return edge;
        } else if (edge.kind() == FlowKind.OTHER) {
            for (PointerFlowEdge inEdge : inEdges) {
                if (inEdge.equals(edge)) {
                    return inEdge;
                }
            }
            return edge;
        }
        return null;
    }

    @Override
    public void addOutEdge(PointerFlowEdge edge) {
        outEdges.add(edge);
    }

    @Override
    public Set<PointerFlowEdge> getOutEdges() {
        return Collections.unmodifiableSet(new ArraySet<>(outEdges, true));
    }

    @Override
    public Set<PointerFlowEdge> getInEdges() {
        return Collections.unmodifiableSet(new ArraySet<>(inEdges, true));
    }

    @Override
    public int getOutDegree() {
        return outEdges.size();
    }

    public void removePFG(FlowKind kind) {
        Iterator<PointerFlowEdge> iterator = inEdges.iterator();
        while (iterator.hasNext()) {
            PointerFlowEdge pfg = iterator.next();
            if (pfg.kind().equals(kind)) {
                iterator.remove();
            }
        }
    }

    public boolean isReQuery() {
        return reQuery;
    }

    @Override
    public void setReQuery(boolean b) {
        this.reQuery = b;
    }
}
