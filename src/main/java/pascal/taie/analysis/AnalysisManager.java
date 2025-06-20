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

package pascal.taie.analysis;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.SummaryAnalysisDriver;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.config.ConfigException;
import pascal.taie.config.Plan;
import pascal.taie.ir.IR;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.Timer;
import pascal.taie.util.graph.SimpleGraph;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.*;

/**
 * Creates and executes analyses based on given analysis plan.
 */
public class AnalysisManager {

    private static final Logger logger = LogManager.getLogger(AnalysisManager.class);

    private final Plan plan;

    /**
     * Whether keep results of all analyses. If the value is {@code false},
     * this manager will clear unused results after it finishes each analysis.
     */
    private final boolean keepAllResults;

    /**
     * Graph that describes the dependencies among analyses (represented
     * by their IDs) in the plan. This graph is used to check whether
     * certain analysis results are useful.
     */
    private SimpleGraph<String> dependenceGraph;

    /**
     * List of analyses that have been executed. For an element in this list,
     * once its result is clear, it will also be removed from this list.
     */
    private List<Analysis> executedAnalyses;

    private List<JClass> classScope;

    private List<JMethod> methodScope;

    private static LinkedList<JMethod> workList;

    private static List<MethodAnalysis> methodAnalyses;

    public AnalysisManager(Plan plan) {
        this.plan = plan;
        this.keepAllResults = plan.keepResult().contains(Plan.KEEP_ALL);
        workList = new LinkedList<>();
        methodAnalyses = new ArrayList<>();
    }

    /**
     * Executes the analysis plan.
     */
    public void execute() {
        // initialize
        if (!keepAllResults) {
            dependenceGraph = new SimpleGraph<>();
            for (AnalysisConfig c : plan.dependenceGraph()) {
                for (AnalysisConfig succ : plan.dependenceGraph().getSuccsOf(c)) {
                    dependenceGraph.addEdge(c.getId(), succ.getId());
                }
            }
            executedAnalyses = new ArrayList<>();
        }
        // execute analyses
        plan.analyses().forEach(config -> methodAnalyses.add((MethodAnalysis) getAnalysis(config)));
        World.get().filterHandler();
        workList.addAll(World.get().getGCEntries());

        Timer.runAndCount(() -> {
            while (!workList.isEmpty()) {
                JMethod method = workList.poll();
                if (!method.hasSummary()) {
                    runMethodAnalysis(method);
                }
            }
        }, "deserialization call graph");

        Timer.runAndCount(() -> {
            SummaryAnalysisDriver analysis = (SummaryAnalysisDriver) getAnalysis(methodAnalyses, SummaryAnalysisDriver.ID);
            analysis.finish();
        }, "collect gc");
    }

    public static void runMethodAnalysis(JMethod m) {
        if (m.isSink() || m.hasSummary() || m.isIgnored()) return;
        methodAnalyses.forEach(analysis -> {
            IR ir = m.getIR();
            Object result = analysis.analyze(ir);
            if (result != null) {
                ir.storeResult(analysis.getId(), result);
            }
        });
    }

    private MethodAnalysis getAnalysis(List<MethodAnalysis> methodAnalyses, String id) {
        for (MethodAnalysis analysis : methodAnalyses) {
            if (analysis.getId().equals(id)) {
                return analysis;
            }
        }
        return null;
    }

    private Analysis getAnalysis(AnalysisConfig config) {
        Analysis analysis;
        try {
            Class<?> clazz = Class.forName(config.getAnalysisClass());
            Constructor<?> ctor = clazz.getConstructor(AnalysisConfig.class);
            analysis = (Analysis) ctor.newInstance(config);
        } catch (ClassNotFoundException e) {
            throw new AnalysisException("Analysis class " +
                    config.getAnalysisClass() + " is not found", e);
        } catch (NoSuchMethodException | IllegalAccessException e) {
            throw new AnalysisException("Failed to get constructor " +
                    config.getAnalysisClass() + "(AnalysisConfig), " +
                    "thus the analysis cannot be executed by Tai-e", e);
        } catch (InstantiationException | InvocationTargetException e) {
            throw new AnalysisException("Failed to initialize " +
                    config.getAnalysisClass(), e);
        } catch (ClassCastException e) {
            throw new ConfigException(
                    config.getAnalysisClass() + " is not an analysis class");
        }
        return analysis;
    }
}
