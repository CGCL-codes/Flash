package pascal.taie.analysis.dataflow.analysis;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.methodsummary.ContrFact;
import pascal.taie.analysis.dataflow.analysis.methodsummary.StackManger;
import pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.*;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.solver.Solver;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelectorFactory;
import pascal.taie.analysis.pta.core.heap.AllocationSiteBasedModel;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.solver.PointerFlowGraph;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

public class SummaryAnalysisDriver extends MethodAnalysis<DataflowResult<Stmt, ContrFact>> {

    public static final String ID = "method-summary";

    private HeapModel heapModel;

    private Context emptyContext;

    private CSManager csManager;

    private StackManger stackManger;

    private PointerFlowGraph pointerFlowGraph;

    private CSCallGraph csCallGraph;

    private Solver<Stmt, ContrFact> solver;

    private CompositePlugin plugin;

    private long allMethod = World.get().allMethods().count();

    private long analyzedMethod;

    private static final Logger logger = LogManager.getLogger(SummaryAnalysisDriver.class);

    public SummaryAnalysisDriver(AnalysisConfig config) {
        super(config);
        this.heapModel = new AllocationSiteBasedModel(getOptions());
        this.emptyContext = ContextSelectorFactory.makeCISelector().getEmptyContext();
        this.csManager = new MapBasedCSManager();
        this.csCallGraph = new CSCallGraph(csManager, emptyContext);
        this.stackManger = new StackManger(this.csCallGraph);
        this.pointerFlowGraph = new PointerFlowGraph(csManager);
        this.solver = Solver.getSolver();
        setPlugin(getOptions());
        analyzedMethod = 0;
    }

    private void setPlugin(AnalysisOptions options) {
        plugin = new CompositePlugin();
        plugin.addPlugin(
                new AnalysisTimer(),
                new ClassInitializer(),
                new PrioriKnow(options.getString("priori-knowledge"))
        );
        if (!World.get().getOptions().isCOLLECTGC_INPROCESS()) {
            plugin.addPlugin(new GCCollectorAfterProcess(csCallGraph, World.get().getOptions().getGC_OUT()));
        }
        plugin.onStart();
    }

    public void finish() {
        plugin.onFinish();
        stackManger.finish();
    }

    @Override
    public DataflowResult<Stmt, ContrFact> analyze(IR ir) {
        JMethod method = ir.getMethod();
        if (stackManger.containsMethod(method) || method.hasSummary()) return null;
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        if (cfg == null) return null;
        stackManger.pushMethod(method);
        plugin.onNewInit(method); // first analyze a method static initializer method
        csCallGraph.addReachableMethod(csManager.getCSMethod(emptyContext, method));
        SummaryAnalysis analysis = makeAnalysis(cfg, stackManger, csManager, heapModel, emptyContext, pointerFlowGraph, csCallGraph, plugin);
        DataflowResult<Stmt, ContrFact> ret = solver.solve(analysis);
        analysis.complementSummary();
        stackManger.popMethod();
        if (!method.hasSummary()) method.setSummary("return", "null+null");
        stackManger.handleTempGC(method.toString());
        analyzedMethod += 1;
        if (analyzedMethod % 5000 == 0) {
            logger.info("[+] have analyzed {} methods, remaining {} methods in stack, {} methods may need analysis", analyzedMethod, stackManger.mSize(), allMethod - analyzedMethod - stackManger.mSize());
        }
        return ret;
    }

    public static SummaryAnalysis makeAnalysis(CFG<Stmt> body, StackManger stackManger, CSManager csManager, HeapModel heapModel, Context context, PointerFlowGraph pointerFlowGraph, CSCallGraph csCallGraph, CompositePlugin plugin) {
        return new SummaryAnalysis(body, stackManger, csManager, heapModel, context, pointerFlowGraph, csCallGraph, plugin);
    }

}
