package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.Analysis;
import pascal.taie.util.Timer;

public class AnalysisTimer implements Plugin {

    private static final Logger logger = LogManager.getLogger(Analysis.class);

    private Timer timer;

    @Override
    public void onStart() {
        timer = new Timer("Dataflow analysis");
        timer.start();
    }

    @Override
    public void onFinish() {
        timer.stop();
        logger.info(timer);
    }

}
