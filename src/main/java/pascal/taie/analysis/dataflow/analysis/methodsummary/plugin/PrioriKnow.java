package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;

public class PrioriKnow implements Plugin {

    private static final Logger logger = LogManager.getLogger(PrioriKnow.class);

    private String config_path;

    public PrioriKnow(String config_path) {
        super();
        this.config_path = config_path;
    }

    @Override
    public void onStart() {
        PrioriKnowConfig config = PrioriKnowConfig.loadConfig(
                config_path,
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info("load {} sinks, {} transfers, {} ignores, {} imitates",
                config.sinks().size(),
                config.transfers().size(),
                config.ignores().size(),
                config.imitates().size());
    }

}
