package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.List;

public class CompositePlugin implements Plugin {

    private final List<Plugin> allPlugins = new ArrayList<>();

    public void addPlugin(Plugin... plugins) {
        for (Plugin plugin : plugins) {
            allPlugins.add(plugin);
        }
    }

    @Override
    public void onStart() {
        allPlugins.forEach(Plugin::onStart);
    }

    @Override
    public void onFinish() {
        allPlugins.forEach(Plugin::onFinish);
    }

    @Override
    public void onNewInit(JMethod method) {
        allPlugins.forEach(p -> p.onNewInit(method));
    }

    @Override
    public void onNewDeser(JMethod method) {
        allPlugins.forEach(p -> p.onNewDeser(method));
    }
}
