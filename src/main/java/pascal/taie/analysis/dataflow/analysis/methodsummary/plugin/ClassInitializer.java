package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import pascal.taie.analysis.AnalysisManager;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.HashSet;
import java.util.Set;

public class ClassInitializer implements Plugin {

    private Set<JClass> noDeserClz;

    private Set<JClass> initClz;

    private Set<JClass> deserClz;

    @Override
    public void onStart() {
        noDeserClz = new HashSet<>();
        initClz = new HashSet<>();
        deserClz = new HashSet<>();
    }

    @Override
    public void onNewInit(JMethod method) {
        JClass clz = method.getDeclaringClass();
        if (method.isStatic() || method.isConstructor() || method.isSource()) {
            initializeClass(clz);
        }
    }

    public void initializeClass(JClass cls) {
        if (cls == null || cls.isIgnored() || initClz.contains(cls)) {
            return;
        }
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        JMethod clinit = cls.getClinit();
        if (clinit != null) {
            initClz.add(cls);
            AnalysisManager.runMethodAnalysis(clinit);
        }
    }

    @Override
    public void onNewDeser(JMethod method) {
        JClass clz = method.getDeclaringClass();
        initializeReadObject(clz);
    }

    private void initializeReadObject(JClass cls) {
        if (cls == null || !cls.isSerializable() || noDeserClz.contains(cls) || deserClz.contains(cls)) {
            return;
        }
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeReadObject(superclass);
        }
        boolean existDeserM = false;
        for (JMethod readObject : cls.getDeclaredMethods()) {
            if (readObject.isSource()) {
                deserClz.add(cls);
                existDeserM = true;
                AnalysisManager.runMethodAnalysis(readObject);
            }
        }
        if (!existDeserM) noDeserClz.add(cls);
    }

}
