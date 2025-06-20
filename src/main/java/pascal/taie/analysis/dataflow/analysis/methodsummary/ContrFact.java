package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.analysis.dataflow.fact.MapFact;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;

import java.util.Collections;
import java.util.Map;

public class ContrFact extends MapFact<Pointer, Contr> {

    public ContrFact() {
        this(Collections.emptyMap());
    }

    public ContrFact(Map<Pointer, Contr> map) {
        super(map);
    }

    public boolean update(CSVar p, Contr contr) {
        return super.update(p, contr);
    }

    public ContrFact copy() {
        return new ContrFact(this.map);
    }

}
