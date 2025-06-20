package pascal.taie.analysis.dataflow.analysis.methodsummary;

import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Modifier;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.util.Strings;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import static pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.PUtil.getPointerMethod;

public class Contr {

    private Pointer pointer;

    private String name;

    private Type type;

    private boolean isTransient = false;

    private boolean isSerializable = false;

    private boolean isNew = false;

    private Set<Type> newType = new HashSet<>();

    private boolean isCasted = false;

    private String value = ContrUtil.sNOT_POLLUTED;

    private String constString;

    private ArrayList<Contr> arrayElements = new ArrayList<>();

    private boolean isIntra;

    private Set<String> value_patterns = new HashSet<>();

    private Contr() {
    }

    private Contr(Pointer pointer) {
        this.pointer = pointer;
        this.type = pointer.getType();
        this.isIntra = false;
        if (pointer instanceof CSVar var) {
            this.name = var.getVar().getName();
            setSerializable(var.getType());
        } else if (pointer instanceof InstanceField iField) {
            this.name = iField.toString();
            setTransient(iField.getField());
            setSerializable(iField.getField().getType());
        } else if (pointer instanceof ArrayIndex arrayVar) {
            this.name = arrayVar.toString();
            if (arrayVar.getType() instanceof ArrayType at) setSerializable(at.elementType());
        } else if (pointer instanceof StaticField sField) {
            this.name = sField.toString();
            setTransient(sField.getField());
            setSerializable(sField.getField().getType());
        }
        if (this.type.getName().equals("java.lang.reflect.Method")) { // TODO improve this
            JMethod m = getPointerMethod(pointer);
            if (m != null && m.getDeclaringClass().isSerializable() && !isSerializable()) setSerializable();
        }
    }

    public static Contr newInstance(Pointer pointer) {
        return pointer == null ? new Contr() : new Contr(pointer);
    }

    private void setTransient(JField field) {
        if (Modifier.hasTransient(field.getModifiers())) {
            setTransient();
        }
    }

    private void setTransient() {
        this.isTransient = true;
    }

    public boolean isTransient() {
        return this.isTransient;
    }

    public void setSerializable(Type type) {
        if (ContrUtil.isSerializableType(type)) setSerializable();
    }

    public void setSerializable() {
        this.isSerializable = true;
    }

    public boolean isSerializable() {
        return isSerializable;
    }

    public Type getType() {
        return type;
    }

    public void setType(Type type) {
        this.type = type;
    }

    public boolean isNew() {
        return isNew || value.startsWith("new");
    }

    public void setNew() {
        this.isNew = true;
        this.newType.add(this.type);
    }

    public void addNewType(Type type) {
        this.newType.add(type);
    }

    public Set<Type> getNewType() {
        return this.newType;
    }

    public boolean isCasted() {
        return isCasted;
    }

    public void setCasted() {
        this.isCasted = true;
    }

    public String getValue() {
        if (this.constString != null) return this.constString;
        return this.value;
    }

    public void setValue(String value) {
        this.value = value;
    }

    public void updateValue(Contr contr, String actionType) {
        if (contr != null) {
            updateValue(contr.getValue(), actionType);
        }
    }

    public void updateValue(String value, String actionType) {
        if (!Strings.isLegalContrValue(value) || value.isEmpty()) return;
        switch (actionType) {
            case "assign" -> {
                if (ContrUtil.needUpdateInMerge(this.value, value)) setValue(value);
            }
            case "append" -> {
                if ((this.value.equals(ContrUtil.sNOT_POLLUTED) || this.value.contains("new"))
                        && !value.equals(ContrUtil.sNOT_POLLUTED)) {
                    setValue(value);
                } else if (!this.value.contains(value)) {
                    String last;
                    if (this.value.contains("+")) {
                        last = this.value.substring(this.value.lastIndexOf("+") + 1);
                    } else {
                        last = this.value;
                    }
                    if (ContrUtil.needUpdateInAppend(last, value)) {
                        this.value = this.value + "+" + value;
                    }
                }
            }
        }

    }

    public void setConstString(String constString) {
        this.constString = constString;
    }

    public String getCS() {
        return constString;
    }

    public String getName() {
        return this.name;
    }

    public Pointer getOrigin() {
        return pointer;
    }

    public void merge(Contr other) {
        if (ContrUtil.needUpdateInMerge(this.value, other.getValue())) {
            setValue(other.getValue());
        }
    }

    public void addArrElement(Contr value) {
        if (value != null) {
            merge(value);
            this.arrayElements.add(value);
        }
    }

    private void addArrElement(ArrayList<Contr> arrayElements) {
        this.arrayElements.addAll(arrayElements);
    }

    public ArrayList<Contr> getArrayElements() {
        return arrayElements;
    }

    public Contr copy() {
        Contr copy = newInstance(pointer);
        copy.setValue(this.value);
        copy.setConstString(this.constString);
        if (isCasted) copy.setCasted();
        if (isNew) copy.setNew();
        if (isNew) copy.setIntra();
        if (!arrayElements.isEmpty()) copy.addArrElement(arrayElements);
        if (!value_patterns.isEmpty()) copy.setValuePatterns(value_patterns);
        return copy;
    }

    private void setValuePatterns(Set<String> valuePatterns) {
        this.value_patterns.addAll(valuePatterns);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        } else if (!(obj instanceof Contr)) {
            return false;
        }
        Contr other = (Contr) obj;
        return pointer.equals(other.pointer) &&
                value.equals(other.value);
    }

    public JClass getJClass() {
        if (type instanceof ClassType ct) {
            return ct.getJClass();
        } else {
            return null;
        }
    }

    public void setIntra() {
        this.isIntra = true;
    }

    public boolean isIntra() {
        return isNew() || isIntra;
    }

}
