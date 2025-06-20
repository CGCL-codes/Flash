package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import com.fasterxml.jackson.core.JsonParser;
import com.fasterxml.jackson.core.ObjectCodec;
import com.fasterxml.jackson.databind.DeserializationContext;
import com.fasterxml.jackson.databind.JsonDeserializer;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.module.SimpleModule;
import com.fasterxml.jackson.databind.node.ArrayNode;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;
import pascal.taie.config.ConfigException;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.InvokeUtils;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static pascal.taie.analysis.dataflow.analysis.methodsummary.plugin.IndexRef.ARRAY_SUFFIX;

public record PrioriKnowConfig(List<JMethod> sinks,
                               List<JMethod> transfers,
                               List<JMethod> imitates,
                               List<Object> ignores) {

    private static final Logger logger = LogManager.getLogger(PrioriKnowConfig.class);

    private static List<String> idxList = List.of("fromIdx", "recIdx", "paramIdx");

    public static PrioriKnowConfig loadConfig(String path, ClassHierarchy hierarchy, TypeSystem typeSystem) {
        ObjectMapper mapper = new ObjectMapper(new YAMLFactory());
        SimpleModule module = new SimpleModule();
        module.addDeserializer(PrioriKnowConfig.class, new Deserializer(hierarchy, typeSystem));
        mapper.registerModule(module);
        File file = new File(path);
        logger.info("Loading priori knowledge config from {}", file.getAbsolutePath());
        return loadSingle(mapper, file);
    }

    private static PrioriKnowConfig loadSingle(ObjectMapper mapper, File file) {
        try {
            return mapper.readValue(file, PrioriKnowConfig.class);
        } catch (IOException e) {
            throw new ConfigException("Failed to priori knowledge config config from " + file, e);
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Priori-Know-Config:");
        if (!sinks.isEmpty()) {
            sb.append("\nsinks:\n");
            sinks.forEach(sink ->
                    sb.append("  ").append(sink).append("\n"));
        }
        if (!transfers.isEmpty()) {
            sb.append("\ntransfers:\n");
            transfers.forEach(transfer ->
                    sb.append("  ").append(transfer).append("\n"));
        }
        if (!ignores.isEmpty()) {
            sb.append("\nignores:\n");
            ignores.forEach(ignore ->
                    sb.append("  ").append(ignore).append("\n"));
        }
        if (!imitates.isEmpty()) {
            sb.append("\nimitates:\n");
            imitates.forEach(imitate ->
                    sb.append("  ").append(imitate).append("\n"));
        }
        return sb.toString();
    }

    private static class Deserializer extends JsonDeserializer<PrioriKnowConfig> {

        private final ClassHierarchy hierarchy;

        private final TypeSystem typeSystem;

        private Deserializer(ClassHierarchy hierarchy, TypeSystem typeSystem) {
            this.hierarchy = hierarchy;
            this.typeSystem = typeSystem;
        }

        @Override
        public PrioriKnowConfig deserialize(JsonParser p, DeserializationContext ctxt) throws IOException {
            ObjectCodec oc = p.getCodec();
            JsonNode node = oc.readTree(p);
            List<JMethod> sinks = deserializeSinks(node.get("sinks"));
            List<JMethod> transfers = deserializeTransfers(node.get("transfers"));
            List<JMethod> imitates = deserializeImitates(node.get("imitates"));
            List<Object> ignores = deserializeIgnores(node.get("ignores"));
            return new PrioriKnowConfig(sinks, transfers, imitates, ignores);
        }

        private List<JMethod> deserializeSinks(JsonNode node) {
            if (node instanceof ArrayNode arrayNode) {
                List<JMethod> sinks = new ArrayList<>(arrayNode.size());
                for (JsonNode elem : arrayNode) {
                    String methodSig = elem.get("method").asText();
                    JMethod method = hierarchy.getMethod(methodSig);
                    if (method != null) {
                        ArrayNode tcArray = (ArrayNode) elem.get("index");
                        int[] TC = new int[tcArray.size()];
                        for (int i = 0; i < tcArray.size(); i++) {
                            TC[i] = InvokeUtils.toInt(tcArray.get(i).asText());
                        }
                        method.setSink(TC);
                        sinks.add(method);
                        World.get().addSink(method);
                    } else {
                        logger.warn("Cannot find sink method '{}'", methodSig);
                    }
                }
                return Collections.unmodifiableList(sinks);
            } else {
                return List.of();
            }
        }

        private List<JMethod> deserializeTransfers(JsonNode node) {
            if (node instanceof ArrayNode arrayNode) {
                List<JMethod> transfers = new ArrayList<>(arrayNode.size());
                for (JsonNode elem : arrayNode) {
                    String methodSig = elem.get("method").asText();
                    JMethod method = hierarchy.getMethod(methodSig);
                    if (method != null) {
                        IndexRef from = toIndexRef(method, elem.get("from").asText());
                        IndexRef to = toIndexRef(method, elem.get("to").asText());
                        JsonNode typeNode = elem.get("type");
                        String type;
                        if (typeNode != null) {
                            type = typeNode.asText();
                        } else {
                            Type varType = getMethodType(method, to.index());
                            type = switch (to.kind()) {
                                case VAR -> varType.getName();
                                case ARRAY -> ((ArrayType) varType).elementType().getName();
                                case FIELD -> to.field().getType().getName();
                            };
                        }
                        boolean isNewTransfer = method.getName().equals("<init>") ? true : false;
                        TaintTransfer tts = new TaintTransfer(method, from, to, type, isNewTransfer);
                        method.addTransfer(tts);
                        transfers.add(method);
                    } else {
                        logger.warn("Cannot find taint-transfer method '{}'", methodSig);
                    }
                }
                return Collections.unmodifiableList(transfers);
            } else {
                return List.of();
            }
        }

        private List<JMethod> deserializeImitates(JsonNode node) {
            if (node instanceof ArrayNode arrayNode) {
                List<JMethod> imitates = new ArrayList<>(arrayNode.size());
                for (JsonNode elem : arrayNode) {
                    String methodSig = elem.get("method").asText();
                    JMethod method = hierarchy.getMethod(methodSig);
                    if (method != null) {
                        imitates.add(method);
                        JsonNode action = elem.get("action");
                        switch (action.asText()) {
                            case "connect" -> {
                                String target = elem.get("jump").asText();
                                method.setImitatedBehavior("jump", target);
                                for (String idx : idxList) {
                                    JsonNode idxNode = elem.get(idx);
                                    if (idxNode != null) {
                                        String idxValue = Integer.toString(InvokeUtils.toInt(elem.get(idx).asText()));
                                        method.setImitatedBehavior(idx, idxValue);
                                    }
                                }
                            }
                            case "polluteRec" -> method.setImitatedBehavior("action", "polluteRec");
                            case "replace" -> method.setImitatedBehavior("action", "replace");
                            case "summary" -> {
                                ArrayNode summaryValue = (ArrayNode) elem.get("value");
                                summaryValue.forEach(value -> {
                                    String[] v = value.asText().split("->");
                                    String old = v[0].contains(":") ? v[0].substring(v[0].indexOf(":") + 1, v[0].length()) : v[0];
                                    String from = v[0].replace(old, ContrUtil.int2String(InvokeUtils.toInt(old)));
                                    boolean isRet = v[1].contains("result");
                                    String to = isRet ? "return" : ContrUtil.int2String(InvokeUtils.toInt(v[1]));
                                    from = from + (isRet ? "+" + (v[1].contains("\\+") ? v[1].split("\\+")[1] : "null") : "");
                                    method.setSummary(to, from);
                                });
                            }
                        }
                    } else {
                        logger.warn("Cannot find imitated method '{}'", methodSig);
                    }
                }
                return Collections.unmodifiableList(imitates);
            } else {
                return List.of();
            }
        }

        private List<Object> deserializeIgnores(JsonNode node) {
            if (node instanceof ArrayNode arrayNode) {
                List<Object> ignores = new ArrayList<>(arrayNode.size());
                for (JsonNode elem : arrayNode) {
                    JsonNode ignoredNode = elem.get("method");
                    if (ignoredNode != null) {
                        String methodSig = elem.get("method").asText();
                        JMethod method = hierarchy.getMethod(methodSig);
                        if (method != null) {
                            method.setIgnored();
                            ignores.add(method);
                        } else {
                            logger.warn("Cannot find ignored method '{}'", methodSig);
                        }
                    } else if (elem.get("class") != null) {
                        String classSig = elem.get("class").asText();
                        JClass jClass = hierarchy.getClass(classSig);
                        if (jClass != null) {
                            jClass.setIgnored();
                            ignores.add(jClass);
                        }
                    } else {
                        String classSig = elem.get("classMethod").asText();
                        JClass jClass = hierarchy.getClass(classSig);
                        if (jClass != null) {
                            jClass.setMethodIgnored();
                            ignores.add(jClass);
                        }
                    }
                }
                return Collections.unmodifiableList(ignores);
            } else {
                return List.of();
            }
        }
    }

    private static IndexRef toIndexRef(JMethod method, String text) {
        IndexRef.Kind kind;
        String indexStr;
        if (text.endsWith(ARRAY_SUFFIX)) {
            kind = IndexRef.Kind.ARRAY;
            indexStr = text.substring(0, text.length() - ARRAY_SUFFIX.length());
        } else if (text.contains(".")) {
            kind = IndexRef.Kind.FIELD;
            indexStr = text.substring(0, text.indexOf('.'));
        } else {
            kind = IndexRef.Kind.VAR;
            indexStr = text;
        }
        int index = InvokeUtils.toInt(indexStr);
        Type varType = getMethodType(method, index);
        JField field = null;
        switch (kind) {
            case ARRAY -> {
                if (!(varType instanceof ArrayType)) {
                    throw new ConfigException(
                            "Expected: array type, given: " + varType);
                }
            }
            case FIELD -> {
                String fieldName = text.substring(text.indexOf('.') + 1);
                if (varType instanceof ClassType classType) {
                    JClass clazz = classType.getJClass();
                    while (clazz != null) {
                        field = clazz.getDeclaredField(fieldName);
                        if (field != null) {
                            break;
                        }
                        clazz = clazz.getSuperClass();
                    }
                }
                if (field == null) {
                    throw new ConfigException("Cannot find field '"
                            + fieldName + "' in type " + varType);
                }
            }
        }
        return new IndexRef(kind, index, field);
    }

    private static Type getMethodType(JMethod method, int index) {
        return switch (index) {
            case InvokeUtils.BASE -> method.getDeclaringClass().getType();
            case InvokeUtils.RESULT -> method.getReturnType();
            default -> method.getParamType(index);
        };
    }
}
