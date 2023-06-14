package ida.cellGraphs;

import java.util.HashMap;

public class RenamingMapping {


    private final HashMap<Integer, String> nodes;
    private final HashMap<String, String> mathVariables;

    public RenamingMapping() {
        this(new HashMap<>(), new HashMap<>());
    }

    public RenamingMapping(HashMap<Integer, String> nodes, HashMap<String, String> mathVariables) {
        this.nodes = nodes;
        this.mathVariables = mathVariables;
    }

    public RenamingMapping copyMathVariables() {
        return new RenamingMapping(new HashMap<>(), new HashMap<>(this.mathVariables));
    }

    public boolean isNodesMappingEmpty() {
        return nodes.isEmpty();
    }

    public String toNode(Integer node) {
        String result = nodes.get(node);
//        if (null == result) {
//            result = "^";
//        }
        return result;
    }

    public String toMath(String variable) {
        String result = mathVariables.get(variable);
//        if (null == result) {
//            result = "^";
//        }
        return result;

    }

    public boolean isNodeIn(Integer node) {
        return nodes.containsKey(node);
    }

    public boolean isVariableIn(String variable) {
        return mathVariables.containsKey(variable);
    }

    public RenamingMapping copy() {
        return new RenamingMapping(new HashMap<>(nodes), new HashMap<>(mathVariables));
    }

    public void incorporate(RenamingMapping mapping) {
        this.nodes.putAll(mapping.nodes);
        this.mathVariables.putAll(mapping.mathVariables);
    }

    public void addNodeIfNeeded(Integer node) {
        if (!isNodeIn(node)) {
            nodes.put(node, nodes.size() + "");
        }
    }

    public boolean containsMathVariableMapping(String variable) {
        return mathVariables.containsKey(variable);
    }

    public void addMathVariableImage(String variable) {
        if (mathVariables.containsKey(variable)) {
            return;
        }
        mathVariables.put(variable, mathVariables.size() + "");
    }
}
