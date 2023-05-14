package ida.sentences.caches;

import ida.ilp.logic.Variable;

import java.util.Set;

public class VariablesCache {
    private static Cache<Set<Variable>> cache = new Cache<>();

    public static Cache<Set<Variable>> getInstance() {
        return cache;
    }

}
