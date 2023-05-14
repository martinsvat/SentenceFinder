package ida.sentences.caches;

import ida.ilp.logic.Predicate;

import java.util.Set;

public class PredicatesCache {
    private static Cache<Set<Predicate>> cache = new Cache<>();

    public static Cache<Set<Predicate>> getInstance() {
        return cache;
    }
}
