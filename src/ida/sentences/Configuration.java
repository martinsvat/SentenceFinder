package ida.sentences;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Predicate;

import java.util.List;
import java.util.Map;
import java.util.Set;

public class Configuration {

    public final List<Predicate> freeUnary;
    public final List<Predicate> freeBinary;
    public final Map<Predicate, Predicate> mapping;
    public final Set<Predicate> negationSwap;
    public final Set<Predicate> directionSwap;
    public final Clause clause;

    public Configuration(List<Predicate> freeUnary, List<Predicate> freeBinary, Map<Predicate, Predicate> mapping, Set<Predicate> negationSwap, Set<Predicate> directionSwap, Clause clause) {
        this.freeUnary = freeUnary;
        this.freeBinary = freeBinary;
        this.mapping = mapping;
        this.negationSwap = negationSwap;
        this.directionSwap = directionSwap;
        this.clause = clause;
    }

    public Clause getClause() {
        return this.clause;
    }
}
