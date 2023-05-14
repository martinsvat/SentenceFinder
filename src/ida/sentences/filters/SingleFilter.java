package ida.sentences.filters;

import ida.ilp.logic.Clause;

import java.util.function.Predicate;

public class SingleFilter<T> implements Predicate<T> {

    private final String name;
    private final Predicate<T> predicate;

    public SingleFilter(String name, Predicate<T> predicate) {
        this.name = name;
        this.predicate = predicate;
    }

    // returns true iff the clause should stay in the collection, false otherwise (i.e. it is violated, e.g. a clause is a tautology...)
    public boolean test(T t) {
        return this.predicate.test(t);
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return getName();
    }
}
