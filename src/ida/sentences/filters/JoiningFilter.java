package ida.sentences.filters;

import ida.ilp.logic.Clause;
import ida.sentences.SentenceState;

import java.util.function.BiPredicate;
import java.util.function.Predicate;

public class JoiningFilter implements BiPredicate<SentenceState, Clause> {

    private final String name;
    private final BiPredicate<SentenceState, Clause> predicate;

    public JoiningFilter(String name, BiPredicate<SentenceState, Clause> predicate) {
        this.name = name;
        this.predicate = predicate;
    }

    // returns true iff the clause should stay in the collection, false otherwise (i.e. it is violated, e.g. a clause is a tautology...)
    public boolean test(SentenceState alpha, Clause beta) {
        return this.predicate.test(alpha, beta);
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return getName();
    }
}
