package logicStuff.theories;

import ida.ilp.logic.Clause;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.utils.Sugar;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Just a simple wrapper for theta-reduction of set of clauses.
 * <p>
 * Created by martin.svatos on 5. 12. 2017.
 */
public class NonredundantClauses {

    private final Matching matching;
    private boolean parallel = true;

    private static NonredundantClauses def;

    private NonredundantClauses() {
        this.matching = new Matching();
    }

    public Set<IsoClauseWrapper> nonredundantICW(Collection<IsoClauseWrapper> icws) {
        return theory(icws.stream().map(IsoClauseWrapper::getOriginalClause));
    }

    public List<Clause> nonredundantTheory(Collection<Clause> theory) {
        return Sugar.parallelStream(theory(theory.stream()).stream(), this.parallel)
                .map(IsoClauseWrapper::getOriginalClause)
                .collect(Collectors.toList());
    }

    public Set<IsoClauseWrapper> theory(Stream<Clause> theory) {
        List<Clause> reduced = Sugar.parallelStream(theory, this.parallel)
                .map(matching::thetaReduction).collect(Collectors.toList());
        return reduced.stream()
                .map(IsoClauseWrapper::create)
                .collect(Collectors.toSet());
    }

    public static NonredundantClauses getDefault() {
        if (null == def) {
            def = new NonredundantClauses();
        }
        return def;
    }

}
