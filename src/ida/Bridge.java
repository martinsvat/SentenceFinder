package ida;

import ida.ilp.logic.Clause;
import ida.sentences.SentenceFinder;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.filters.JoiningFilter;
import ida.sentences.filters.SingleFilter;
import ida.sentences.generators.ClausesGenerator;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Quintuple;

import java.util.List;

public class Bridge {


    public static SentenceSetup constructSetup(int unaryPredicates, int binaryPredicates, int k,
                                               int maxLiteralsPerClause, int maxLiteralsPerCountingClause,
                                               int maxCountingClauses, boolean doubleCountingExists, String prover9Path) {
        return new SentenceSetup(-1, -1, maxLiteralsPerClause, unaryPredicates, binaryPredicates, 2, true, false,
                prover9Path, false, true, "", false, false, 0, true, true, true, true, true, true, k,
                maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExists, false, 30, "", true, true, -1l,
                -1l, "", true, true, true, "bfs");
    }

    public static Quintuple<SentenceFinder, List<Clause>, List<SingleFilter<SentenceState>>, List<JoiningFilter>, ClausesGenerator> prepare(SentenceSetup setup) {
        SentenceFinder sfinder = new SentenceFinder(setup);
        Pair<List<Clause>, ClausesGenerator> pair = sfinder.initForQueries();
        List<Clause> clauses = pair.getR();
        ClausesGenerator generator = pair.getS();
        return new Quintuple<>(sfinder, clauses, sfinder.getSentenceFilters(generator, setup),
                sfinder.getJoiningFilters(generator, setup), generator);
    }
}
