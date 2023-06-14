package ida.cellGraphs;

import ida.ilp.logic.Clause;
import ida.sentences.SentenceState;
import ida.sentences.generators.ClausesGenerator;

import java.util.Collection;
import java.util.List;
import java.util.Set;

public interface CellGraphFilter {

    void incorporate(SentenceState sentence, String line);

    Collection<List<Clause>> values();

    String getPrefix();

    void setUpRedisOutput(SentenceState sentence, String redisOutput);

    void fillInCellGraphs(List<SentenceState> sentences);

    // ad those which are hidden by other techniques
    void addHiddens(Collection<SentenceState> sentences);

    // returns a collection of groups which have been identified as new ones in this batch; the ones that have been found
    // as redundant due to some earlier level are added into the skip collection during the operation
    Collection<List<SentenceState>> add(List<SentenceState> sentences, Set<SentenceState> skip, ClausesGenerator clausesGenerator);

}
