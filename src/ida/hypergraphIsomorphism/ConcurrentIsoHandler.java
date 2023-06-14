package ida.hypergraphIsomorphism;

import ida.ilp.logic.Clause;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.SentenceState;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

// it is not nice that this is mostly a copy of multilist
public class ConcurrentIsoHandler {

    private final ConcurrentHashMap<IsoClauseWrapper, List<Clause>> map = new ConcurrentHashMap<>();

    public ConcurrentIsoHandler() {
    }

    // public boolean contains(IsoClauseWrapper icw) {
    // returns null if there is no witness for this :)) otherwise, it returns the witness
    public SentenceState contains(IsoClauseWrapper icw) {
        List<Clause> result;
        synchronized (map) {
            result = map.get(icw);
            if (null == result) {
                result = Collections.synchronizedList(new ArrayList<>());
                result.add(icw.getOriginalClause());
                map.put(icw, result);
                return null;
            }
        }
        synchronized (result) {
            Matching m = new Matching();
            for (Clause clause : result) {
                if (m.isomorphism(clause, icw.getOriginalClause())) {
                    return clause.getSentence();
                }
            }
            result.add(icw.getOriginalClause());
            return null;
        }
    }


    public Set<Map.Entry<IsoClauseWrapper, List<Clause>>> entrySet() {
        return this.map.entrySet();
    }
}
