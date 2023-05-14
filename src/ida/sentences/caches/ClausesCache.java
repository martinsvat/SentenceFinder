package ida.sentences.caches;

import ida.utils.Cache;
import ida.ilp.logic.Clause;

public class ClausesCache extends Cache<String, Clause> {
    private static ClausesCache cache = new ClausesCache();

    public static ClausesCache getInstance() {
        return cache;
    }

    public Clause get(Clause clause) {
        synchronized (this) {
            if (null == get(clause.getCannonic())) {
                put(clause.getCannonic(), clause);
            }
        }
        return get(clause.getCannonic());
    }
}
