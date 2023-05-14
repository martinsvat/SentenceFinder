package ida.ilp.logic;

import ida.utils.Cache;
import ida.utils.StringUtils;
import ida.utils.tuples.Pair;

/**
 * Created by martin.svatos on 16. 3. 2018.
 */
public class PredicateFactory {
    private static PredicateFactory ourInstance = new PredicateFactory(true);
    private final Cache<Pair<String, Integer>, Predicate> cache;
    private final boolean useCache;

    public static PredicateFactory getInstance() {
        return ourInstance;
    }

    public PredicateFactory(boolean useCache) {
        this.cache = new Cache<>();
        this.useCache = useCache;
    }

    public Predicate create(Literal literal) {
        return create(literal.predicate(), literal.arity());
    }

    public Predicate create(String name, int arity) {
        name = StringUtils.capitalize(name);
        if (useCache) {
            synchronized (cache) {
                Pair<String, Integer> key = new Pair<>(name, arity);
                if (null == cache.get(key)) {
                    cache.put(key, new Predicate(name, arity));
                }
                return cache.get(key);
            }
        }
        return new Predicate(name, arity);
    }
}
