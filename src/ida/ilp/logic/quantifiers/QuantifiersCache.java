package ida.ilp.logic.quantifiers;

import ida.utils.Cache;

public class QuantifiersCache extends Cache<String, Quantifier> {
    private static QuantifiersCache cache = new QuantifiersCache();

    public static QuantifiersCache getInstance() {
        return cache;
    }

    public Quantifier get(Quantifier quantifier) {
        if (null == get(quantifier.getPrefix())) {
            put(quantifier.getPrefix(), quantifier);
        }
        return get(quantifier.getPrefix());
    }
}
