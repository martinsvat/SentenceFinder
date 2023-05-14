package ida.sentences.caches;

import ida.ilp.logic.Term;
import ida.utils.Cache;
import ida.ilp.logic.Literal;

public class LiteralsCache extends Cache<String, Literal> {

    private static LiteralsCache cache = new LiteralsCache();

    public static LiteralsCache getInstance() {
        return cache;
    }

    public static LiteralsCache getLayer() {
        return new LiteralsCache();
    }

    public Literal get(Literal literal) {
        synchronized (this) {
            if (null == get(literal.toString())) {
                put(literal.toString(), literal);
            }
            return get(literal.toString());
        }
    }

    public Literal constructAndGet(String predicate, boolean negated, Term[] arguments) {
        String string = Literal.toString(predicate, negated, arguments, Literal.negationSign);
        synchronized (this) {
            Literal literal = get(string);
            if (null == literal) {
                literal = new Literal(predicate, negated, arguments);
                put(string, literal);
            }
            return literal;
        }
    }

    public void forget() {
        this.clear();
    }
}
