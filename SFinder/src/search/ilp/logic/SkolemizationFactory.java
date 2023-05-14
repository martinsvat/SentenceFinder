package search.ilp.logic;


public class SkolemizationFactory {

    public static final SkolemizationFactory factory = new SkolemizationFactory();

    private long counterArity0 = 0L;
    private long counterArity1 = 0L;


    public static SkolemizationFactory getInstance() {
        return factory;
    }

    public static SkolemizationFactory getOneFromStart() {
        return new SkolemizationFactory();
    }

    public String getNext(int arity) {
        if (0 == arity) {
            String result = "S" + counterArity0;
            if (counterArity0 == Long.MAX_VALUE) {
                throw new UnsupportedOperationException("run out of long values");
            }
            counterArity0++;
            return result;
        } else if (1 == arity) {
            String result = "S" + counterArity1;
            if (counterArity1 == Long.MAX_VALUE) {
                throw new UnsupportedOperationException("run out of long values");
            }
            counterArity1++;
            return result;
        }
        throw new IllegalStateException();
    }
}
