package search.ilp.logic;

public enum TwoQuantifiers {
    EXISTS_EXISTS, FORALL_FORALL, FORALL_EXISTS, EXISTS_FORALL;

    public static boolean startsWithForall(TwoQuantifiers quantifier) {
        return FORALL_FORALL == quantifier || FORALL_EXISTS == quantifier;
    }
    public static boolean startsWithExists(TwoQuantifiers quantifier) {
        return EXISTS_FORALL == quantifier || EXISTS_EXISTS == quantifier;
    }
}
