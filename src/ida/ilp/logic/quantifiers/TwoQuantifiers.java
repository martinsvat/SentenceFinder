package ida.ilp.logic.quantifiers;

public enum TwoQuantifiers {
    EXISTS, FORALL, EXISTS_EXISTS, FORALL_FORALL, FORALL_EXISTS, EXISTS_FORALL, EMPTY;

    public static boolean startsWithForall(TwoQuantifiers quantifier) {
        return FORALL_FORALL == quantifier || FORALL_EXISTS == quantifier || FORALL == quantifier;
    }
    public static boolean startsWithExists(TwoQuantifiers quantifier) {
        return EXISTS_FORALL == quantifier || EXISTS_EXISTS == quantifier || EXISTS == quantifier;
    }
}
