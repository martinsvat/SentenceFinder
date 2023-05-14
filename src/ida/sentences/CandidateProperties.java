package ida.sentences;

public class CandidateProperties {
    public boolean printOut;
    public boolean addToNextLayer;

    private static CandidateProperties trueTrue = new CandidateProperties(true, true);
    private static CandidateProperties falseFalse = new CandidateProperties(false, false);
    private static CandidateProperties trueFalse = new CandidateProperties(true, false);
    private static CandidateProperties falseTrue = new CandidateProperties(false, true);

    public CandidateProperties(boolean printOut, boolean addToNextLayer) {
        this.printOut = printOut;
        this.addToNextLayer = addToNextLayer;
    }

    public static CandidateProperties create(boolean printOut, boolean addToNextLayer) {
        if (printOut && addToNextLayer) {
            return trueTrue;
        } else if (!printOut && !addToNextLayer) {
            return falseFalse;
        } else if (printOut && !addToNextLayer) {
            return trueFalse;
        } else if (!printOut && addToNextLayer) {
            return falseTrue;
        }
        return falseFalse;
    }
}
