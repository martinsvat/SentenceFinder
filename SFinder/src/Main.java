import search.sentences.SentenceFinder;
import search.sentences.SentenceSetup;

public class Main {
    public static void main(String[] args) {
        SentenceSetup setup = SentenceSetup.createFromCmdValues();

        String version = "0.25.21";
        String message = "# starting search with setup:\t" + version + "\t" + setup;
        System.out.println(message);
        if (setup.statesStoring) {
            System.err.println(message);
        }

        System.out.println("# prover9 is " + ((null != setup.prover9Path && !setup.prover9Path.isBlank())  ? "used with " + setup.prover9Path : " not used, the provided path does not exist"));
        System.out.println("# cell graph script is " + ((null != setup.cellGraphPath && !setup.cellGraphPath.isBlank()) ? "used with " + setup.cellGraphPath : " not used, the provided path does not exist"));

        SentenceFinder finder = new SentenceFinder(setup);
        if (setup.continueWithSearch()) {
            finder.loadAndContinueSearch();
        } else if (!setup.seed.isBlank()) {
            finder.startFromSeed(setup.seed);
        } else {
            finder.search();
        }
    }
}