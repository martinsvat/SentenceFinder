import ida.sentences.SentenceFinder;
import ida.sentences.SentenceSetup;

public class Main {
    public static void main(String[] args) {
        SentenceSetup setup = SentenceSetup.createFromCmd();

        String version = "1.5.11";
        String fastWFOMCVersion = "0.1";
        setup.setFastWFOMCVersion(fastWFOMCVersion);
        String message = "# starting search with setup:\t" + version + "\t" + fastWFOMCVersion +"\t" + setup;
        System.out.println(message);
        if (setup.statesStoring) {
            System.err.println(message);
        }


        SentenceFinder finder = new SentenceFinder(setup);
        if (setup.continueWithSearch()) {
            finder.loadAndContinueSearch();
        } else if (!setup.seed.isBlank()) {
            finder.startFromSeed(setup.seed);
        } else {
            finder.generate();
        }

        setup.closeRedis();
    }
}