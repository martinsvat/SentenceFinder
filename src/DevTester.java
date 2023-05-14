import ida.ilp.logic.Predicate;
import ida.ilp.logic.Variable;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.generators.LiteralsGenerator;
import ida.utils.Sugar;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.IntStream;

public class DevTester {

    public static void main(String[] args) {
        List<Variable> variables = Sugar.list(Variable.construct("x"), Variable.construct("y"));
        List<Predicate> predicates = Sugar.list(Predicate.create("B0", 2),
                Predicate.create("U0", 1));
        SentenceSetup setup = new SentenceSetup(2);
        setup = setup.setPredicates(predicates);
        DevTester dev = new DevTester();
        LiteralsGenerator.generate(variables, predicates);

        // (V x V y B0(x, x) | U0(x) | U0(y) | ~B0(x, y)) & (V x V y B0(x, x) | U0(y) | ~B0(y, y))
        // tzn v cell-graph to neni protoze to je proriznute necim jinym, ale to dava teda jine spektrum jo? zjistit com je to proriznute

        //dev.checkPresence(setup, Paths.get("C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\cw-experiments\\run2\\fo52-order2-5-2-10-1-1-0\\10baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_subsumption_quantifiers_trivialConstraints_cell.txt"));
        dev.scanSentence("(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~B0(y, x))", setup);

//        streamEnds();
    }

    private static void streamEnds() {
        System.out.println(System.getProperty("java.util.concurrent.ForkJoinPool.common.parallelism", ""));
        Thread.setDefaultUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
            @Override
            public void uncaughtException(Thread t, Throwable e) {
                System.out.println("there is a bug, bug bug bug!!!!");
                System.out.println(t);
                e.printStackTrace();
                System.exit(-1);
            }
        });
        IntStream.range(0, 100).parallel().forEach(i -> {
            if (i % 10 == 1) {
                System.out.println(i);
            } else if (i == 50) {
                //System.out.println(0 / 0);
                throw new IllegalStateException();
            }
        });
    }

    private void checkPresence(SentenceSetup setup, Path path) {
        List<String> sentences = Sugar.list(
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y ~B0(x, y) | U0(y) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | U0(y) | ~B0(x, y) | B0(y, x))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, y)) & (E x V y ~B0(y, x) | B0(y, y))",
                "(E x V y B0(x, y) | ~B0(y, y)) & (E x V y ~B0(x, x) | U0(y) | B0(y, x) | ~B0(y, y))",
                "(E x V y U0(x) | B0(x, y) | ~B0(y, x)) & (E x V y ~B0(x, y) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y ~B0(x, x) | B0(x, y) | B0(y, x))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y ~B0(x, y) | U0(y) | B0(y, x) | ~B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y B0(x, x) | U0(y) | B0(x, y) | ~B0(y, x))",
                "(E x V y U0(x) | U0(y) | B0(x, y) | ~B0(y, y)) & (E x V y ~B0(x, y) | U0(y) | ~B0(y, x))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y B0(x, x) | U0(y) | B0(x, y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y ~B0(x, x) | U0(y) | B0(x, y) | ~B0(y, x))",
                "(E x V y U0(x) | B0(x, y) | ~B0(x, x) | B0(y, x)) & (E x V y ~B0(x, y) | ~B0(y, x) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x) | ~B0(y, y)) & (E x V y B0(x, x) | ~B0(x, y))",
                "(E x V y U0(x) | B0(x, y) | B0(y, x)) & (E x V y B0(x, y) | ~U0(y) | ~B0(y, x) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x) | B0(y, y)) & (E x V y B0(x, x) | ~B0(x, y) | ~B0(y, x))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~U0(y) | ~B0(y, x))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~U0(y) | ~B0(x, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y ~B0(x, x) | ~B0(x, y) | B0(y, x))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y ~B0(x, x) | ~U0(y) | B0(x, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~B0(y, x))",
                "(E x V y U0(x) | B0(x, y) | ~B0(y, y)) & (E x V y ~B0(x, y) | B0(y, y))",
                "(E x V y U0(x) | B0(x, y) | ~B0(y, x)) & (E x V y B0(x, y) | ~B0(y, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y ~B0(x, x) | B0(x, y) | ~B0(y, x))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~B0(x, y) | ~B0(y, x))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | B0(x, y) | ~B0(y, x))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~B0(x, y) | B0(y, x))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y ~B0(x, x) | ~U0(y) | ~B0(x, y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (E x V y B0(x, x) | ~B0(x, y))",
                "(E x V y U0(x) | B0(x, y) | ~B0(y, x)) & (E x V y ~B0(x, y) | U0(y) | B0(y, y))",
                "(E x V y U0(x) | B0(x, y) | ~B0(y, y)) & (E x V y ~B0(y, x) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y B0(x, x) | ~B0(x, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y ~B0(x, x) | B0(x, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y ~B0(x, x) | ~U0(y) | B0(y, x))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x) | B0(y, y)) & (E x V y ~B0(x, y) | U0(y))",
                "(E x V y B0(x, y) | ~B0(y, x) | B0(y, y)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y U0(x) | B0(x, y) | B0(y, x)) & (E x V y ~B0(x, y) | B0(y, y))",
                "(E x V y U0(x) | B0(x, y) | ~B0(y, y)) & (E x V y B0(y, x) | ~B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x) | ~B0(y, y)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x) | ~B0(y, y)) & (V x E y U0(x) | ~B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x) | ~B0(y, y)) & (V x E y B0(x, x) | U0(y))",
                "(V x E y U0(x) | ~B0(y, y)) & (E x V y U0(x) | B0(x, y) | B0(y, x) | ~B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x) | B0(y, y)) & (V x E y B0(x, x) | ~U0(y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x) | B0(y, y)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x) | ~B0(y, y)) & (V x E y B0(x, x) | ~U0(y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (V x E y U0(x) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, y)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, y)) & (V x E y U0(x) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, y)) & (V x E y U0(x) | ~B0(y, y))",
                "(V x V y U0(x) | U0(y) | B0(x, y) | ~B0(x, x) | ~B0(y, y)) & (E x V y ~B0(x, y) | ~B0(y, x) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (V x E y B0(x, x) | ~U0(y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x)) & (V x E y B0(x, x) | U0(y))",
                "(V x V y U0(x) | U0(y) | B0(x, y) | ~B0(y, x)) & (V x V y B0(x, x) | ~B0(x, y) | B0(y, y))",
                "(V x V y U0(x) | ~U0(y) | B0(x, y) | B0(x, x)) & (V x V y B0(x, x) | ~B0(x, y) | B0(y, y))",
                "(E x V y B0(x, y) | U0(y)) & (V x E y B0(x, x) | ~U0(y))",
                "(E x V y B0(x, y) | ~B0(y, x)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y B0(x, y) | U0(y) | B0(y, x)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y B0(x, y) | U0(y) | ~B0(y, x)) & (V x E y B0(x, x) | ~U0(y))",
                "(V x V y U0(x) | B0(x, y) | B0(y, x) | ~B0(y, y)) & (V x V y ~U0(x) | ~B0(x, y) | ~B0(y, x) | B0(y, y))"
        );

        for (String s : sentences) {
            SentenceState sentence = SentenceState.parse(s, setup);
            if (!isIn(sentence, path)) {
                System.out.println("this is not in the file provided\n\t" + s + "\n\t" + sentence.getUltraCannonic());
            }

        }
    }

    private boolean isIn(SentenceState sentence, Path path) {
        String target = sentence.getUltraCannonic().trim();
        try {
            return Files.lines(path).filter(line -> !line.startsWith("#"))
                    .anyMatch(line -> line.trim().equals(target));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void printUltraCannon(String s, SentenceSetup setup) {
        SentenceState sentence = SentenceState.parse(s, setup);
        String ultraCannonic = sentence.getUltraCannonic();
        System.out.println(ultraCannonic);
    }

    private void scanSentence(String s, SentenceSetup setup) {
        SentenceState sentence = SentenceState.parse(s, setup);

        String ultraCannonic = sentence.getUltraCannonic();
        System.out.println(s);
        System.out.println(sentence.toFol());
        System.out.println(ultraCannonic);
        System.out.println("\t" + ultraCannonic.equals(s));


    }
}
