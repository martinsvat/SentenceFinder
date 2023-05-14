import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Predicate;
import ida.ilp.logic.Variable;
import ida.ilp.logic.quantifiers.Quantifier;
import ida.ilp.logic.quantifiers.QuantifiersGenerator;
import ida.sentences.SentenceFinder;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.filters.SingleFilter;
import ida.sentences.generators.ClausesGenerator;
import ida.sentences.generators.LiteralsGenerator;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class DevComparator {


    // this comes for debug purposes only!
    public static void main(String[] args) {
//        matches();
//        showDifferences();
        //thetaReduction();
        compareLogs();
    }

    private static void compareLogs() {
        List<Variable> variables = Sugar.list(Variable.construct("x"), Variable.construct("y"));
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> quantifiers = QuantifiersGenerator.generateQuantifiers(true, 0, false, false, variables);
        List<Literal> literals = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        List<String> singleThread = loadLogs(Paths.get(".", "debug", "singleThread.log"), true, "ThetaSubsumptionFilter", 3);
        List<String> tenThreads = loadLogs(Paths.get(".", "debug", "tenThreads.log"), true, "ThetaSubsumptionFilter", 3);
        Collections.sort(singleThread);
        Collections.sort(tenThreads);

        System.out.println("single");
        singleThread.forEach(System.out::println);
        System.out.println("parallel");
        tenThreads.forEach(System.out::println);
    }

    private static List<String> loadLogs(Path source, boolean ignoreTime, String reasonFilter, int sortByCannonicField) {
        try {
            return Files.lines(source).filter(line -> line.contains(";") && line.contains(reasonFilter))
                    .map(line -> {
                        String[] split = line.split(";");

                        Clause c = Clause.parseWithQuantifier(split[sortByCannonicField]);
                        return c.getCannonic() + "\t" + (ignoreTime ? line.split(";", 2)[1] : line);
                    }).collect(Collectors.toList());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void thetaReduction() {
        List<Variable> variables = Sugar.list(Variable.construct("x"), Variable.construct("y"));
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> quantifiers = QuantifiersGenerator.generateQuantifiers(true, 0, false, false, variables);
        List<Literal> literals = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        List<Clause> singleThread = loadCanonFolClauses(Paths.get(".", "debug", "singleThread.txt"));
        List<Clause> tenThreads = loadCanonFolClauses(Paths.get(".", "debug", "tenThreads.txt"));
        singleThread.sort(Comparator.comparing(Clause::getCannonic));
        tenThreads.sort(Comparator.comparing(Clause::getCannonic));

        ClausesGenerator generator = new ClausesGenerator(literals, quantifiers.r, quantifiers.s, quantifiers.t, null);
        SingleFilter<Clause> filter = generator.thetaSubsumptionFilter();
        for (int idx = 0; idx < singleThread.size(); idx++) {
            Clause alpha = singleThread.get(idx);
            Clause beta = tenThreads.get(idx);
            if (!alpha.equals(beta)) {
                throw new IllegalStateException();
            }
            boolean first = filter.test(alpha);
            boolean second = filter.test(beta);

            if (first != second) {
                System.out.println("different output for");
                System.out.println("\t" + alpha.getCannonic() + "\t" + alpha.toFOL() + "\t" + first);
                System.out.println("\t" + beta.getCannonic() + "\t" + beta.toFOL() + "\t" + second);
            }
        }
    }

    private static List<Clause> loadCanonFolClauses(Path source) {
        try {
            return Files.lines(source).filter(line -> !line.startsWith("#"))
                    .map(line -> Clause.parseWithQuantifier(line.split(";")[1]))
                    .collect(Collectors.toList());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void showDifferences() {
        List<Path> sources = Sugar.list(Paths.get("debug", "9baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_subsumption_quantifiers_trivialConstraints.txt"),
                Paths.get("debug", "10baseline_decomposable_proving_isoSent_isoNeg_permArg_reflexAtoms_subsumption_quantifiers_trivialConstraints_cell.txt"));

        DevComparator dev = new DevComparator();
//        sources.forEach(dev::splitInfos);
        dev.findFirstDifference(sources.get(0), sources.get(1));
    }

    private void findFirstDifference(Path alpha, Path beta) {
        for (int idx = 0; ; idx++) {
            String suffix = ".info" + idx;
            System.out.println("testing\t" + suffix);
            Path alphaPrime = Paths.get(alpha + suffix);
            Path betaPrime = Paths.get(beta + suffix);
            if (!alphaPrime.toFile().exists() || !betaPrime.toFile().exists()) {
                System.out.println("end since non-existences of files");
                System.out.println(alphaPrime.toFile().exists() + "\t" + alphaPrime);
                System.out.println(betaPrime.toFile().exists() + "\t" + betaPrime);
                return;
            }
            if (findDifferences(alphaPrime, betaPrime)) {
                return;
            }
        }
    }

    private boolean findDifferences(Path alpha, Path beta) {
        MultiList<String, Pair<String, String>> alphaData = loadDebugOutput(alpha);
        MultiList<String, Pair<String, String>> betaData = loadDebugOutput(beta);
        if (!alphaData.keySet().equals(betaData.keySet())) {
            System.out.println("not possible to compare, some debug print is missing");
            System.out.println("alpha\t" + String.join(", ", alphaData.keySet()));
            System.out.println("beta\t" + String.join(", ", betaData.keySet()));
            return true;
        }
        boolean diff = false;
        for (String key : alphaData.keySet()) {
            if (key.contains("after-filtering")) {
                continue;
            }
            System.out.println("key is\t" + key + "\t" + alphaData.get(key).size() + " " + betaData.get(key).size()
                    + " \t\t" + uniquesOnly(alphaData, key) + " " + uniquesOnly(betaData, key));

            if (alphaData.get(key).size() != betaData.get(key).size()) {
                System.out.println("alpha");
                System.out.println(toHist(alphaData.get(key)));
                System.out.println("beta");
                System.out.println(toHist(betaData.get(key)));
            }


            Pair<List<String>, List<String>> diffs = differenece(alphaData.get(key), betaData.get(key));
            List<String> inFirstNotInSecond = diffs.getR();
            if (!inFirstNotInSecond.isEmpty()) {
                System.out.println("is in first, not in second");
                inFirstNotInSecond.forEach(System.out::println);
            }

            List<String> inSecondNotInFirst = diffs.getS();
            if (!inSecondNotInFirst.isEmpty()) {
                System.out.println("is in second, not in first");
                inSecondNotInFirst.forEach(System.out::println);
            }
            diff |= (!inFirstNotInSecond.isEmpty() || !inSecondNotInFirst.isEmpty())
                    && !key.contains("after-filtering");
        }
        return diff;
    }

    private String toHist(List<Pair<String, String>> pairs) {
        MultiList<String, String> bag = new MultiList<>();
        for (Pair<String, String> pair : pairs) {
            bag.put(pair.getR(), pair.getS());
        }

        return bag.entrySet().stream()
//                .map(entry -> entry.getValue().size() + " " + entry.getKey() + ": " + entry.getValue().stream().sorted().collect(Collectors.joining(" ; ")))
                .map(entry -> entry.getValue().size() + " " + entry.getKey())
                .sorted()
                .collect(Collectors.joining("\n"));
    }

    private int uniquesOnly(MultiList<String, Pair<String, String>> data, String key) {
        //return data.get(key).stream().map(Pair::getR).collect(Collectors.toSet()).size();
        return data.get(key).stream().map(Pair::getS).collect(Collectors.toSet()).size();
    }

    private MultiList<String, Pair<String, String>> loadDebugOutput(Path partialOutput) {
        MultiList<String, Pair<String, String>> retVal = new MultiList<>();
        try {
            String state = null;
            for (String line : Files.lines(partialOutput).toList()) {
                if (line.endsWith("start")) {
                    state = line.substring(0, line.length() - "start".length());
                } else if (line.endsWith("end")) {
                    state = null;
                } else if (line.startsWith("# (") && null != state) {
                    String[] split = line.trim().substring(1).split(";");
                    if (split.length != 2) {
                        throw new IllegalStateException();
                    }
                    retVal.put(state, new Pair<>(split[0].trim(), split[1].trim()));
                }

            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return retVal;
    }

    private Pair<List<String>, List<String>> differenece(List<Pair<String, String>> alpha, List<Pair<String, String>> beta) {
        Set<String> alphaSet = alpha.stream().map(Pair::getR).collect(Collectors.toSet());
        Set<String> betaSet = beta.stream().map(Pair::getR).collect(Collectors.toSet());

        List<String> inAlphaNotInBeta = alpha.stream().filter(pair -> !betaSet.contains(pair.getR())).map(p -> p.getR() + " ; " + p.getS()).toList();
        List<String> inBetaNotInAlpha = beta.stream().filter(pair -> !alphaSet.contains(pair.getR())).map(p -> p.getR() + " ; " + p.getS()).toList();

        return new Pair<>(inAlphaNotInBeta, inBetaNotInAlpha);
    }

    private void splitInfos(Path path) {
        int marked = 0;
        try {
            List<String> before = Sugar.list();
            for (String line : Files.lines(path).toList()) {
                if (line.startsWith("# info")) {
                    Files.write(Paths.get(path.toString() + ".info" + marked), before);
                    before = Sugar.list();
                    marked++;
                } else {
                    before.add(line.strip());
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void matches() {
        DevComparator dev = new DevComparator();

        SentenceSetup setup = SentenceSetup.createFromCmd();
        SentenceFinder finder = new SentenceFinder(setup);

        List<SentenceState> first = dev.load(Paths.get(".", "ethalon.txt"), finder, setup);
        List<SentenceState> second = dev.load(Paths.get(".", "new.txt"), finder, setup);

        System.out.println("first cardinality\t" + first.size());
        System.out.println("second cardinality\t" + second.size());

        List<String> f1 = first.stream().map(SentenceState::getUltraCannonic).collect(Collectors.toList());
        List<String> f2 = second.stream().map(SentenceState::getUltraCannonic).collect(Collectors.toList());

        System.out.println("is in first, not in second");
        Collection<String> d1 = dev.listDifference(f1, f2);
        System.out.println(d1.size());
        d1.forEach(System.out::println);

        System.out.println("is in second, not in first");
        Collection<String> d2 = dev.listDifference(f2, f1);
        System.out.println(d2.size());
        d2.forEach(System.out::println);

        for (SentenceState sentence : second) {
            if (sentence.getUltraCannonic().equals("(E=1 x V y B0(x, y)) & (V x V y U0(x) | ~B0(y, y))")) {
                System.out.println(sentence.toFol());
            }
        }

//        dev.printCannonicalOutput(first);
//        dev.printCannonicalOutput(second);
    }

    private void printCannonicalOutput(List<SentenceState> list) {
        System.out.println("there are " + list.size() + " sentences");
        list.stream().map(SentenceState::getCannonic).sorted().forEach(System.out::println);
    }

    private <T> Collection<T> listDifference(List<T> base, List<T> minus) {
        return base.stream().filter(state -> !minus.contains(state)).collect(Collectors.toList());
//        return Sugar.setDifference(base,minus);
    }

    private List<SentenceState> load(Path path, SentenceFinder finder, SentenceSetup setup) {
        throw new IllegalStateException();
//        try {
//            return Files.lines(path)
//                    .filter(line -> !line.startsWith("#") && !line.isBlank())
//                    .map(line -> SentenceState.parse(line, finder.quantifiersToCache(), setup, finder.literalCache))
//                    .collect(Collectors.toList());
//        } catch (
//                IOException e) {
//            throw new RuntimeException(e);
//        }
    }
}
