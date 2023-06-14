package ida.cellGraphs;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Predicate;
import ida.ilp.logic.Variable;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.generators.ClausesGenerator;
import ida.sentences.generators.LiteralsGenerator;
import ida.utils.Sugar;
import ida.utils.collections.Counters;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.util.*;

public class CanonicalFilter implements CellGraphFilter {

    private final String prefix;
    private final SentenceSetup setup;
    private final Set<String> cellGraphs;

    public CanonicalFilter(SentenceSetup setup) {
        this.prefix = "CF" + setup.fastWFOMCVersion;
        this.setup = setup;
        this.cellGraphs = Sugar.set();
    }

    @Override
    public void incorporate(SentenceState sentence, String line) {
        this.cellGraphs.add(line);
    }

    @Override
    public Collection<List<Clause>> values() {
        return Sugar.list();
    }

    @Override
    public String getPrefix() {
        return prefix;
    }

    @Override
    public void setUpRedisOutput(SentenceState sentence, String redisOutput) {
        sentence.setCanonicalCellGraph(redisOutput);
    }

    @Override
    public void fillInCellGraphs(List<SentenceState> cellGraphQueue) {
        // TODO the bad design is that part of this code is duplicated with the other implementation (IsomorphicFilter)
        if (cellGraphQueue.isEmpty()) {
            return;
        }
        List<Pair<SentenceState, String>> queue = Sugar.list();
        try {
            File file = File.createTempFile("sentences", ".in");
            StringBuilder sb = new StringBuilder();
            cellGraphQueue.forEach(sentence -> sb.append(sb.isEmpty() ? "" : "\n").append(sentence.getUltraCannonic()));
            Files.write(file.toPath(), Sugar.list(sb.toString()));

            ProcessBuilder processBuilder = new ProcessBuilder();
//            if (setup.juliaSoVersion != null) { // TODO throw this unused version out :))
//                processBuilder.command("julia", "--sysimage", setup.juliaSoVersion, "--threads", "" + setup.juliaThreads, setup.cellGraphPath, file.getAbsolutePath(), "" + setup.cellTimeLimit);
//            } else {
            processBuilder.command("julia", "--threads", "" + setup.juliaThreads, setup.cellGraph, file.getAbsolutePath(), "" + setup.cellTimeLimit);

//            System.out.println("the input is in\t" + file.getAbsolutePath());
            Process process = processBuilder.start();

            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            int addedCellGraphs = 0;
            while ((line = reader.readLine()) != null) {
                if (line.startsWith("[")) {
                    String lineWithoutBracket = line.strip();
                    lineWithoutBracket = lineWithoutBracket.substring(1, lineWithoutBracket.length() - 1);
                    SentenceState sentence = cellGraphQueue.get(addedCellGraphs);
                    queue.add(new Pair<>(sentence, lineWithoutBracket));
                    addedCellGraphs++;
                } else {
                    printComment("there is an unparseable line from FastWFOMC\t" + line + " ; after parsing " + addedCellGraphs + " cell-graphs");
                }
            }
            if (cellGraphQueue.size() != addedCellGraphs) {
                System.err.println("Not every single cell-graph was returned from the query!");
                System.err.println(processBuilder.command());
                System.err.println(file.getAbsolutePath());
                System.err.println(sb);

                BufferedReader errorReader = new BufferedReader(new InputStreamReader(process.getErrorStream()));
                System.err.println("error from WFOMC");
                while ((line = errorReader.readLine()) != null) {
                    System.err.println(line);
                }
                throw new IllegalStateException();
            }
            int exitCode = process.waitFor();
            Files.deleteIfExists(file.toPath());
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        queue.parallelStream().forEach(pair -> {
            SentenceState sentence = pair.getR();
//            long start = System.nanoTime();
//            System.out.println(sentence.getUltraCannonic());
//            System.out.println(pair.s);
            String minimal = toCanonical(pair.getS());
//            System.out.println("\t" + ((System.nanoTime() - start) / 1_000_000_000));
            sentence.setCanonicalCellGraph(minimal);
            if (null != setup.redisConnection) {
                setup.redisConnection.set(prefix + sentence.getUltraCannonic(), minimal);
            }
        });
    }


    private String minimalCanonical(List<String> keys, MultiList<String, CellSubGraph> graphs, RenamingMapping
            mapping) {
        if (keys.isEmpty()) {
            return "";
        }
        String key = keys.get(0);
        List<CellSubGraph> possibleStarts = Sugar.listFromCollections(graphs.get(key));
        String minimal = null;
        List<Pair<CellSubGraph, RenamingMapping>> minimalMappings = Sugar.list();
        for (CellSubGraph start : possibleStarts) {
            RenamingMapping extendable = mapping.copyMathVariables();
            String currentMinimal = start.getMinimal(extendable);
            if (null == minimal || 0 == minimal.compareTo(currentMinimal)) {
                minimal = currentMinimal;
                minimalMappings.add(new Pair<>(start, extendable));
            } else if (currentMinimal.compareTo(minimal) < 0) {
                minimal = currentMinimal;
                minimalMappings = Sugar.list();
                minimalMappings.add(new Pair<>(start, extendable));
            }
        }

        String rest = null;
        for (Pair<CellSubGraph, RenamingMapping> pair : minimalMappings) {
            CellSubGraph currentKey = pair.getR();
            graphs.get(key).remove(currentKey);
            boolean isLast = graphs.get(key).isEmpty();
            String currentRest = minimalCanonical(isLast ? keys.subList(1, keys.size()) : keys,
                    graphs, pair.getS());
            if (null == rest || currentRest.compareTo(rest) < 0) {
                rest = currentRest;
            }
            graphs.put(key, currentKey);
        }

        return rest.isEmpty() ? minimal : (minimal + ">" + rest);
    }


    public String toCanonical(String cellGraphLine) {
        MultiList<String, CellSubGraph> graphs = new MultiList<>();
        Arrays.stream(cellGraphLine.split(";")).forEach(sub -> {
            CellSubGraph graph = CellSubGraph.create(sub);
            graphs.put(graph.getCannonicHash(), graph);
        });

        List<String> keys = Sugar.listFromCollections(graphs.keySet());
        Collections.sort(keys);
        return minimalCanonical(keys, graphs, new RenamingMapping());
    }

    private void printComment(String message) { // TODO this is not nice!
        System.out.println("# " + message);
        System.err.println("# " + message);
    }

    @Override
    public void addHiddens(Collection<SentenceState> sentences) {
        for (SentenceState sentence : sentences) {
            cellGraphs.add(sentence.getCanonicalCellGraph());
        }
    }

    @Override
    public Collection<List<SentenceState>> add(List<SentenceState> sentences, Set<SentenceState> skip, ClausesGenerator clausesGenerator) {
        MultiList<String, SentenceState> parents = new MultiList<>(); // meaning cell graph in this layer minus the one hidden using skip-collection
        for (SentenceState sentence : sentences) {
            if (skip.contains(sentence)) {
                continue;
            }

            boolean found = !cellGraphs.add(sentence.getCanonicalCellGraph());
            if (found) {
                if (parents.containsKey(sentence.getCanonicalCellGraph())) {
                    parents.put(sentence.getCanonicalCellGraph(), sentence);
                } else {
                    if (clausesGenerator.useLogger) {
                        clausesGenerator.log(sentence, null, "CellGraph-Inter");
//                        clausesGenerator.log(sentence, null, "CellGraph-Inter " + sentence.getCanonicalCellGraph());
                    }
                    skip.add(sentence); // this sentence is cell-isomorphic to something with less literals
                }
            } else {
                parents.put(sentence.getCanonicalCellGraph(), sentence);
//                if (setup.collectCellGraphs) { // this is just a dev tool
//                    this.cellGraphs.put(sentence.getCellGraph(), sentence);
            }
        }
        return parents.values();
    }


    public static CanonicalFilter create(SentenceSetup setup) {
        return new CanonicalFilter(setup);
    }

    // TODO try another tie-breaking feature to set the order of nodes uniquely at the very start to trim the branching factor (degree of a node,...)
    public static void main(String[] args) {
        SentenceSetup setup = SentenceSetup.createFromCmd();
        List<Variable> variables = Sugar.list(Variable.construct("x"), Variable.construct("y"));
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        CanonicalFilter filter = CanonicalFilter.create(setup);
        //String input = "W(1), L(n1, '-x1', 1), L(n2, '-x1', 1), L(n3, 'x1', 4), L(n4, '-x1', 4), L(n5, 'x1*x2', 1), L(n6, 'x1', 1), L(n7, 'x1*x2', 1), L(n8, -1, 4), L(n9, 1, 4), L(n10, 'x1', 1), L(n11, '-x1*x2', 1), E(n1, n2, 0), E(n2, n1, 0), E(n1, n3, 0), E(n3, n1, 0), E(n1, n4, 1), E(n4, n1, 1), E(n1, n5, 0), E(n5, n1, 0), E(n1, n6, 1), E(n6, n1, 1), E(n1, n7, 1), E(n7, n1, 1), E(n1, n8, 1), E(n8, n1, 1), E(n1, n9, 0), E(n9, n1, 0), E(n1, n10, 1), E(n10, n1, 1), E(n1, n11, 1), E(n11, n1, 1), E(n2, n3, 2), E(n3, n2, 2), E(n2, n4, 0), E(n4, n2, 0), E(n2, n5, 1), E(n5, n2, 1), E(n2, n6, 0), E(n6, n2, 0), E(n2, n7, 0), E(n7, n2, 0), E(n2, n8, 0), E(n8, n2, 0), E(n2, n9, 2), E(n9, n2, 2), E(n2, n10, 0), E(n10, n2, 0), E(n2, n11, 0), E(n11, n2, 0), E(n3, n4, 0), E(n4, n3, 0), E(n3, n5, 2), E(n5, n3, 2), E(n3, n6, 0), E(n6, n3, 0), E(n3, n7, 0), E(n7, n3, 0), E(n3, n8, 0), E(n8, n3, 0), E(n3, n9, 4), E(n9, n3, 4), E(n3, n10, 0), E(n10, n3, 0), E(n3, n11, 0), E(n11, n3, 0), E(n4, n5, 0), E(n5, n4, 0), E(n4, n6, 2), E(n6, n4, 2), E(n4, n7, 1), E(n7, n4, 1), E(n4, n8, 4), E(n8, n4, 4), E(n4, n9, 0), E(n9, n4, 0), E(n4, n10, 2), E(n10, n4, 2), E(n4, n11, 2), E(n11, n4, 2), E(n5, n6, 0), E(n6, n5, 0), E(n5, n7, 0), E(n7, n5, 0), E(n5, n8, 0), E(n8, n5, 0), E(n5, n9, 2), E(n9, n5, 2), E(n5, n10, 0), E(n10, n5, 0), E(n5, n11, 0), E(n11, n5, 0), E(n6, n7, 1), E(n7, n6, 1), E(n6, n8, 2), E(n8, n6, 2), E(n6, n9, 0), E(n9, n6, 0), E(n6, n10, 2), E(n10, n6, 2), E(n6, n11, 1), E(n11, n6, 1), E(n7, n8, 1), E(n8, n7, 1), E(n7, n9, 0), E(n9, n7, 0), E(n7, n10, 1), E(n10, n7, 1), E(n7, n11, 1), E(n11, n7, 1), E(n8, n9, 0), E(n9, n8, 0), E(n8, n10, 2), E(n10, n8, 2), E(n8, n11, 2), E(n11, n8, 2), E(n9, n10, 0), E(n10, n9, 0), E(n9, n11, 0), E(n11, n9, 0), E(n10, n11, 2), E(n11, n10, 2)";
        //String input = "W(1), L(n1, -1, 1), C(n2, 1, 4, 2, 4), L(n3, '-x1', 1), C(n4, -1, 4, 2, 4), L(n5, 1, 1), L(n6, '-x1', 1), L(n7, -1, 1), L(n8, 'x1', 1), L(n9, 1, 1), C(n10, 1, 4, 2, 4), L(n11, 1, 1), L(n12, 1, 1), L(n13, 'x1', 1), L(n14, 1, 1), L(n15, -1, 1), L(n16, -1, 1), L(n17, '-x1', 1), L(n18, -1, 1), C(n19, -1, 4, 2, 4), L(n20, 'x1', 1), E(n1, n2, 0), E(n2, n1, 0), E(n1, n3, 0), E(n3, n1, 0), E(n1, n4, 0), E(n4, n1, 0), E(n1, n5, 0), E(n5, n1, 0), E(n1, n6, 0), E(n6, n1, 0), E(n1, n7, 0), E(n7, n1, 0), E(n1, n8, 0), E(n8, n1, 0), E(n1, n9, 0), E(n9, n1, 0), E(n1, n10, 2), E(n10, n1, 2), E(n1, n11, 0), E(n11, n1, 0), E(n1, n12, 0), E(n12, n1, 0), E(n1, n13, 1), E(n13, n1, 1), E(n1, n14, 1), E(n14, n1, 1), E(n1, n15, 0), E(n15, n1, 0), E(n1, n16, 2), E(n16, n1, 2), E(n1, n17, 1), E(n17, n1, 1), E(n1, n18, 0), E(n18, n1, 0), E(n1, n19, 0), E(n19, n1, 0), E(n1, n20, 0), E(n20, n1, 0), E(n2, n3, 0), E(n3, n2, 0), E(n2, n4, 0), E(n4, n2, 0), E(n2, n5, 0), E(n5, n2, 0), E(n2, n6, 0), E(n6, n2, 0), E(n2, n7, 0), E(n7, n2, 0), E(n2, n8, 0), E(n8, n2, 0), E(n2, n9, 0), E(n9, n2, 0), E(n2, n10, 0), E(n10, n2, 0), E(n2, n11, 0), E(n11, n2, 0), E(n2, n12, 0), E(n12, n2, 0), E(n2, n13, 0), E(n13, n2, 0), E(n2, n14, 0), E(n14, n2, 0), E(n2, n15, 0), E(n15, n2, 0), E(n2, n16, 0), E(n16, n2, 0), E(n2, n17, 0), E(n17, n2, 0), E(n2, n18, 2), E(n18, n2, 2), E(n2, n19, 0), E(n19, n2, 0), E(n2, n20, 2), E(n20, n2, 2), E(n3, n4, 0), E(n4, n3, 0), E(n3, n5, 2), E(n5, n3, 2), E(n3, n6, 0), E(n6, n3, 0), E(n3, n7, 0), E(n7, n3, 0), E(n3, n8, 1), E(n8, n3, 1), E(n3, n9, 0), E(n9, n3, 0), E(n3, n10, 0), E(n10, n3, 0), E(n3, n11, 0), E(n11, n3, 0), E(n3, n12, 1), E(n12, n3, 1), E(n3, n13, 0), E(n13, n3, 0), E(n3, n14, 0), E(n14, n3, 0), E(n3, n15, 1), E(n15, n3, 1), E(n3, n16, 0), E(n16, n3, 0), E(n3, n17, 0), E(n17, n3, 0), E(n3, n18, 0), E(n18, n3, 0), E(n3, n19, 2), E(n19, n3, 2), E(n3, n20, 0), E(n20, n3, 0), E(n4, n5, 0), E(n5, n4, 0), E(n4, n6, 2), E(n6, n4, 2), E(n4, n7, 0), E(n7, n4, 0), E(n4, n8, 0), E(n8, n4, 0), E(n4, n9, 2), E(n9, n4, 2), E(n4, n10, 0), E(n10, n4, 0), E(n4, n11, 2), E(n11, n4, 2), E(n4, n12, 0), E(n12, n4, 0), E(n4, n13, 0), E(n13, n4, 0), E(n4, n14, 0), E(n14, n4, 0), E(n4, n15, 0), E(n15, n4, 0), E(n4, n16, 0), E(n16, n4, 0), E(n4, n17, 0), E(n17, n4, 0), E(n4, n18, 0), E(n18, n4, 0), E(n4, n19, 0), E(n19, n4, 0), E(n4, n20, 0), E(n20, n4, 0), E(n5, n6, 0), E(n6, n5, 0), E(n5, n7, 0), E(n7, n5, 0), E(n5, n8, 1), E(n8, n5, 1), E(n5, n9, 0), E(n9, n5, 0), E(n5, n10, 0), E(n10, n5, 0), E(n5, n11, 0), E(n11, n5, 0), E(n5, n12, 2), E(n12, n5, 2), E(n5, n13, 0), E(n13, n5, 0), E(n5, n14, 0), E(n14, n5, 0), E(n5, n15, 1), E(n15, n5, 1), E(n5, n16, 0), E(n16, n5, 0), E(n5, n17, 0), E(n17, n5, 0), E(n5, n18, 0), E(n18, n5, 0), E(n5, n19, 2), E(n19, n5, 2), E(n5, n20, 0), E(n20, n5, 0), E(n6, n7, 0), E(n7, n6, 0), E(n6, n8, 0), E(n8, n6, 0), E(n6, n9, 0), E(n9, n6, 0), E(n6, n10, 0), E(n10, n6, 0), E(n6, n11, 1), E(n11, n6, 1), E(n6, n12, 0), E(n12, n6, 0), E(n6, n13, 0), E(n13, n6, 0), E(n6, n14, 0), E(n14, n6, 0), E(n6, n15, 0), E(n15, n6, 0), E(n6, n16, 0), E(n16, n6, 0), E(n6, n17, 0), E(n17, n6, 0), E(n6, n18, 0), E(n18, n6, 0), E(n6, n19, 0), E(n19, n6, 0), E(n6, n20, 0), E(n20, n6, 0), E(n7, n8, 0), E(n8, n7, 0), E(n7, n9, 0), E(n9, n7, 0), E(n7, n10, 2), E(n10, n7, 2), E(n7, n11, 0), E(n11, n7, 0), E(n7, n12, 0), E(n12, n7, 0), E(n7, n13, 0), E(n13, n7, 0), E(n7, n14, 0), E(n14, n7, 0), E(n7, n15, 0), E(n15, n7, 0), E(n7, n16, 1), E(n16, n7, 1), E(n7, n17, 0), E(n17, n7, 0), E(n7, n18, 0), E(n18, n7, 0), E(n7, n19, 0), E(n19, n7, 0), E(n7, n20, 0), E(n20, n7, 0), E(n8, n9, 0), E(n9, n8, 0), E(n8, n10, 0), E(n10, n8, 0), E(n8, n11, 0), E(n11, n8, 0), E(n8, n12, 1), E(n12, n8, 1), E(n8, n13, 0), E(n13, n8, 0), E(n8, n14, 0), E(n14, n8, 0), E(n8, n15, 1), E(n15, n8, 1), E(n8, n16, 0), E(n16, n8, 0), E(n8, n17, 0), E(n17, n8, 0), E(n8, n18, 0), E(n18, n8, 0), E(n8, n19, 1), E(n19, n8, 1), E(n8, n20, 0), E(n20, n8, 0), E(n9, n10, 0), E(n10, n9, 0), E(n9, n11, 0), E(n11, n9, 0), E(n9, n12, 0), E(n12, n9, 0), E(n9, n13, 0), E(n13, n9, 0), E(n9, n14, 0), E(n14, n9, 0), E(n9, n15, 0), E(n15, n9, 0), E(n9, n16, 0), E(n16, n9, 0), E(n9, n17, 0), E(n17, n9, 0), E(n9, n18, 0), E(n18, n9, 0), E(n9, n19, 0), E(n19, n9, 0), E(n9, n20, 0), E(n20, n9, 0), E(n10, n11, 0), E(n11, n10, 0), E(n10, n12, 0), E(n12, n10, 0), E(n10, n13, 2), E(n13, n10, 2), E(n10, n14, 1), E(n14, n10, 1), E(n10, n15, 0), E(n15, n10, 0), E(n10, n16, 2), E(n16, n10, 2), E(n10, n17, 1), E(n17, n10, 1), E(n10, n18, 0), E(n18, n10, 0), E(n10, n19, 0), E(n19, n10, 0), E(n10, n20, 0), E(n20, n10, 0), E(n11, n12, 0), E(n12, n11, 0), E(n11, n13, 0), E(n13, n11, 0), E(n11, n14, 0), E(n14, n11, 0), E(n11, n15, 0), E(n15, n11, 0), E(n11, n16, 0), E(n16, n11, 0), E(n11, n17, 0), E(n17, n11, 0), E(n11, n18, 0), E(n18, n11, 0), E(n11, n19, 0), E(n19, n11, 0), E(n11, n20, 0), E(n20, n11, 0), E(n12, n13, 0), E(n13, n12, 0), E(n12, n14, 0), E(n14, n12, 0), E(n12, n15, 1), E(n15, n12, 1), E(n12, n16, 0), E(n16, n12, 0), E(n12, n17, 0), E(n17, n12, 0), E(n12, n18, 0), E(n18, n12, 0), E(n12, n19, 2), E(n19, n12, 2), E(n12, n20, 0), E(n20, n12, 0), E(n13, n14, 1), E(n14, n13, 1), E(n13, n15, 0), E(n15, n13, 0), E(n13, n16, 2), E(n16, n13, 2), E(n13, n17, 1), E(n17, n13, 1), E(n13, n18, 0), E(n18, n13, 0), E(n13, n19, 0), E(n19, n13, 0), E(n13, n20, 0), E(n20, n13, 0), E(n14, n15, 0), E(n15, n14, 0), E(n14, n16, 1), E(n16, n14, 1), E(n14, n17, 1), E(n17, n14, 1), E(n14, n18, 0), E(n18, n14, 0), E(n14, n19, 0), E(n19, n14, 0), E(n14, n20, 0), E(n20, n14, 0), E(n15, n16, 0), E(n16, n15, 0), E(n15, n17, 0), E(n17, n15, 0), E(n15, n18, 0), E(n18, n15, 0), E(n15, n19, 1), E(n19, n15, 1), E(n15, n20, 0), E(n20, n15, 0), E(n16, n17, 1), E(n17, n16, 1), E(n16, n18, 0), E(n18, n16, 0), E(n16, n19, 0), E(n19, n16, 0), E(n16, n20, 0), E(n20, n16, 0), E(n17, n18, 0), E(n18, n17, 0), E(n17, n19, 0), E(n19, n17, 0), E(n17, n20, 0), E(n20, n17, 0), E(n18, n19, 0), E(n19, n18, 0), E(n18, n20, 1), E(n20, n18, 1), E(n19, n20, 0), E(n20, n19, 0)";
        //String input = "W(1), L(n1, 1, 4), L(n2, 1, 1), E(n1, n2, 2); W(-1), L(n1, 1, 1)";
        String input = "W(1), L(n1, 1, 1), L(n2, 1, 4), E(n1, n2, 2); W(-1), L(n1, 1, 1)";
        long start = System.nanoTime();

//        String result = filter.toCanonical(input);
//        System.out.println("\t" + ((System.nanoTime() - start) / 1_000_000_000));
//        System.out.println(result);

        // just counting degrees
        /*
        CellSubGraph graph = CellSubGraph.create(input);
        Counters<Integer> counter = graph.degrees();
        counter.toMap().entrySet().stream().sorted(Map.Entry.<Integer, Integer>comparingByValue().thenComparing(Map.Entry.<Integer, Integer>comparingByKey()))
                .forEach(e -> System.out.println(e.getValue() + "\tn" + e.getKey() + "\t" + graph.neighborhood(e.getKey(), counter.toMap()) + "\t" + graph.neighborhoodTwoLevels(e.getKey(), counter.toMap())));
        */

        /**/
        SentenceState s1 = SentenceState.parse("(E x E y B0(x, y)) & (V x V y B0(x, x) | ~B0(x, y))", setup);
        SentenceState s2 = SentenceState.parse("(E x B0(x, x)) & (V x V y B0(x, x) | ~B0(x, y))", setup);
        filter.fillInCellGraphs(Sugar.list(s1, s2));

//        System.out.println(sentence.getUltraCannonic());
//        System.out.println(sentence.getCanonicalCellGraph());
        /**/
    }

}

