import ida.ilp.logic.Clause;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.SentenceState;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;
import jdk.jfr.Timespan;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.concurrent.TimeUnit;

public class Dev {

    private static final Matching matching = new Matching();

    public static void main(String[] args) throws IOException {
        /*String a = "C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\cw-experiments\\strategyIsoC\\dfs.txt";
        String b = "C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\cw-experiments\\strategyIsoC\\bfs.txt";

        MultiList<IsoClauseWrapper, Pair<String, Clause>> as = load(a);
        MultiList<IsoClauseWrapper, Pair<String, Clause>> bs = load(b);

        System.out.println("a -> b");
        isInFirstNotInSecond(as, bs);
        System.out.println("b -> a");
        isInFirstNotInSecond(bs, as);
        */

        subProcessTimeOut();

    }

    private static void subProcessTimeOut() throws IOException {
//        Path source = Paths.get("sentences3901645161121027589.in");
        Path source = Paths.get("sentences.in");
        List<String> sentences = Files.lines(source).filter(l -> !l.isBlank()).toList();
        System.out.println("threads\t" + System.getProperty("java.util.concurrent.ForkJoinPool.common.parallelism"));

        sentences.parallelStream().forEach(sentence -> {
            File file = null;
            try {
                file = File.createTempFile("sentences-t", ".in");
                StringBuilder sb = new StringBuilder();
                sb.append(sentence);
                Files.write(file.toPath(), Sugar.list(sb.toString()));

                ProcessBuilder processBuilder = new ProcessBuilder();
                processBuilder.command("julia", "--threads", "1", "C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\SFinder\\julia\\sample_multithreaded_unskolemized.jl",
                        file.getAbsolutePath(), "" + 0);

//            System.out.println("the input is in\t" + file.getAbsolutePath());
                Process process = processBuilder.start();

                if (process.waitFor(30l, TimeUnit.SECONDS)) {

                    BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
                    String line;
                    int addedCellGraphs = 0;
                    while ((line = reader.readLine()) != null) {
                        if (line.startsWith("[")) {
                            String wholeLine = line;
                            // parsing a cell-graph
                            line = line.substring(1, line.length() - 1);
//                        Clause cellGraph = parseCellGraph(cellGraphQueue, processBuilder, line, addedCellGraphs, wholeLine);
//                        SentenceState sentence = cellGraphQueue.get(addedCellGraphs);
//                        sentence.setCellGraph(cellGraph);
//                        if (null != setup.redisConnection) {
//                            setup.redisConnection.set(prefix + sentence.getUltraCannonic(), cellGraph.toString());
//                        }
                            addedCellGraphs++;
                            System.out.println(sentence + "\t" + line.trim());
                        } else {
                            System.out.println("there is an unparseable line from FastWFOMC\t" + line + " ; after parsing " + addedCellGraphs + " cell-graphs");
                        }
                    }
                } else {
                    process.destroy();
//                    System.out.println("X\t" + sentence);
                }
                Files.deleteIfExists(file.toPath());
            } catch (IOException e) {
                throw new RuntimeException(e);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }

        });

    }

    private static void isInFirstNotInSecond(MultiList<IsoClauseWrapper, Pair<String, Clause>> first, MultiList<IsoClauseWrapper, Pair<String, Clause>> second) {
        first.keySet().forEach(key ->
                first.get(key).forEach(pair -> {
                    if (!isThere(key, pair.s, second)) {
                        System.out.println("misses\t" + pair.r);
                    }
                })
        );
    }

    private static boolean isThere(IsoClauseWrapper key, Clause s, MultiList<IsoClauseWrapper, Pair<String, Clause>> second) {
        List<Pair<String, Clause>> possible = second.get(key);
        if (null == possible) {
            return false;
        }
        for (Pair<String, Clause> pair : possible) {
            if (matching.isomorphism(s, pair.s)) {
                return true;
            }
        }
        return false;
    }

    private static MultiList<IsoClauseWrapper, Pair<String, Clause>> load(String a) {
        MultiList<IsoClauseWrapper, Pair<String, Clause>> retVal = new MultiList<>();
        try {
            Files.lines(Paths.get(a)).filter(line -> !line.startsWith("#") && line.contains(";"))
                    .forEach(line -> {
                        String[] split = line.split(";");
                        Clause cellGraph = Clause.parse(split[1], ',', null);
                        String sentence = split[0];
                        retVal.put(IsoClauseWrapper.create(cellGraph), new Pair<>(sentence, cellGraph));
                    });
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return retVal;
    }
}
