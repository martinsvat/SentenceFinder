import ida.ilp.logic.Clause;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.SentenceState;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

public class Dev {

    private static final Matching matching = new Matching();

    public static void main(String[] args) {
        String a = "C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\cw-experiments\\strategyIsoC\\dfs.txt";
        String b = "C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\cw-experiments\\strategyIsoC\\bfs.txt";

        MultiList<IsoClauseWrapper, Pair<String, Clause>> as = load(a);
        MultiList<IsoClauseWrapper, Pair<String, Clause>> bs = load(b);

        System.out.println("a -> b");
        isInFirstNotInSecond(as, bs);
        System.out.println("b -> a");
        isInFirstNotInSecond(bs, as);

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
