import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Predicate;
import ida.sentences.SentenceState;
import ida.utils.Combinatorics;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class DevUltraCannonic {

    public String bruteForceMinimal(String s) {
        SentenceState sentence = SentenceState.parse(s);
        Set<Pair<String, Integer>> predicates = sentence.getPredicates();
        long binary = predicates.stream().filter(p -> p.getS() == 2).count();
        long unary = predicates.size() - binary;
        List<Predicate> unarySource = predicates.stream().filter(p -> p.getS() == 1).map(Predicate::create).collect(Collectors.toList());
        List<Predicate> binarySource = predicates.stream().filter(p -> p.getS() == 2).map(Predicate::create).collect(Collectors.toList());
        List<Predicate> unaryImage = IntStream.range(0, (int) unary).mapToObj(i -> Predicate.create("U" + i, 1)).collect(Collectors.toList());
        List<Predicate> binaryImage = IntStream.range(0, (int) binary).mapToObj(i -> Predicate.create("B" + i, 2)).collect(Collectors.toList());

        List<List<Predicate>> unaryPerms = Combinatorics.permutations(unaryImage);
        List<List<Predicate>> binaryPerms = Combinatorics.permutations(binaryImage);
        List<Map<Predicate, Predicate>> unaryMappings = cartesian(unarySource, unaryPerms);
        List<Map<Predicate, Predicate>> binaryMappings = cartesian(binarySource, binaryPerms);

        List<Map<Predicate, Predicate>> mappings = join(unaryMappings, binaryMappings);

        String minimal = null;
        List<List<Predicate>> negationFlips = Combinatorics.allSubsets(Sugar.listFromCollections(unaryImage, binaryImage));
        List<List<Predicate>> directionFlips = Combinatorics.allSubsets(Sugar.listFromCollections(binaryImage));
        for (Map<Predicate, Predicate> mapping : mappings) {
            SentenceState predicateRemapped = substitutePredicates(sentence, mapping);
            for (List<Predicate> directionFlip : directionFlips) {
                SentenceState directionFlipped = flipDirection(predicateRemapped, directionFlip);
                for (List<Predicate> negationFlip : negationFlips) {
                    SentenceState negationFlipped = flipNegations(directionFlipped, negationFlip);
                    String current = negationFlipped.getCannonic();
                    if (null == minimal || minimal.compareTo(current) > 0) {
                        minimal = current;
                    }
                }
            }
        }
        return minimal;
    }

    private SentenceState substitutePredicates(SentenceState sentence, Map<Predicate, Predicate> mapping) {
        List<Clause> clauses = sentence.clauses.stream()
                .map(c -> new Clause(c.getQuantifier(),
                        c.literals().stream().map(l -> new Literal(mapping.get(l.pred()).getName(), l.isNegated(), l.arguments()))
                                .collect(Collectors.toList())))
                .collect(Collectors.toList());
        return new SentenceState(clauses, null);
    }

    private SentenceState flipDirection(SentenceState sentence, List<Predicate> directionFlip) {
        List<Clause> clauses = sentence.clauses.stream()
                .map(c -> new Clause(c.getQuantifier(),
                        c.literals().stream().map(l -> {
                            if (directionFlip.contains(l.pred())) {
                                return new Literal(l.predicate(), l.isNegated(), l.get(1), l.get(0));
                            } else {
                                return l;
                            }
                        }).collect(Collectors.toList())))
                .collect(Collectors.toList());
        return new SentenceState(clauses, null);
    }

    private SentenceState flipNegations(SentenceState sentence, List<Predicate> predicate) {
        List<Clause> clauses = sentence.clauses.stream()
                .map(c -> new Clause(c.getQuantifier(),
                        c.literals().stream().map(l -> {
                            if (predicate.contains(l.pred())) {
                                return new Literal(l.predicate(), !l.isNegated(), l.arguments());
                            } else {
                                return l;
                            }
                        }).collect(Collectors.toList())))
                .collect(Collectors.toList());
        return new SentenceState(clauses, null);
    }

    private List<Map<Predicate, Predicate>> join(List<Map<Predicate, Predicate>> unaryMappings, List<Map<Predicate, Predicate>> binaryMappings) {
        if (unaryMappings.isEmpty() && binaryMappings.isEmpty()) {
            throw new IllegalStateException();
        }
        if (unaryMappings.isEmpty()) {
            unaryMappings.add(new HashMap<>());
        }
        if (binaryMappings.isEmpty()) {
            binaryMappings.add(new HashMap<>());
        }
        List<Map<Predicate, Predicate>> retVal = Sugar.list();
        for (Map<Predicate, Predicate> unaryMapping : unaryMappings) {
            for (Map<Predicate, Predicate> binaryMapping : binaryMappings) {
                retVal.add(union(unaryMapping, binaryMapping));
            }
        }
        return retVal;
    }

    private Map<Predicate, Predicate> union(Map<Predicate, Predicate> unaryMapping, Map<Predicate, Predicate> binaryMapping) {
        Map<Predicate, Predicate> retVal = new HashMap<>();
        retVal.putAll(unaryMapping);
        retVal.putAll(binaryMapping);
        return retVal;
    }

    private List<Map<Predicate, Predicate>> cartesian(List<Predicate> source, List<List<Predicate>> target) {
        return target.stream()
                .map(image -> toMapping(source, image))
                .collect(Collectors.toList());
    }

    private Map<Predicate, Predicate> toMapping(List<Predicate> source, List<Predicate> image) {
        if (source.size() != image.size()) {
            throw new IllegalStateException();
        }
        Map<Predicate, Predicate> retVal = new HashMap<>();
        for (int idx = 0; idx < source.size(); idx++) {
            retVal.put(source.get(idx), image.get(idx));
        }
        return retVal;
    }

    public static void main(String[] args) {
//        comparatorDev();
        askDev();
    }

    private static void askDev() {
        DevUltraCannonic dev = new DevUltraCannonic();
//        String query = "(V x V y U0(x) | ~U0(y) | B0(x, y) | B0(y, x)) & (V x E=1 y ~B0(x, y))";
        String query = "(V x V y U0(x) | U0(y) | B0(x, y)) & (V x V y ~B0(x, x) | U1(y))";
        String result = dev.bruteForceMinimal(query);
        System.out.println("in, out, equals");
        System.out.println(query);
        System.out.println(result);
        System.out.println(query.equals(result));
    }

    private static void comparatorDev() {

        DevUltraCannonic dev = new DevUltraCannonic();
        List<String> input = Sugar.list(
                "(V x E y B0(x, x) | U0(y)) & (V x E y U0(x) | ~B0(y, y))",
                "(V x E y B0(x, x) | U0(y)) & (E x V y ~B0(x, y) | U0(y))",
                "(V x E y B0(x, x) | U0(y)) & (V x E y B0(x, x) | ~U0(y))",
                "(E x E y B0(x, y) | ~U0(y)) & (E x E y B0(x, y) | ~U0(x))",
                "(V x E y ~B0(x, x) | ~U0(y)) & (V x E y B0(x, x) | ~U0(y))",
                "(V x V y B0(x, y) | ~B0(y, y)) & (V x V y B0(x, y) | ~B0(x, x))",
                "(V x E y B0(x, x) | ~U0(y)) & (V x E y ~B0(x, x) | ~U0(y))",

                "(E x V y B0(y, x)) & (E x V y B0(x, y) | B0(y, y))",
                "(E x V y B0(x, y) | B0(y, y)) & (E x V y B0(y, x))",
                "(E x V y B0(y, x) | B0(y, y)) & (E x V y B0(x, y))",
                "(E x V y B0(y, x)) & (E x V y B0(x, y) | U0(x))",
                "(E x V y B0(x, y) | U0(x)) & (E x V y B0(y, x))",
                "(E x V y B0(y, x) | U0(x)) & (E x V y B0(x, y))",
                "(E x V y B0(y, x)) & (V x E y B0(x, x) | U0(y))",
                "(E x V y B0(y, x)) & (V x E y B0(x, x) | ~U0(y))",
                "(V x E y B0(x, x) | U0(y)) & (E x V y B0(x, y))",
                "(V x E y B0(x, x) | U0(y)) & (E x V y B0(y, x))",
                "(E x V y ~B0(y, x)) & (V x E y ~B0(x, x) | ~U0(y))",
                "(V x E y ~B0(x, x) | ~U0(y)) & (E x V y ~B0(x, y))",
                "(V x E y ~B0(x, x) | ~U0(y)) & (E x V y ~B0(y, x))"

        );

        List<String> expectedOutputs = Sugar.list(
                "(E x V y B0(x, x) | U0(y)) & (E x V y U0(x) | ~B0(y, y))",
                "(E x V y B0(x, y) | U0(y)) & (E x V y U0(x) | ~B0(y, y))",
                "(E x V y B0(y, y) | U0(x)) & (E x V y B0(y, y) | ~U0(x))",
                "(E x E y B0(x, y) | U0(x)) & (E x E y B0(x, y) | U0(y))",
                "(E x V y B0(y, y) | U0(x)) & (E x V y U0(x) | ~B0(y, y))",
                "(V x V y B0(x, x) | ~B0(x, y)) & (V x V y B0(x, x) | ~B0(y, x))",
                "(E x V y B0(y, y) | U0(x)) & (E x V y U0(x) | ~B0(y, y))",

                "(E x V y B0(x, y) | B0(y, y)) & (E x V y B0(y, x))",
                "(E x V y B0(x, y) | B0(y, y)) & (E x V y B0(y, x))",
                "(E x V y B0(x, y) | B0(y, y)) & (E x V y B0(y, x))",
                "(E x V y B0(x, y) | U0(x)) & (E x V y B0(y, x))",
                "(E x V y B0(x, y) | U0(x)) & (E x V y B0(y, x))",
                "(E x V y B0(x, y) | U0(x)) & (E x V y B0(y, x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))",
                "(E x V y B0(x, y)) & (E x V y B0(y, y) | U0(x))"

        );

        for (int idx = 0; idx < input.size(); idx++) {
            String in = input.get(idx);
            String output = dev.bruteForceMinimal(in);
            String expectedOutput = expectedOutputs.get(idx);

            if (!output.equals(expectedOutput)) {
                System.out.println("--------------");
                System.out.println(in);
                System.out.println(expectedOutput);
                System.out.println(output);
            }
        }
    }
}
