package ida.cellGraphs;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.collections.Counters;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Quintuple;
import ida.utils.tuples.Triple;

import java.util.*;
import java.util.stream.Collectors;

public class CellSubGraph {
    /*
    cell graphs
    [g_i] i.e. list fo graphs of form
    W(1), L(x3, 4, 1), E(x1, x2, 2), C(name_i, w_i, r_ii, k, inner_ri) k is a scalar (size of the clique)


     - W/1 ... the argument is a scalar
     - L/3 ... node index, weight, weight
     - E/3 ... node index, node index, weight
     - C/5 ... node index, weight, weight, scalar, weight

     weights are shared, nodes among different g_i are not shared
     */

    private int nodes;
    private String argumentOfW1;
    private List<Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight>> c5;
    private List<Triple<Integer, Integer, SymbolicWeight>> e3;
    private List<Triple<Integer, SymbolicWeight, SymbolicWeight>> l3;
    private Set<SymbolicWeight> weights;

    public CellSubGraph(int argumentOfW1, List<Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight>> c5, List<Triple<Integer, Integer, SymbolicWeight>> e3, List<Triple<Integer, SymbolicWeight, SymbolicWeight>> l3, Collection<SymbolicWeight> weights) {
        this.c5 = c5;

        Counters<Integer> histogram = new Counters<>();
        e3.forEach(e -> {
            if (e.t.isOnlyScalar()) {
                histogram.increment(e.t.getScalar());
            }
        });
        Map.Entry<Integer, Integer> maxEntry = histogram.toMap().entrySet().stream().max(Map.Entry.<Integer, Integer>comparingByValue().thenComparing(Map.Entry.<Integer, Integer>comparingByKey())).orElseGet(() -> null);
        Integer maxKey = null == maxEntry ? null : maxEntry.getKey();
        this.argumentOfW1 = null == maxKey ? ("" + argumentOfW1) : (argumentOfW1 + "." + maxKey);

        this.e3 = null == maxKey ? e3 : e3.stream().filter(e -> !(e.t.isOnlyScalar() && e.t.getScalar() == maxKey)).collect(Collectors.toList());
        this.l3 = l3;
        this.weights = Sugar.setFromCollections(weights);

        int cMax = c5.stream().mapToInt(c -> c.r).max().orElse(0);
        int eMax = e3.stream().mapToInt(e -> Math.max(e.r, e.s)).max().orElse(0);
        int lMax = l3.stream().mapToInt(l -> l.r).max().orElse(0);
        this.nodes = Math.max(cMax, Math.max(eMax, lMax));
    }

    // canonical string for sorting g_i
    // #nodes-[sorted k from C/3]-[sorted polynomials without x_i in it]-argumentOfW/1
    public String getCannonicHash() {
        StringBuilder sb = new StringBuilder();
        sb.append(nodes).append("-");
        // sorted ks
        sb.append("[");
        c5.stream().map(q -> q.u).sorted().forEach(k -> sb.append(k).append(","));
        sb.append("]-");
        // sorted polynomials without variable naming
        sb.append("[");
        Sugar.listFromCollections(weights).stream()
                .map(SymbolicWeight::getVariablesless)
                .sorted()
                .forEach(weight -> sb.append(weight).append(","));
        sb.append("]-");
        sb.append(argumentOfW1);
        return sb.toString();
    }

    public String getMinimal(RenamingMapping mapping) {
        // again the dummy recursion but over c5, e3, and l3...
        // assuming that extendable has no nodes indexed at the very beginning, but may contain some math's variables mapping
        String minimalNext = null;
        List<Pair<String, RenamingMapping>> candidates = Sugar.list();
        // this is awful because is one big copy cat :'((
        minimalNext = selectMinimalFromL3(candidates, mapping);
        if (null == minimalNext) {
            minimalNext = selectMinimalFromC5(candidates, mapping);
        }
        if (null == minimalNext) {
            minimalNext = selectMinimalFromE3(candidates, mapping);
        }
        if (null == minimalNext) {
            return apply(mapping);
        }
        String restMinimal = null;
        RenamingMapping bestMapping = null;
        for (Pair<String, RenamingMapping> candidate : candidates) {
            String currentRest = getMinimal(candidate.s);
            if (null == restMinimal || currentRest.compareTo(restMinimal) < 0) {
                restMinimal = currentRest;
                bestMapping = candidate.s;
            }
        }
        // propagate math variable mapping
        mapping.incorporate(bestMapping);
        return restMinimal;
    }


    private String selectMinimalFromC5(List<Pair<String, RenamingMapping>> candidates, RenamingMapping mapping) {
        String currentMinimal = null;
        for (Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight> quintuple : c5) {
            if (isNotBindedC5(quintuple, mapping)) {
                Pair<String, List<RenamingMapping>> current = bindToMinimalC5(quintuple, mapping);
                if (currentMinimal == null || current.r.compareTo(currentMinimal) < 0) {
                    currentMinimal = current.r;
                    candidates.clear();
                    for (RenamingMapping renamingMapping : current.s) {
                        candidates.add(new Pair<>(current.r, renamingMapping));
                    }
                } else if (0 == current.r.compareTo(currentMinimal)) {
                    for (RenamingMapping renamingMapping : current.s) {
                        candidates.add(new Pair<>(current.r, renamingMapping));
                    }
                }
            }
        }
        return currentMinimal;
    }

    private Pair<String, List<RenamingMapping>> bindToMinimalC5(Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight> quintuple, RenamingMapping mapping) {
        RenamingMapping extended = mapping.copy();
        extended.addNodeIfNeeded(quintuple.r);
        Pair<String, List<RenamingMapping>> mins = minimal(quintuple.s, extended);
        String best = null;
        List<RenamingMapping> bestMaps1 = Sugar.list();
        for (RenamingMapping map1 : mins.s) {
            Pair<String, List<RenamingMapping>> mins1 = minimal(quintuple.t, map1);
            if (null == best || mins.r.compareTo(mins1.r) < 0) {
                best = mins.r;
                bestMaps1.clear();
                bestMaps1.addAll(mins1.s);
            }
        }

        best = null;
        List<RenamingMapping> finalBest = Sugar.list();
        for (RenamingMapping partial : bestMaps1) {
            Pair<String, List<RenamingMapping>> current = minimal(quintuple.v, partial);
            for (RenamingMapping map : current.s) {
                String currentBest = "C(" + map.toNode(quintuple.r) + "," + quintuple.s.apply(map) + "," + quintuple.t.apply(map) + "," + quintuple.u + "," + quintuple.v + ")";
                if (null == best || currentBest.compareTo(best) < 0) {
                    best = currentBest;
                    finalBest.clear();
                    finalBest.add(map);
                } else if (0 == currentBest.compareTo(best)) {
                    finalBest.add(map);
                }
            }
        }
        return new Pair<>(best, finalBest);
    }

    private Pair<String, List<RenamingMapping>> minimal(SymbolicWeight weight, RenamingMapping mapping) {
        // returns minimal possible output and all renaming mappings that produces it
        if (weight.isFullyApplicable(mapping)) {
            return new Pair<>(weight.apply(mapping), Sugar.list(mapping));
        }
        // pivot(s)
        Pair<String, List<RenamingMapping>> pair = weight.getFirstUnassignedAddition(mapping);
//        String minimal = pair.r;
        List<RenamingMapping> candidates = pair.s;

        // rest
        String rest = null;
        List<RenamingMapping> restCandidates = Sugar.list();
        for (RenamingMapping candidate : candidates) {
            Pair<String, List<RenamingMapping>> currentRest = minimal(weight, candidate);
            String current = currentRest.getR();
            if (null == rest || current.compareTo(rest) == 0) {
                rest = current;
                restCandidates.addAll(currentRest.s);
            } else if (current.compareTo(rest) < 0) {
                rest = current;
                restCandidates.clear();
                restCandidates.addAll(currentRest.s);
            }
        }
        return new Pair<>(weight.apply(restCandidates.get(0)), restCandidates);
    }

    private boolean isNotBindedC5(Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight> quintuple, RenamingMapping mapping) {
        return !mapping.isNodeIn(quintuple.r) || !quintuple.s.isFullyApplicable(mapping) || !quintuple.t.isFullyApplicable(mapping) || !quintuple.v.isFullyApplicable(mapping);
    }

    private String selectMinimalFromE3(List<Pair<String, RenamingMapping>> candidates, RenamingMapping mapping) {
        String currentMinimal = null;
        for (Triple<Integer, Integer, SymbolicWeight> triple : e3) {
            if (isNotBindedE3(triple, mapping)) {
                Pair<String, List<RenamingMapping>> current = bindToMinimalE3(triple, mapping);
                if (currentMinimal == null || current.r.compareTo(currentMinimal) < 0) {
                    currentMinimal = current.r;
                    candidates.clear();
                    for (RenamingMapping renamingMapping : current.s) {
                        candidates.add(new Pair<>(current.r, renamingMapping));
                    }
                } else if (0 == current.r.compareTo(currentMinimal)) {
                    for (RenamingMapping renamingMapping : current.s) {
                        candidates.add(new Pair<>(current.r, renamingMapping));
                    }
                }
            }
        }
        return currentMinimal;
    }

    private Pair<String, List<RenamingMapping>> bindToMinimalE3(Triple<Integer, Integer, SymbolicWeight> triple, RenamingMapping mapping) {
        RenamingMapping extended = mapping.copy();
        extended.addNodeIfNeeded(triple.r);
        extended.addNodeIfNeeded(triple.s);
        Pair<String, List<RenamingMapping>> mins = minimal(triple.t, extended);
        String best = null;
        List<RenamingMapping> minimals = Sugar.list();
        for (RenamingMapping partial : mins.s) {
            Pair<String, List<RenamingMapping>> current = minimal(triple.t, partial);
            for (RenamingMapping map : current.s) {
                String currentBest = "E(" + map.toNode(triple.r) + "," + map.toNode(triple.s) + "," + triple.t.apply(map) + ")";
                //String currentBest = "L(" + map.toNode(triple.r) + "," + map.toNode(triple.s) + "," + triple.t.apply(map) + ")";
                if (null == best || currentBest.compareTo(best) < 0) {
                    best = currentBest;
                    minimals.clear();
                    minimals.add(map);
                } else if (0 == currentBest.compareTo(best)) {
                    minimals.add(map);
                }
            }
        }
        return new Pair<>(best, minimals);
    }

    private boolean isNotBindedE3(Triple<Integer, Integer, SymbolicWeight> triple, RenamingMapping mapping) {
        return !mapping.isNodeIn(triple.r) || !mapping.isNodeIn(triple.s) || !triple.t.isFullyApplicable(mapping);
    }


    private String selectMinimalFromL3(List<Pair<String, RenamingMapping>> candidates, RenamingMapping mapping) {
        String currentMinimal = null;
        for (Triple<Integer, SymbolicWeight, SymbolicWeight> triple : l3) {
            if (isNotBindedL3(triple, mapping)) {
                Pair<String, List<RenamingMapping>> current = bindToMinimalL3(triple, mapping);
                if (currentMinimal == null || current.r.compareTo(currentMinimal) < 0) {
                    currentMinimal = current.r;
                    candidates.clear();
                    for (RenamingMapping renamingMapping : current.s) {
                        candidates.add(new Pair<>(current.r, renamingMapping));
                    }
                } else if (0 == current.r.compareTo(currentMinimal)) {
                    for (RenamingMapping renamingMapping : current.s) {
                        candidates.add(new Pair<>(current.r, renamingMapping));
                    }
                }
            }
        }
        return currentMinimal;
    }

    private Pair<String, List<RenamingMapping>> bindToMinimalL3(Triple<Integer, SymbolicWeight, SymbolicWeight> triple, RenamingMapping mapping) {
        RenamingMapping extended = mapping.copy();
        extended.addNodeIfNeeded(triple.r);
        Pair<String, List<RenamingMapping>> mins = minimal(triple.s, extended);
        String best = null;
        List<RenamingMapping> minimals = Sugar.list();
        for (RenamingMapping partial : mins.s) {
            Pair<String, List<RenamingMapping>> current = minimal(triple.t, partial);
            for (RenamingMapping map : current.s) {
//                String currentBest = "L(" + map.toNode(triple.r) + "," + triple.s.apply(map) + "," + triple.t.apply(map) + ")";
                String currentBest = "A(" + map.toNode(triple.r) + "," + triple.s.apply(map) + "," + triple.t.apply(map) + ")";
                if (null == best || currentBest.compareTo(best) < 0) {
                    best = currentBest;
                    minimals.clear();
                    minimals.add(map);
                } else if (0 == currentBest.compareTo(best)) {
                    minimals.add(map);
                }
            }
        }
        return new Pair<>(best, minimals);
    }

    private boolean isNotBindedL3(Triple<Integer, SymbolicWeight, SymbolicWeight> triple, RenamingMapping mapping) {
        return !mapping.isNodeIn(triple.r) || !triple.s.isFullyApplicable(mapping) || !triple.t.isFullyApplicable(mapping);
    }


    private String apply(RenamingMapping mapping) {
        List<String> literals = Sugar.list();
        for (Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight> quint : c5) {
            literals.add("C(" + mapping.toNode(quint.r) + "," +
                    quint.s.apply(mapping) + "," +
                    quint.t.apply(mapping) + "," +
                    quint.u + "," +
                    quint.v.apply(mapping) + ")");
        }
        for (Triple<Integer, Integer, SymbolicWeight> triple : e3) {
            literals.add("E(" + mapping.toNode(triple.r) + "," +
                    mapping.toNode(triple.s) + "," +
                    triple.t.apply(mapping) + ")");
        }
        for (Triple<Integer, SymbolicWeight, SymbolicWeight> triple : l3) {
//            literals.add("L(" + mapping.toNode(triple.r) + "," +
            literals.add("A(" + mapping.toNode(triple.r) + "," +
                    triple.s.apply(mapping) + "," +
                    triple.t.apply(mapping) + ")");
        }
        literals.add("W(" + argumentOfW1 + ")");
        Collections.sort(literals);
        return String.join(", ", literals);
    }

    public static CellSubGraph create(String sub) {
        Map<String, SymbolicWeight> cache = new HashMap<>();
        List<Quintuple<Integer, SymbolicWeight, SymbolicWeight, Integer, SymbolicWeight>> c5 = Sugar.list();
        List<Triple<Integer, Integer, SymbolicWeight>> e3 = Sugar.list();
        List<Triple<Integer, SymbolicWeight, SymbolicWeight>> l3 = Sugar.list();
        int argumentOfW1 = 0;
        for (Literal literal : Clause.parse(sub, ',', null).literals()) {
            switch (literal.predicate()) {
                case "W":
                    argumentOfW1 = Integer.parseInt(literal.get(0).name());
                    break;
                case "C":
                    c5.add(new Quintuple<>(nodeToIndex(literal.get(0).name()),
                            toWeight(literal.get(1).name(), cache),
                            toWeight(literal.get(2).name(), cache),
                            Integer.parseInt(literal.get(3).name()),
                            toWeight(literal.get(4).name(), cache)));
                    break;
                case "E":
                    e3.add(new Triple<>(nodeToIndex(literal.get(0).name()),
                            nodeToIndex(literal.get(1).name()),
                            toWeight(literal.get(2).name(), cache)));
                    break;
                case "L": // let's map this to A/3 so the weights are sorted as first as possible
                    l3.add(new Triple<>(nodeToIndex(literal.get(0).name()),
                            toWeight(literal.get(1).name(), cache),
                            toWeight(literal.get(2).name(), cache)));
                    break;
                case "G":
                    break;
                default:
                    throw new IllegalStateException("Unknown literal in cell graph: " + literal);
            }
        }

        return new CellSubGraph(argumentOfW1, c5, e3, l3, cache.values());
    }

    private static SymbolicWeight toWeight(String weight, Map<String, SymbolicWeight> cache) {
        if (!cache.containsKey(weight)) {
            cache.put(weight, SymbolicWeight.parse(weight));
        }
        return cache.get(weight);
    }

    private static Integer nodeToIndex(String xI) {
        return Integer.parseInt(xI.substring(1));
    }

    public Counters<Integer> degrees() {
        Counters<Integer> result = new Counters<>();
        for (Triple<Integer, Integer, SymbolicWeight> triple : e3) {
            result.increment(triple.r);
            result.increment(triple.s);
        }
        return result;
    }

    public String neighborhood(Integer sourceNode, Map<Integer, Integer> nodeToDegree) {
        Counters<Integer> hood = new Counters<>();
        for (Triple<Integer, Integer, SymbolicWeight> triple : e3) {
            if (triple.r.equals(sourceNode)) {
                hood.increment(nodeToDegree.get(triple.s));
            }
        }
        return hood.toMap().entrySet().stream().map(e -> e.getValue() + ":" + e.getKey()).collect(Collectors.joining("::"));
    }

    public String neighborhoodTwoLevels(Integer sourceNode, Map<Integer, Integer> nodeToDegree) {
        Map<Integer, String> firstLayer = firstNeighborhood(nodeToDegree);
        Counters<String> hood = new Counters<>();
        for (Triple<Integer, Integer, SymbolicWeight> triple : e3) {
            if (triple.r.equals(sourceNode)) {
                hood.increment(firstLayer.get(triple.s));
            }
        }
        return hood.toMap().entrySet().stream().map(e -> e.getValue() + "^" + e.getKey()).collect(Collectors.joining("^^"));
    }

    private Map<Integer, String> firstNeighborhood(Map<Integer, Integer> nodeToDegree) {
        Map<Integer, String> result = new HashMap<>();
        for (int node = 1; node <= nodes; node++) {
            result.put(node, neighborhood(node, nodeToDegree));
        }
        return result;
    }
}
