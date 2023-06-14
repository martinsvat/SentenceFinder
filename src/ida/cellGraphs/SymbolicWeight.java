package ida.cellGraphs;

import ida.utils.Combinatorics;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;

import java.util.*;
import java.util.stream.Collectors;

public class SymbolicWeight {

    //  'x1^2 + 2*x1^1*x2^2 + 1' ... it's sorted anyway in decreasing order
    // or a scalar

    private List<Pair<String, List<Pair<String, Integer>>>> terms; // <multiplier, [<variable, exponent>]>

    public SymbolicWeight(List<Pair<String, List<Pair<String, Integer>>>> terms) {
        this.terms = terms;
    }

    public String getVariablesless() {
        return terms.stream().map(pair -> pair.s + ",," + pair.getS().stream().map(Pair::getS)
                        .sorted()
                        .map(s -> s + "")
                        .collect(Collectors.joining(",")))
                .sorted()
                .collect(Collectors.joining("+"));
    }


    public static SymbolicWeight parse(String expression) {
        List<Pair<String, List<Pair<String, Integer>>>> terms = Sugar.list();
        if (expression.startsWith("'")) {
            expression = expression.substring(1, expression.length() - 1); // removing first and last '...'
        }

        while (!expression.isEmpty()) { // copy & cat from parseSymbolicWeight :))
            boolean startsWithMinus = expression.startsWith("-");
            int nextPlus = expression.indexOf("+");
            int nextMinus = startsWithMinus ? expression.indexOf("-", 1) : expression.indexOf("-");
            int end = 0;
            if (-1 == nextPlus && -1 == nextMinus) {
                end = expression.length();
            } else if (-1 == nextPlus) {
                end = nextMinus;
            } else if (-1 == nextMinus) {
                end = nextPlus;
            } else {
                end = Math.min(nextPlus, nextMinus);
            }

            String part = expression.substring(startsWithMinus ? 1 : 0, end);
            expression = expression.substring(end);

            List<Pair<String, Integer>> factors = Sugar.list();
            int multiplier = startsWithMinus ? -1 : 1;
            for (String factor : part.split("\\*")) {
                if (factor.contains("x")) {
                    String[] exponentSplit = factor.split("\\^");
                    factors.add(new Pair<>(exponentSplit[0], exponentSplit.length > 1 ? Integer.parseInt(exponentSplit[1]) : 1));
                } else { // scalar
                    multiplier *= Integer.parseInt(factor);
                }
            }
            terms.add(new Pair<>("" + multiplier, factors));

            if (expression.startsWith("+")) {
                expression = expression.substring(1);
            }
        }

        return new SymbolicWeight(terms);
    }

    public String apply(RenamingMapping mapping) {
        return terms.stream().map(p -> p.getR() +
                        (p.s.isEmpty() ? "" :
                                ("*" + p.getS().stream()
                                        .map(factor -> mapping.toMath(factor.getR()) + "^" + factor.getS())
                                        .sorted()
                                        .collect(Collectors.joining("*")))))
                .sorted()
                .collect(Collectors.joining("+"));
    }

    public boolean isFullyApplicable(RenamingMapping mapping) {
        for (Pair<String, List<Pair<String, Integer>>> term : terms) {
            for (Pair<String, Integer> factor : term.s) {
                if (!mapping.isVariableIn(factor.getR())) {
                    return false;
                }
            }
        }
        return true;
    }

    public Pair<String, List<RenamingMapping>> getFirstUnassignedAddition(RenamingMapping mapping) {
        String multiplier = null;
        String minimal = null;
        String hash = null;
        List<RenamingMapping> retVal = Sugar.list();
        for (Pair<String, List<Pair<String, Integer>>> term : terms) {
            if ((null != multiplier && multiplier.compareTo(term.r) < 0) || isFullyApplicable(term, mapping)) {
                continue;
            }
            String currentHash = toHashLike(term.r, term.s);
            if (null != hash && hash.compareTo(currentHash) < 0) {
                continue;
            }
            Map<Integer, List<String>> freeVariables = selectUnassignedVariables(term.s, mapping);
            List<RenamingMapping> possibleMappings = Sugar.list(mapping);
            List<Integer> keys = Sugar.listFromCollections(freeVariables.keySet());
            Collections.sort(keys);
            for (Integer key : keys) {
                List<RenamingMapping> nextPossibleMappings = Sugar.list();
                List<String> variables = freeVariables.get(key);
                List<List<String>> permutations = 1 == variables.size() ? Sugar.list(variables) : Combinatorics.permutations(variables);
                for (List<String> permutation : permutations) {
                    for (RenamingMapping possibleMapping : possibleMappings) {
                        possibleMapping = possibleMapping.copy();
                        for (String variable : permutation) {
                            possibleMapping.addMathVariableImage(variable);
                        }
                        nextPossibleMappings.add(possibleMapping);
                    }
                }
                possibleMappings = nextPossibleMappings;
            }
            for (RenamingMapping possibleMapping : possibleMappings) {
                String currentMinimal = apply(term.r, term.s, possibleMapping);
                if (null == minimal || currentMinimal.compareTo(minimal) < 0) {
                    hash = currentHash;
                    minimal = currentMinimal;
                    retVal.clear();
                    retVal.add(possibleMapping);
                } else if (currentMinimal.compareTo(minimal) == 0) {
                    retVal.add(possibleMapping);
                }
            }
        }
        return new Pair<>(minimal, retVal);
    }

    private String apply(String multiplier, List<Pair<String, Integer>> factors, RenamingMapping mapping) {
        return multiplier + "*" + factors.stream().map(pair -> mapping.toMath(pair.r) + "^" + pair.s).sorted().collect(Collectors.joining("*"));
    }

    private Map<Integer, List<String>> selectUnassignedVariables(List<Pair<String, Integer>> factors, RenamingMapping mapping) {
        Map<Integer, List<String>> retVal = new HashMap<>();
        for (Pair<String, Integer> factor : factors) {
            if (!mapping.containsMathVariableMapping(factor.r)) {
                if (!retVal.containsKey(factor.s)) {
                    retVal.put(factor.s, Sugar.list());
                }
                retVal.get(factor.s).add(factor.r);
            }
        }
        return retVal;
    }

    private String toHashLike(String multiplier, List<Pair<String, Integer>> factors) {
        return multiplier + "^" + factors.stream().sorted(Comparator.comparing(Pair::getS)).map(i -> i + "").collect(Collectors.joining("^"));
    }

    private boolean isFullyApplicable(Pair<String, List<Pair<String, Integer>>> term, RenamingMapping mapping) {
        for (Pair<String, Integer> pair : term.s) {
            if (!mapping.containsMathVariableMapping(pair.r)) {
                return false;
            }
        }
        return true;
    }

    public boolean isOnlyScalar() {
        return terms.size() == 1 && terms.get(0).s.isEmpty();
    }

    public int getScalar() { // returns the first multiplicative constant, i.e. the scalar if the weith is scalar
        return Integer.parseInt(terms.get(0).r);
    }
}
