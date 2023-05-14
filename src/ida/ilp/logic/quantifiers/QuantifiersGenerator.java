package ida.ilp.logic.quantifiers;

import ida.ilp.logic.Variable;
import ida.utils.Cache;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class QuantifiersGenerator {

    public static Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> generateQuantifiers(boolean generateExistsQuantifiers, int maxK, boolean generateCountingQuantifiers, boolean doubleCountingExist, List<Variable> variables) {
        Cache<String, Quantifier> cache = QuantifiersCache.getInstance();
        List<Quantifier> quantifiers = Sugar.list();
        MultiList<Quantifier, Quantifier> quantifierSuccessors = new MultiList<>();
        Map<Quantifier, Quantifier> quantifiersMirrors = new HashMap<>();

        if (generateExistsQuantifiers) {
            Quantifier forall = Quantifier.create(TwoQuantifiers.FORALL, variables);
            Quantifier exists = Quantifier.create(TwoQuantifiers.EXISTS, variables);
            Quantifier forallForall = Quantifier.create(TwoQuantifiers.FORALL_FORALL, variables);
            Quantifier forallExists = Quantifier.create(TwoQuantifiers.FORALL_EXISTS, variables);
            Quantifier existsForall = Quantifier.create(TwoQuantifiers.EXISTS_FORALL, variables);
            Quantifier existsExists = Quantifier.create(TwoQuantifiers.EXISTS_EXISTS, variables);

            quantifierSuccessors.put(forall, forallForall);
            quantifierSuccessors.put(forall, forallExists);
            quantifierSuccessors.put(exists, existsForall);
            quantifierSuccessors.put(exists, existsExists);

            quantifiersMirrors.put(forallExists, existsForall);
            quantifiersMirrors.put(existsForall, forallExists);

            quantifiers.addAll(Sugar.list(forall, exists, forallForall, forallExists, existsForall, existsExists));

            if (generateCountingQuantifiers) { // don't generate these if they are not gonna be used at all
                List<Pair<TwoQuantifiers, Integer>> counting = Sugar.list(
                        new Pair<>(TwoQuantifiers.EXISTS, 0),
                        new Pair<>(TwoQuantifiers.EXISTS_FORALL, 0),
                        new Pair<>(TwoQuantifiers.FORALL_EXISTS, 1));
                if (doubleCountingExist) {
                    counting.add(new Pair<>(TwoQuantifiers.EXISTS_EXISTS, 0));
                    counting.add(new Pair<>(TwoQuantifiers.EXISTS_EXISTS, 1));
                }
                Quantifier[] countingExists = new Quantifier[maxK];
                Quantifier[] flip = new Quantifier[maxK];

                // here, we generate only single-counting variable for a two-variable quantifier
                for (Pair<TwoQuantifiers, Integer> pair : counting) {
                    TwoQuantifiers quantifier = pair.getR();
                    int countingVariableIndex = pair.getS();
                    Quantifier previous = TwoQuantifiers.startsWithForall(quantifier) ? forall : exists;
                    for (int k = 1; k <= maxK; k++) {
                        Quantifier countingQuantifier = 0 == countingVariableIndex ? Quantifier.create(quantifier, variables, k, -1) : Quantifier.create(quantifier, variables, -1, k);
//                        System.out.println(countingQuantifier);
//                        if("V x E=1 y".equals(countingQuantifier.toString())){
//                            System.out.println("debug here!");
//                        }

                        if (0 == countingVariableIndex) {
                            if (TwoQuantifiers.EXISTS == quantifier) {
                                previous = null;
                                countingExists[k - 1] = countingQuantifier;
                            } else {
                                previous = countingExists[k - 1];
                            }
                        }
                        quantifiers.add(countingQuantifier);
                        if (null != previous) {
                            quantifierSuccessors.put(previous, countingQuantifier);
                        }

                        if (2 == countingQuantifier.numberOfUsedVariables) {
                            if (0 == countingVariableIndex) {
                                flip[k - 1] = countingQuantifier;
                            } else {
                                Quantifier flipped = flip[k - 1];
                                quantifiersMirrors.put(flipped, countingQuantifier);
                                quantifiersMirrors.put(countingQuantifier, flipped);
                            }
                        }
                    }
                }
                if (doubleCountingExist) {
                    Map<Pair<Integer, Integer>, Quantifier> flips = new HashMap<>();
                    for (int k = 1; k <= maxK; k++) {
                        for (int j = 1; j <= maxK; j++) {
                            Quantifier countingQuantifier = Quantifier.create(TwoQuantifiers.EXISTS_EXISTS, variables, k, j);
                            quantifiers.add(countingQuantifier);
                            quantifierSuccessors.put(countingExists[k - 1], countingQuantifier);
                            if (k != j) {
                                if (k < j) {
                                    flips.put(new Pair<>(k, j), countingQuantifier);
                                } else {
                                    Quantifier previous = flips.get(new Pair<>(j, k));
                                    quantifiersMirrors.put(previous, countingQuantifier);
                                    quantifiersMirrors.put(countingQuantifier, previous);
                                }
                            }
                        }
                    }
                }
            }
        } else {
            Quantifier forall = Quantifier.create(TwoQuantifiers.FORALL, variables);
            Quantifier forallForall = Quantifier.create(TwoQuantifiers.FORALL_FORALL, variables);
            quantifiers.addAll(Sugar.list(forall, forallForall));
            quantifierSuccessors.put(forall, forallForall);
        }


        // the other are easy, but this one is a cumberstone, it is not so easy strip counting quantifiers and let match the other,
        // e.g. for (E=1 x E=1 y phi(x,y)) && (E=1 x E=1 y ~phi(x,y))   we can't conclude as easily as for
        // (E=1 x E=1 y phi(x,y)) && (V x V y ~phi(x,y))
        return new Triple<>(quantifiers, quantifierSuccessors, quantifiersMirrors);
    }


}
