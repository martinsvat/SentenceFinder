package ida.sentences.generators;

import ida.ilp.logic.*;
import ida.sentences.caches.Cache;
import ida.sentences.caches.LiteralsCache;
import ida.sentences.caches.VariablesCache;
import ida.utils.Combinatorics;
import ida.utils.Sugar;

import java.util.*;

public class LiteralsGenerator {


    // return interconnected literals so Literal::negation(), Literal::flipSigns(), etc. works in constant time
    public static List<Literal> generate(List<Variable> variables, List<Predicate> predicates) {
        if (2 != variables.size()) {
            throw new IllegalStateException();
        }
        List<Literal> retVal = Sugar.list();
        Map<Literal, Literal> lookup = new HashMap<>();
        Cache<Set<Variable>> variablesCache = VariablesCache.getInstance();

        Map<Term, Term> substitution = new HashMap<>();
        substitution.put(variables.get(0), variables.get(1));
        substitution.put(variables.get(1), variables.get(0));
        // LiteralsCache cache = LiteralsCache.getInstance(); // TODO find out why literalsCache fails the whole process !!!

        for (Predicate predicate : predicates) {
            for (List<Variable> currentVariables : Combinatorics.variationsWithRepetition(Sugar.setFromCollections(variables), predicate.getArity())) {
                for (Boolean sign : Sugar.list(false, true)) {
                    //Literal literal = cache.get(new Literal(predicate.getName(), sign, currentVariables));
                    Literal literal = new Literal(predicate.getName(), sign, currentVariables);
                    if (lookup.containsKey(literal)) {
                        literal = lookup.get(literal);
                    } else {
                        lookup.put(literal, literal);
                    }
                    // TODO ta variable cache se chova jinak nez bych chtel, predelat :))
                    literal.setVariables(variablesCache.get(Sugar.setFromCollections(currentVariables)));

                    // negation inter-wined
                    Literal negation = literal.copy();
                    negation.setNegation(!sign);
                    if (lookup.containsKey(negation)) {
                        negation = lookup.get(negation);
                    } else {
                        lookup.put(negation, negation);
                    }
                    literal.setNegatedPair(negation);
                    negation.setNegatedPair(literal);

                    // mirror substitution
//                    Literal mirror = cache.get(LogicUtils.substitute(literal, substitution));
                    Literal mirror = LogicUtils.substitute(literal, substitution);
                    if (!lookup.containsKey(mirror)) {
                        literal.setMirror(mirror);
                        mirror.setMirror(literal);
                        lookup.put(mirror, mirror);
                    }

                    // flip symmetry
                    List<Variable> reversed = Sugar.listFromCollections(currentVariables);
                    Collections.reverse(reversed);
                    //Literal flipped = cache.get(new Literal(predicate.getName(), sign, reversed));
                    Literal flipped = new Literal(predicate.getName(), sign, reversed);
                    if (flipped.equals(literal)) {
                        literal.setFlipped(literal);
                    } else {
                        if (lookup.containsKey(flipped)) {
                            flipped = lookup.get(flipped);
                        } else {
                            lookup.put(flipped, flipped);
                        }
                        literal.setFlipped(flipped);
                        flipped.setFlipped(literal);
                    }
                    literal.allowModifications(false);
                    retVal.add(literal);
                }
            }
        }
        // fill in the cache!
        for (Literal literal : retVal) {
            LiteralsCache.getInstance().get(literal);
        }
        return retVal;
    }


    public static Map<Literal, Literal> literalsToMap(Collection<Literal> literals) {
        Map<Literal, Literal> retVal = new HashMap<>();
        for (Literal literal : literals) {
            retVal.put(literal, literal);
        }
        return retVal;
    }

    public static Map<String, Literal> stringToLiteralCache(Collection<Literal> literals) {
        Map<String, Literal> retVal = new HashMap<>();
        for (Literal literal : literals) {
            retVal.put(literal.toString(), literal);
        }
        return retVal;
    }
}
