/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package logicStuff.theories;

import ida.ilp.logic.*;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;

import java.util.*;
import java.util.stream.Collectors;

/**
 * WARNING: The methods in this class do not perform preemptive shattering of constants because the logicStuff.theories produced by the learner
 * do not contain constants (it uses unary literals instead of constants) and they assume an @alldiff constraint over all variables in them.
 * <p>
 * Created by kuzelkao_cardiff on 02/02/17.
 */
public class TheorySimplifier {


    private static Clause simplifyBySAT(Clause toBeSimplified, Collection<Clause> theory, int numConstants) {
        boolean changed;
        do {
            changed = false;
            if (toBeSimplified.countLiterals() > 1) {
                for (Literal l : toBeSimplified.literals()) {
                    Clause shorter = new Clause(Sugar.setDifference(toBeSimplified.literals(), l));
                    boolean implied = isImplied(shorter, theory, numConstants);
                    if (implied) {
                        toBeSimplified = shorter;
                        changed = true;
                    }
                }
            }
        } while (changed);
        return toBeSimplified;
    }

    public static List<Clause> simplify(Collection<Clause> theory, int numConstants) {
        return simplifyBySAT(removeImpliedRules(theory, numConstants), numConstants);
    }

    public static List<Clause> removeImpliedRules(Collection<Clause> theory, int numConstants) {
        List<Clause> filtered = new ArrayList<Clause>();
        Set<Clause> copy = Sugar.setFromCollections(theory);
        Map<Clause, Integer> clauseLengths = new HashMap<Clause, Integer>();
        for (Clause c : copy) {
            clauseLengths.put(c, c.countLiterals());
        }
        for (Clause c : Sugar.sortDesc(Sugar.listFromCollections(copy), clauseLengths)) {
            if (isImplied(c, copy, numConstants)) {
                copy.remove(c);
            } else {
                filtered.add(c);
            }
        }
        return filtered;
    }

    private static List<Clause> simplifyBySAT(Collection<Clause> theory, int numConstants) {
        List<Clause> filtered = new ArrayList<Clause>();
        Set<Clause> copy = Sugar.setFromCollections(theory);
        for (Clause c : Sugar.listFromCollections(copy)) {
            boolean changed;
            do {
                changed = false;
                if (c.countLiterals() > 1) {
                    for (Literal l : c.literals()) {
                        Clause shorter = new Clause(Sugar.setDifference(c.literals(), l));
                        copy.add(shorter);
                        boolean implied = isImplied(shorter, copy, numConstants);
                        copy.remove(shorter);
                        if (implied) {
                            Sugar.replace(copy, c, shorter);
                            c = shorter;
                            changed = true;
                        }
                    }
                }
            } while (changed);
        }
        filtered.addAll(copy);
        return filtered;
    }


    // this was a try for optimisation but it should be reverted :(
    public static boolean isGroundLiteralImplied(Literal l, Collection<Clause> theory, int subsumptionMode, int solverMode) {
        return isGroundLiteralImpliedImpl(l, theory.stream().map(c -> new Pair<>(c, LogicUtils.flipSigns(c))).collect(Collectors.toList()), subsumptionMode, solverMode);
    }

    private static boolean isGroundLiteralImpliedImpl(Literal l, Collection<Pair<Clause, Clause>> theory, int subsumptionMode, int solverMode) {
        if (!LogicUtils.isGround(l)) {
            throw new IllegalArgumentException("The first argument must be a ground literal.");
        }
//        String t = theory.stream().map(Clause::toString).sorted().collect(Collectors.joining("; "));
//        System.out.println("debug now\t" + l + "\t" + t.hashCode() + "\t" + t);
        Set<Pair<Clause, Clause>> copyOfTheory = Sugar.setFromCollections(theory);
        Clause lClause = new Clause(l.negation());
        copyOfTheory.add(new Pair<>(lClause, LogicUtils.flipSigns(lClause)));
        TheorySolver ts = newTS(solverMode);
        ts.setSubsumptionMode(subsumptionMode);
        //return ts.solve(copyOfTheory) == null;
        return null == ts.solvePreprocessed(copyOfTheory, Sugar.set(), Sugar.set());
    }

    public static boolean isGroundLiteralImplied(Literal l, Collection<Clause> theory, int subsumptionMode) {
        return isGroundLiteralImplied(l,
                theory,
                subsumptionMode,
                TheorySolver.CUTTING_PLANES);
    }

    public static boolean isGroundLiteralImpliedWithOptimisation(Literal l, Collection<Pair<Clause, Clause>> theory, int subsumptionMode) {
        return isGroundLiteralImpliedImpl(l, theory, subsumptionMode, TheorySolver.CUTTING_PLANES);
    }


    private static boolean isImplied(Clause clause, Collection<Clause> theory, int numConstants) {
        Set<Clause> copyOfTheory = Sugar.setFromCollections(theory);
        copyOfTheory.remove(clause);
        Clause counterExample = counterExample(clause);
        for (Literal clauseLit : counterExample.literals()) {
            copyOfTheory.add(new Clause(clauseLit));
        }
        Literal constantIntroductionLiteral = new Literal("", numConstants);
        for (int i = 0; i < numConstants; i++) {
            constantIntroductionLiteral.set(Constant.construct("c" + i), i);
        }
        copyOfTheory.add(new Clause(constantIntroductionLiteral));
        TheorySolver ts = newTS();
        return ts.solve(copyOfTheory) == null;
    }

    public static List<Clause> variants(Clause clause) {
        Set<IsoClauseWrapper> variants = new HashSet<IsoClauseWrapper>();

        throw new UnsupportedOperationException("todo");
    }

    private static TheorySolver newTS() {
        return newTS(TheorySolver.GROUND_ALL);
    }


    private static TheorySolver newTS(int mode) {
        TheorySolver retVal = new TheorySolver();
        retVal.setSubsumptionMode(Matching.OI_SUBSUMPTION);
        retVal.setSubsumptionMode(mode);
        return retVal;
    }

    private static Clause counterExample(Clause c) {
        int numConstants = c.variables().size();
        Literal constantIntroduction = new Literal("", numConstants);
        Literal truePred = new Literal(SpecialVarargPredicates.TRUE, true, numConstants);
        for (int i = 0; i < numConstants; i++) {
            constantIntroduction.set(Constant.construct("c" + i), i);
        }
        int i = 0;
        for (Variable v : c.variables()) {
            truePred.set(v, i);
            i++;
        }
        Clause e = new Clause(constantIntroduction);
        List<Literal> special = new ArrayList<Literal>();
        special.add(truePred);
        List<Literal> other = new ArrayList<Literal>();
        for (Literal l : c.literals()) {
            if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()) || SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())) {
                special.add(l);
            } else {
                other.add(l);
            }
        }
        Clause auxC = new Clause(LogicUtils.flipSigns(special));
        Matching m = new Matching();
        m.setSubsumptionMode(Matching.OI_SUBSUMPTION);
        Pair<Term[], List<Term[]>> subs = m.allSubstitutions(auxC, e, 1);
        return LogicUtils.flipSigns(LogicUtils.substitute(new Clause(other), subs.r, subs.s.get(0)));
    }

}
