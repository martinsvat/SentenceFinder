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

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.LogicUtils;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.Sugar;
import ida.utils.collections.ValueToIndex;
import ida.utils.tuples.Pair;
import org.sat4j.core.VecInt;
import org.sat4j.maxsat.WeightedMaxSatDecorator;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.GateTranslator;
import org.sat4j.tools.ModelIterator;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 04/02/15.
 */
public class GroundTheorySolver {

    private List<Pair<Clause, BigInteger>> softClauses = new ArrayList<Pair<Clause, BigInteger>>();

    private List<Clause> hardClauses = new ArrayList<Clause>();

    private List<int[]> hardDimacsClauses;

    private List<Pair<int[], BigInteger>> softDimacsClauses;

    private List<Literal> hardAtLeastConstraints = new ArrayList<Literal>();

    private List<Literal> hardAtMostConstraints = new ArrayList<Literal>();

    private List<Literal> hardXorConstraints = new ArrayList<Literal>();

    private List<Literal> auxXorLiterals = new ArrayList<Literal>();

    private List<Pair<int[], Integer>> hardDimacsAtLeastConstraints;

    private List<Pair<int[], Integer>> hardDimacsAtMostConstraints;

    private List<Pair<int[], Boolean>> hardDimacsXorConstraints;

    private ValueToIndex<Literal> literalsToIndices = new ValueToIndex<Literal>(1);

    private int optimizationTimeout = Integer.MAX_VALUE;

    private GateTranslator solver;

    private WeightedMaxSatDecorator optimizer;

    private final static String ATLEAST = "@atleast", ATMOST = "@atmost", XOR = "@xor";

    public GroundTheorySolver(Collection<Clause> hardClauses) {
        this(hardClauses, null, null);
    }

    public GroundTheorySolver(Collection<Clause> hardClauses, Set<Literal> groundAtoms) {
        this(hardClauses, groundAtoms, null);
    }

    public GroundTheorySolver(Collection<Clause> hardClauses, Collection<Pair<Clause, BigInteger>> softClauses) {
        this(hardClauses, null, softClauses);
    }

    public GroundTheorySolver(Collection<Clause> hardClauses, Set<Literal> groundAtoms, Collection<Pair<Clause, BigInteger>> softClauses) {
        Set<String> allPredicates = new HashSet<String>();
        if (softClauses != null) {
            for (Pair<Clause, BigInteger> c : softClauses) {
                for (Literal literal : c.r.literals()) {
                    literalsToIndices.valueToIndex(literal.isNegated() ? literal.negation() : literal);
                }
                if (c.s == null) {
                    this.hardClauses.add(c.r);
                } else {
                    Set<String> predicates = c.r.predicates();
                    if (predicates.contains(ATLEAST) || predicates.contains(ATMOST)) {
                        throw new UnsupportedOperationException("Soft clauses with @atmost and @atleast are not supported in the current version.");
                    }
                    this.softClauses.add(new Pair<Clause, BigInteger>(c.r, c.s));
                }
            }
        }
        this.softDimacsClauses = this.toSoftDimacsClauses(this.softClauses);
        for (Clause c : hardClauses) {
            Set<String> predicates = c.predicates();
            allPredicates.addAll(predicates);
            if (predicates.contains(ATLEAST) || predicates.contains(ATMOST)) {
                addCardinalityConstraint(c);
            } else if (predicates.contains(XOR)) {
                addXorConstraint(c);
            } else {
                for (Literal literal : c.literals()) {
                    literalsToIndices.valueToIndex(literal.isNegated() ? literal.negation() : literal);
                }
                this.hardClauses.add(c);
            }
        }
        if (groundAtoms != null) {
            for (Literal l : groundAtoms) {
                this.literalsToIndices.valueToIndex(l);
            }
        }
        this.hardDimacsAtLeastConstraints = this.toHardDimacsCardinalityConstraints(this.hardAtLeastConstraints);
        this.hardDimacsAtMostConstraints = this.toHardDimacsCardinalityConstraints(this.hardAtMostConstraints);
        this.hardDimacsClauses = this.toHardDimacsClauses(this.hardClauses);
        this.hardDimacsXorConstraints = this.toHardDimacsXorConstraints(this.hardXorConstraints);
        for (String predicateName : LogicUtils.freshPredicateNames(allPredicates, this.hardXorConstraints.size())) {
            Literal auxLit = new Literal(predicateName);
            this.auxXorLiterals.add(auxLit);
            this.literalsToIndices.valueToIndex(auxLit);
        }
    }

    private void addCardinalityConstraint(Clause cardinalityConstraint) {
        if (cardinalityConstraint.literals().size() > 1) {
            throw new IllegalArgumentException("The predicateNames @atmost and @atleast can only be used on their own. Specifically they cannot be used in clauses containing anything else, at least in this version...");
        } else {
            Literal l = Sugar.chooseOne(cardinalityConstraint.literals());
            if (l.predicate().equals(ATLEAST)) {
                this.hardAtLeastConstraints.add(l);
            } else if (l.predicate().equals(ATMOST)) {
                this.hardAtMostConstraints.add(l);
            }
        }
    }

    private void addXorConstraint(Clause xor) {
        if (xor.literals().size() > 1) {
            throw new IllegalArgumentException("The predicate @xor can only be used on its own. Specifically it cannot be used in clauses containing anything else, at least in this version...");
        }
        Literal l = Sugar.chooseOne(xor.literals());
        this.hardXorConstraints.add(l);
    }


    public Set<Literal> solve() {
        try {
            if (this.solver == null) {
                this.solver = new GateTranslator(SolverFactory.newDefault());
                //this.solver = SolverFactory.newMiniLearningHeap();
                this.solver.newVar(this.literalsToIndices.size());
                this.solver.setExpectedNumberOfClauses(hardClauses.size() + softClauses.size() + hardXorConstraints.size() + hardAtLeastConstraints.size() + hardAtMostConstraints.size());
                try {
                    for (int[] clause : hardDimacsClauses) {
                        this.solver.addClause(new VecInt(clause));
                    }
                    for (Pair<int[], Integer> atleast : this.hardDimacsAtLeastConstraints) {
                        this.solver.addAtLeast(new VecInt(atleast.r), atleast.s);
                    }
                    for (Pair<int[], Integer> atmost : this.hardDimacsAtMostConstraints) {
                        this.solver.addAtMost(new VecInt(atmost.r), atmost.s);
                    }
                    int xorIndex = 0;
                    for (Pair<int[], Boolean> xor : this.hardDimacsXorConstraints) {
                        int auxLitIndex = this.literalsToIndices.valueToIndex(auxXorLiterals.get(xorIndex));
                        this.solver.xor(auxLitIndex, new VecInt(xor.r));
                        this.solver.addClause(new VecInt(new int[]{xor.s ? auxLitIndex : -auxLitIndex}));
                        xorIndex++;
                    }
                } catch (ContradictionException ce) {
                    return null;
                }
            }

            IProblem problem = this.solver;
            Set<Literal> auxLiteralsSet = Sugar.setFromCollections(this.auxXorLiterals);
            if (problem.isSatisfiable()) {
                int[] model = problem.model();
                Set<Literal> solution = new HashSet<Literal>();
                for (int i : model) {
                    if (i > 0) {
                        Literal l = literalsToIndices.indexToValue(i);
                        if (!auxLiteralsSet.contains(l)) {
                            solution.add(l);
                        }
                    }
                }
                return solution;
            }
            return null;
        } catch (TimeoutException e) {
            e.printStackTrace();
            return null;
        }
    }

    public List<Set<Literal>> solveAll(int numSolutions) {
        List<Set<Literal>> retVal = new ArrayList<Set<Literal>>();
        try {
            if (this.solver == null) {
                this.solver = new GateTranslator(SolverFactory.newDefault());
                //this.solver = SolverFactory.newMiniLearningHeap();
                this.solver.newVar(this.literalsToIndices.size());
                this.solver.setExpectedNumberOfClauses(hardClauses.size() + softClauses.size());
                try {
                    for (int[] clause : hardDimacsClauses) {
                        this.solver.addClause(new VecInt(clause));
                    }
                    for (Pair<int[], Integer> atleast : this.hardDimacsAtLeastConstraints) {
                        this.solver.addAtLeast(new VecInt(atleast.r), atleast.s);
                    }
                    for (Pair<int[], Integer> atmost : this.hardDimacsAtMostConstraints) {
                        this.solver.addAtMost(new VecInt(atmost.r), atmost.s);
                    }
                    int xorIndex = 0;
                    for (Pair<int[], Boolean> xor : this.hardDimacsXorConstraints) {
                        //System.out.println("xor: "+ VectorUtils.intArrayToString(xor.r));
                        int auxLitIndex = this.literalsToIndices.valueToIndex(auxXorLiterals.get(xorIndex));
                        this.solver.xor(auxLitIndex, new VecInt(xor.r));
                        this.solver.addClause(new VecInt(new int[]{xor.s ? auxLitIndex : -auxLitIndex}));
                        xorIndex++;
                    }
                    for (Literal l : literalsToIndices.values()) {
                        int lIndex = literalsToIndices.valueToIndex(l);
                        this.solver.addClause(new VecInt(new int[]{lIndex, -lIndex}));
                    }
                } catch (ContradictionException ce) {
                    return retVal;
                }
            }

            IProblem problem = new ModelIterator(this.solver);
            Set<Literal> auxLiteralsSet = Sugar.setFromCollections(this.auxXorLiterals);
            int num = 0;
            while (problem.isSatisfiable() && (numSolutions < 0 || num < numSolutions)) {
                int[] model = problem.model();
                System.out.println("solution found");
                for (int i = 0; i < model.length; i++) {
                    System.out.println(" " + model[i]);
                }
                System.out.println("");
                Set<Literal> solution = new HashSet<Literal>();
                for (int i : model) {
                    if (i > 0) {
                        Literal l = literalsToIndices.indexToValue(i);
                        if (!auxLiteralsSet.contains(l)) {
                            solution.add(l);
                        }
                    }
                }
                retVal.add(solution);
                num++;
            }
            return retVal;
        } catch (TimeoutException e) {
            e.printStackTrace();
            return retVal;
        }
    }

    public List<Set<Literal>> solveAll() {
        return solveAll(-1);
    }

    public Set<Literal> optimize() {
        try {
            if (this.optimizer == null) {
                this.optimizer = new WeightedMaxSatDecorator(org.sat4j.pb.SolverFactory.newDefaultOptimizer());
                this.optimizer.newVar(this.literalsToIndices.size());
                this.optimizer.setExpectedNumberOfClauses(softClauses.size() + hardClauses.size());
                BigInteger maxWeight = null;
                for (Pair<Clause, BigInteger> pair : this.softClauses) {
                    if (pair.s != null && (maxWeight == null || maxWeight.compareTo(pair.s) < 0)) {
                        maxWeight = pair.s;
                    }
                }
                if (maxWeight != null) {
                    this.optimizer.setTopWeight(maxWeight.add(BigInteger.ONE));
                }
                this.optimizer.setTimeoutMs(optimizationTimeout);
                if (this.hardDimacsClauses != null) {
                    for (int[] clause : hardDimacsClauses) {
                        this.optimizer.addHardClause(new VecInt(clause));
                    }
                }

                if (this.softDimacsClauses != null) {
                    for (Pair<int[], BigInteger> clause : this.softDimacsClauses) {
                        this.optimizer.addSoftClause(clause.s, new VecInt(clause.r));
                    }
                }
            }
            if (this.optimizer.isSatisfiable()) {
                int[] model;// = solver.model();
                Set<Literal> solution = new HashSet<Literal>();
                model = this.optimizer.model();

                for (int i : model) {
                    if (i > 0) {
                        solution.add(literalsToIndices.indexToValue(i));
                    }
                }
                return solution;
            }
        } catch (Exception e) {
            return null;
        }
        return null;
    }

    private List<Pair<int[], BigInteger>> toSoftDimacsClauses(Collection<Pair<Clause, BigInteger>> program) {
        List<Pair<int[], BigInteger>> retVal = new ArrayList<Pair<int[], BigInteger>>();
        for (Pair<Clause, BigInteger> c : program) {
            int[] clause = new int[c.r.literals().size()];
            int i = 0;
            for (Literal l : c.r.literals()) {
                if (l.isNegated()) {
                    clause[i] = -literalsToIndices.valueToIndex(l.negation());
                } else {
                    clause[i] = literalsToIndices.valueToIndex(l);
                }
                i++;
            }

            retVal.add(new Pair<int[], BigInteger>(clause, c.s));
        }
        return retVal;
    }

    private List<Pair<int[], Integer>> toHardDimacsCardinalityConstraints(List<Literal> constraints) {
        List<Pair<int[], Integer>> retVal = new ArrayList<Pair<int[], Integer>>();
        for (Literal l : constraints) {
            retVal.add(toHardDimacsCardinalityConstraint(l));
        }
        return retVal;
    }

    private List<Pair<int[], Boolean>> toHardDimacsXorConstraints(List<Literal> constraints) {
        List<Pair<int[], Boolean>> retVal = new ArrayList<Pair<int[], Boolean>>();
        for (Literal l : constraints) {
            int[] arr = toHardDimacsXorConstraint(l);
            Arrays.sort(arr);
            retVal.add(new Pair<int[], Boolean>(arr, Boolean.valueOf(!l.isNegated())));
        }
        return retVal;
    }

    private Pair<int[], Integer> toHardDimacsCardinalityConstraint(Literal l) {
        int[] constr = new int[l.arity() - 1];
        for (int i = 0; i < constr.length; i++) {
            constr[i] = literalsToIndices.valueToIndex(LogicUtils.termToLiteral(l.get(i + 1)));
        }
        return new Pair<int[], Integer>(constr, Integer.parseInt(l.get(0).name()));
    }

    private int[] toHardDimacsXorConstraint(Literal l) {
        int[] xor = new int[l.arity()];
        for (int i = 0; i < xor.length; i++) {
            xor[i] = literalsToIndices.valueToIndex(LogicUtils.termToLiteral(l.get(i)));
        }
        return xor;
    }

    private List<int[]> toHardDimacsClauses(List<Clause> program) {
        List<int[]> retVal = new ArrayList<int[]>();
        for (Clause c : program) {
            retVal.add(this.toHardDimacsClause(c));
        }
        return retVal;
    }

    private int[] toHardDimacsClause(Clause c) {
        int[] hardDimacsClause = new int[c.literals().size()];
        int i = 0;
        for (Literal l : c.literals()) {
            if (l.isNegated()) {
                hardDimacsClause[i] = -literalsToIndices.valueToIndex(l.negation());
            } else {
                hardDimacsClause[i] = literalsToIndices.valueToIndex(l);
            }
            i++;
        }
        return hardDimacsClause;
    }

    public List<Clause> hardRules() {
        return this.hardClauses;
    }

    public List<Pair<Clause, BigInteger>> softRules() {
        return this.softClauses;
    }

    public static Set<Clause> simplifyTheory(Collection<Clause> theory) {

        return null;
    }

    public static boolean isImplied(Clause clause, Collection<Clause> theory) {
        Set<Clause> copyOfAlphaLevel = Sugar.setFromCollections(theory);
        copyOfAlphaLevel.remove(clause);
        for (Literal clauseLit : LogicUtils.flipSigns(clause).literals()) {
            if (!SpecialVarargPredicates.SPECIAL_PREDICATES.contains(clauseLit.predicate()) && !SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(clauseLit.predicate())) {
                copyOfAlphaLevel.add(new Clause(Sugar.list(clauseLit)));
            }
        }
        GroundTheorySolver gps = new GroundTheorySolver(copyOfAlphaLevel);
        return gps.solve() == null;
    }

    public static List<Clause> simplify(Collection<Clause> theory) {
        return simplifyBySAT(removeImpliedRules(theory));
    }

    private static List<Clause> removeImpliedRules(Collection<Clause> theory) {
        List<Clause> filtered = new ArrayList<Clause>();
        Set<Clause> copy = Sugar.setFromCollections(theory);
        Map<Clause, Integer> clauseLengths = new HashMap<Clause, Integer>();
        for (Clause c : copy) {
            clauseLengths.put(c, c.countLiterals());
        }
        for (Clause c : Sugar.sortDesc(Sugar.listFromCollections(copy), clauseLengths)) {
            if (isImplied(c, copy)) {
                copy.remove(c);
            } else {
                filtered.add(c);
            }
        }
        return filtered;
    }

    private static List<Clause> simplifyBySAT(Collection<Clause> theory) {
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
                        boolean implied = isImplied(shorter, copy);
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

    public static void main(String[] args) {
//        Clause c1 = Clause.parse("a(x), b(x), c(x)");
//        Clause c2 = Clause.parse("@atleast(2,a(x),b(x),c(x))");
//        Clause c3 = Clause.parse("@atmost(2,a(x),b(x),c(x))");
//        Clause c4 = Clause.parse("@xor(a(x),b(x),c(x))");
//        GroundTheorySolver gts = new GroundTheorySolver(Sugar.list(c1, c4));
        Clause c1 = Clause.parse("a(x), !a(x)");
        Clause c2 = Clause.parse("b(x), !b(x)");
        Clause c3 = Clause.parse("!a(x), !b(x), c(x)");
        Clause c4 = Clause.parse("!a(x), !b(x)");

        GroundTheorySolver gts = new GroundTheorySolver(Sugar.list(c1, c2, c3, c4));

        System.out.println(gts.solveAll());
    }

    public void setOptimizationTimeout(int optimizationTimeout) {
        this.optimizationTimeout = optimizationTimeout;
    }
}
