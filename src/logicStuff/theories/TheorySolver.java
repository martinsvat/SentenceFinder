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
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.IntegerFunction;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by kuzelkao_cardiff on 06/02/15.
 */
public class TheorySolver {

    public static boolean DEBUG = false;

    private int subsumptionMode = Matching.THETA_SUBSUMPTION;

    private Set<Literal> deterministicLiterals;

    private Set<Pair<String, Integer>> deterministicPredicates = new HashSet<Pair<String, Integer>>();

    private SpecialBinaryPredicates specialBinaryPredicates = new SpecialBinaryPredicates();

    public final static int CUTTING_PLANES = 1, GROUND_ALL = 2;

    private int mode = CUTTING_PLANES; // GROUND_ALL;

    private int activeRuleSubsample = Integer.MAX_VALUE;

    private int activeRuleSubsamplingLevelStep = 1;

    private IntegerFunction restartSequence = new IntegerFunction.ConstantFunction(Integer.MAX_VALUE);

    private SatSolver satSolver = new SatSolver() {

        @Override
        public Set<Literal> solve(Collection<Clause> satProblem) {
            return new GroundTheorySolver(Sugar.setFromCollections(satProblem)).solve();
        }

        @Override
        public List<Set<Literal>> solveAll(Collection<Clause> satProblem, int maxCount) {
            return new GroundTheorySolver(Sugar.setFromCollections(satProblem)).solveAll(maxCount);
        }

        @Override
        public List<Set<Literal>> solveAll(Collection<Clause> satProblem, Set<Literal> groundAtoms, int maxCount) {
            return new GroundTheorySolver(Sugar.setFromCollections(satProblem), groundAtoms).solveAll(maxCount);
        }
    };

    public Set<Literal> solve(Collection<Clause> rules) {
        return this.solve(rules, Sugar.<Literal>set());
    }

    public Set<Literal> solve(Collection<Clause> rules, Set<Literal> evidence) {
        return this.solve(rules, evidence, Sugar.<Literal>set());
    }

    public Set<Literal> solve(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic) {
        return solvePreprocessed(rules.stream().map(c -> new Pair<>(c, LogicUtils.flipSigns(c))).collect(Collectors.toList()),
                evidence,
                deterministic);
    }

    public Set<Literal> solvePreprocessed(Collection<Pair<Clause, Clause>> rules, final Set<Literal> evidence, final Set<Literal> deterministic) {
        Set<Constant> constants = collectConstants(rules.stream().map(Pair::getR));

        // hack here, because when clause is used for testing subsumption in parallel, then some error can occur in c.variableDomains[index].size() (dynamic creation of index, Ondra's email]
        rules = rules.stream().map(p -> new Pair<>(p.r, LogicUtils.flipSigns(p.r))).collect(Collectors.toList());

        for (Literal d : deterministic) {
            this.deterministicPredicates.add(new Pair<String, Integer>(d.predicate(), d.arity()));
        }
        this.deterministicLiterals = deterministic;

        Set<Literal> state = new HashSet<Literal>();
        Set<Pair<Clause, Clause>> initRules = new HashSet<>();
        Pair<String, Integer> p = new Pair<String, Integer>();
        for (Literal e : evidence) {
            p.set(e.predicate(), e.arity());
            if (deterministicPredicates.contains(p)) {
                if ((e.isNegated() && deterministic.contains(e.negation())) || (!e.isNegated() && !deterministic.contains(e))) {
                    return null;
                }
            } else {
                if (!e.isNegated()) {
                    state.add(e);
                }
                Clause c = new Clause(Sugar.list(e));
                initRules.add(new Pair<>(c, LogicUtils.flipSigns(c)));
            }
        }
        state.addAll(deterministic);
        Set<Pair<Clause, Clause>> groundRules = new HashSet<>();
        for (Pair<Clause, Clause> pair : rules) {
            if (LogicUtils.isGround(pair.r)) {
                groundRules.add(pair);
            }
        }

        rules = Sugar.collectionDifference(rules, groundRules);

        initRules.addAll(groundRules);
        if (this.mode == GROUND_ALL) {
            List<Clause> q = rules.stream().map(Pair::getR).collect(Collectors.toList());
            initRules.addAll(groundAll(q, state, Sugar.set()).stream().map(c -> new Pair<>(c, LogicUtils.flipSigns(c))).collect(Collectors.toList()));
        }
        initRules = Sugar.funcallAndRemoveNulls(initRules, new Sugar.Fun<Pair<Clause, Clause>, Pair<Clause, Clause>>() {
            @Override
            public Pair<Clause, Clause> apply(Pair<Clause, Clause> pair) {
                if (isGroundClauseVacuouslyTrue(pair.r, deterministic)) {
                    return null;
                } else {
                    Clause c = removeSpecialAndDeterministicPredicates(pair.r);
                    return new Pair<>(c, LogicUtils.flipSigns(c));
                }
            }
        });

        Set<Clause> activeRules = initRules.stream().map(Pair::getR).collect(Collectors.toSet());


        int iteration = 1;
        int restart = 0;
        while (true) {
            if (DEBUG) {
                System.out.println("Active rules: " + activeRules.size() + ", iteration: " + iteration);
            }
            //System.out.println(activeRules);
            if ((state = satSolver.solve(activeRules)) == null) {
                return null;
            }
            state.addAll(deterministic);

            // s tim prvnim radkem to neprochazelo jednim testem
            Set<Clause> violatedRules = Sugar.setFromCollections(findViolatedRulesNew(Sugar.union(rules, initRules), state, constants));
//            Set<Clause> violatedRules = Sugar.setFromCollections(findViolatedRules(rules, state)); // puvodni verze

            violatedRules = Sugar.funcallAndRemoveNulls(violatedRules, new Sugar.Fun<Clause, Clause>() {
                @Override
                public Clause apply(Clause rule) {
                    if (isGroundClauseVacuouslyTrue(rule, deterministic)) {
                        System.out.println("weird: " + rule + ", ~~~" + LogicUtils.flipSigns(rule));
                        return null;
                    } else {
                        return removeSpecialAndDeterministicPredicates(rule);
                    }
                }
            });

//            activeRules.addAll(initRules); // tohle taky puvodni verze, melo by to byt spolecne s rakdme 141 pryc
            activeRules.addAll(violatedRules);

            iteration++;
            if (violatedRules.isEmpty()) {
                //sanity checkq
                if (this.activeRuleSubsample != Integer.MAX_VALUE) {
                    this.activeRuleSubsample = Integer.MAX_VALUE;
                    if (!findViolatedRulesNew(rules, state, constants).isEmpty()) {
                        throw new IllegalStateException();
                    }
                }
                break;
            }
            if (iteration >= this.restartSequence.f(restart)) {
                Set<Clause> oldActiveRules = activeRules;
                //activeRules = new HashSet<Clause>(initRules);//Sugar.union(violatedRules, initRules);
                activeRules = initRules.stream().map(Pair::getR).collect(Collectors.toSet());
//                for (Clause c : oldActiveRules){
//                    if (Math.random() < 0.1){
//                        activeRules.add(c);
//                    }
//                }
                iteration = 0;
                restart++;
            }
        }
        return state;
    }

    private Set<Constant> collectConstants(Stream<Clause> stream) {
        Set<Constant> retVal = Sugar.set();
        stream.forEach(clause -> retVal.addAll(LogicUtils.constants(clause)));
        return retVal;
    }


    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, int maxCount) {
        return solveAll(rules, evidence, deterministic, null, maxCount);
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, Set<Literal> groundAtoms, int maxCount) {
        return solveAll(rules, evidence, deterministic, groundAtoms, maxCount, maxCount);
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, int maxReturnedCount, int maxTriedCount) {
        return solveAll(rules, evidence, deterministic, null, maxReturnedCount, maxTriedCount);
    }

    public List<Set<Literal>> solveAll(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic, Set<Literal> groundAtoms, int maxReturnedCount, int maxTriedCount) {
        for (Literal d : deterministic) {
            this.deterministicPredicates.add(new Pair<String, Integer>(d.predicate(), d.arity()));
        }
        this.deterministicLiterals = deterministic;

        Set<Literal> fixedState = new HashSet<Literal>();

        Set<Clause> initRules = new HashSet<Clause>();
        Pair<String, Integer> p = new Pair<String, Integer>();
        for (Literal e : evidence) {
            p.set(e.predicate(), e.arity());
            if (deterministicPredicates.contains(p)) {
                if ((e.isNegated() && deterministic.contains(e.negation())) || (!e.isNegated() && !deterministic.contains(e))) {
                    return new ArrayList<Set<Literal>>();
                }
            } else {
                if (!e.isNegated()) {
                    fixedState.add(e);
                }
                initRules.add(new Clause(Sugar.list(e)));
            }
        }
        fixedState.addAll(deterministic);
        Set<Clause> groundRules = new HashSet<Clause>();
        for (Clause rule : rules) {
            if (LogicUtils.isGround(rule)) {
                groundRules.add(rule);
            }
            if (rule.literals().isEmpty()) {
                return new ArrayList<Set<Literal>>();
            }
        }
        rules = Sugar.collectionDifference(rules, groundRules);
        initRules.addAll(groundRules);
        initRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(initRules, new Sugar.Fun<Clause, Clause>() {
            @Override
            public Clause apply(Clause clause) {
                if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                    return null;
                } else {
                    return removeSpecialAndDeterministicPredicates(clause);
                }
            }
        });


        System.out.println("tady ty metodu jsem asi nikdy nepustil, ale nejspis nebude opravena pro nektery test case saturaci");
        Set<Clause> activeRules = new HashSet<Clause>();
        activeRules.addAll(initRules);

        if (this.mode == GROUND_ALL) {
            activeRules.addAll(groundAll(rules, evidence, groundAtoms));
            activeRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(activeRules, new Sugar.Fun<Clause, Clause>() {
                @Override
                public Clause apply(Clause clause) {
                    if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                        return null;
                    } else {
                        return removeSpecialAndDeterministicPredicates(clause);
                    }
                }
            });
            return satSolver.solveAll(activeRules, groundAtoms, maxReturnedCount);
        } else {
            int mc = 1;
            Set<Set<Literal>> retVal = new HashSet<Set<Literal>>();
            do {
                int iteration = 1;
                mc = Math.min(2 * mc, maxTriedCount);
                while (true) {
                    System.out.println("Active rules: " + activeRules.size() + ", iteration: " + iteration);
                    List<Set<Literal>> candidateSolutions = satSolver.solveAll(activeRules, groundAtoms, mc);
                    if (candidateSolutions.isEmpty()) {
                        return candidateSolutions;
                    }
                    int numViolatedRules = 0;
                    for (Set<Literal> solution : candidateSolutions) {
                        Set<Clause> violatedRules = Sugar.setFromCollections(findViolatedRules(Sugar.union(rules, initRules), Sugar.union(solution, deterministic)));
                        violatedRules = Sugar.<Clause, Clause>funcallAndRemoveNulls(violatedRules, new Sugar.Fun<Clause, Clause>() {
                            @Override
                            public Clause apply(Clause clause) {
                                if (isGroundClauseVacuouslyTrue(clause, deterministic)) {
                                    System.out.println("weird: " + clause + ", ~~~" + LogicUtils.flipSigns(clause));
                                    return null;
                                } else {
                                    return removeSpecialAndDeterministicPredicates(clause);
                                }
                            }
                        });
                        if (violatedRules.isEmpty()) {
                            retVal.add(solution);
                        } else {
                            numViolatedRules += violatedRules.size();
                            activeRules.addAll(violatedRules);
                        }
                    }
                    iteration++;
                    if (numViolatedRules == 0 || retVal.size() >= maxReturnedCount) {
                        //sanity check
                        for (Set<Literal> solution : retVal) {
                            //System.out.println(solution);
                            if (this.activeRuleSubsample != Integer.MAX_VALUE) {
                                this.activeRuleSubsample = Integer.MAX_VALUE;
                                if (!findViolatedRules(rules, solution).isEmpty()) {
                                    throw new IllegalStateException();
                                }
                            }
                        }
                        break;
                    }
                }
            } while (mc < maxReturnedCount && retVal.size() >= mc);
            return Sugar.listFromCollections(retVal);
        }
    }

    public List<Clause> findViolatedRules(Collection<Clause> rules, Set<Literal> currentState) {
        List<Clause> violated = new ArrayList<Clause>();
        Set<Constant> constants = LogicUtils.constants(rules); // bottleneck? cache somehow?
        for (Literal l : currentState) {
            for (int i = 0; i < l.arity(); i++) {
                if (constants.contains(l.get(i))) {
                    constants.remove(l.get(i));
                }
            }
        }

        // introducing constants which are not in the state yet
        Literal constantIntroductionLiteral = new Literal("", true, constants.size());

        int constantIndex = 0;
        for (Constant c : constants) {
            constantIntroductionLiteral.set(c, constantIndex++);
        }

        Matching matching = newM(new Clause(Sugar.union(currentState, constantIntroductionLiteral)));
        for (Clause rule : rules) {
            if (this.activeRuleSubsample == Integer.MAX_VALUE) {
                Pair<Term[], List<Term[]>> substitutions = matching.allSubstitutions(LogicUtils.flipSigns(rule), 0, Integer.MAX_VALUE);
                for (Term[] subs : substitutions.s) {
                    violated.add(LogicUtils.substitute(rule, substitutions.r, subs));
                }
            } else {
                Pair<Term[], List<Term[]>> substitutions0 = matching.allSubstitutions(LogicUtils.flipSigns(rule), 0, this.activeRuleSubsample);
                if (substitutions0.s.size() < this.activeRuleSubsample) {
                    for (Term[] subs : substitutions0.s) {
                        violated.add(LogicUtils.substitute(rule, substitutions0.r, subs));
                    }
                } else {
                    Triple<Term[], List<Term[]>, Double> substitutions = matching.searchTreeSampler(LogicUtils.flipSigns(rule), 0, this.activeRuleSubsample, this.activeRuleSubsamplingLevelStep);
                    for (Term[] subs : substitutions.s) {
                        violated.add(LogicUtils.substitute(rule, substitutions.r, subs));
                    }
                }
            }
        }
        return violated;
    }

    // optimalized implementation of findViolatedRules
    private List<Clause> findViolatedRulesNew(Collection<Pair<Clause, Clause>> rules, Set<Literal> currentState, Set<Constant> constants) {
        List<Clause> violated = Sugar.list();

        Set<Constant> stateConstants = LogicUtils.constantsFromLiterals(currentState);
        List<Constant> introducedConstants = Sugar.list();
        for (Constant constant : constants) {
            if (!stateConstants.contains(constant)) {
                introducedConstants.add(constant);
            }
        }
        Literal constantsIntroductionLiteral = new Literal("", true, introducedConstants);

        Matching matching = newM(new Clause(Sugar.union(currentState, constantsIntroductionLiteral)));
        for (Pair<Clause, Clause> pair : rules) {
            Clause rule = pair.r;
            Clause negatedRule = pair.s;
            //Clause negatedRule = LogicUtils.flipSigns(pair.r);
            Pair<Term[], List<Term[]>> substitutions = violatedSubsitutions(matching, negatedRule);
            for (Term[] subs : substitutions.s) {
                violated.add(new Clause(LogicUtils.substitute(rule, substitutions.r, subs).literals().stream().filter(l -> !l.predicate().equals(SpecialVarargPredicates.ALLDIFF)).collect(Collectors.toList())));
            }
        }
        return violated;
    }

    private Pair<Term[], List<Term[]>> violatedSubsitutions(Matching matching, Clause negatedRule) {
        // the trick is that the rules is existentially quantified, thus negation of universally quantified rule
//        synchronized (negatedRule) {
        if (this.activeRuleSubsample == Integer.MAX_VALUE) {
            return matching.allSubstitutions(negatedRule, 0, Integer.MAX_VALUE);
        }
        Pair<Term[], List<Term[]>> substitutions0 = matching.allSubstitutions(negatedRule, 0, this.activeRuleSubsample);
        if (substitutions0.s.size() < this.activeRuleSubsample) {
            return substitutions0;
        } else {
            Triple<Term[], List<Term[]>, Double> substitutions = matching.searchTreeSampler(negatedRule, 0, this.activeRuleSubsample, this.activeRuleSubsamplingLevelStep);
            return new Pair<>(substitutions.r, substitutions.s);
        }
//        }
    }

    public List<Clause> groundAll(Collection<Clause> rules, Set<Literal> evidence, Set<Literal> groundAtoms) {
        List<Clause> groundRules = new ArrayList<Clause>();
        Matching matching;
        Set<Constant> constantsInGroundAtoms = LogicUtils.constantsFromLiterals(groundAtoms);
        Literal constantIntroduction = new Literal("", Sugar.listFromCollections(constantsInGroundAtoms));
        if (this.deterministicLiterals != null) {
            matching = newM(new Clause(Sugar.union(this.deterministicLiterals, evidence, Sugar.list(constantIntroduction))));
        } else {
            matching = newM(new Clause(Sugar.union(evidence, groundAtoms)));
        }
        matching.setSubsumptionMode(this.subsumptionMode);
        for (Clause rule : rules) {
            Clause stub = ruleStub(rule);
            Pair<Term[], List<Term[]>> substitutions = matching.allSubstitutions(LogicUtils.flipSigns(stub), 0, Integer.MAX_VALUE);
            for (Term[] subs : substitutions.s) {
                groundRules.add(LogicUtils.substitute(rule, substitutions.r, subs));
                //System.out.println(rule+" --> "+LogicUtils.substitute(rule, substitutions.r, subs));
            }
        }

        return groundRules;
    }

    private Clause ruleStub(Clause rule) {
        Set<String> specialPredicates = Sugar.setFromCollections(SpecialBinaryPredicates.SPECIAL_PREDICATES, SpecialVarargPredicates.SPECIAL_PREDICATES);
        Set<Literal> newLiterals = new HashSet<Literal>();
        Pair<String, Integer> pair = new Pair<String, Integer>();
        for (Literal l : rule.literals()) {
            pair.set(l.predicate(), l.arity());
            if (specialPredicates.contains(l.predicate()) || deterministicPredicates.contains(pair)) {
                newLiterals.add(l);
            }
        }
        Set<Variable> variables = rule.variables();
        Literal variablesIntroduction = new Literal(SpecialVarargPredicates.TRUE, true, variables.size());
        int i = 0;
        for (Variable var : variables) {
            variablesIntroduction.set(var, i++);
        }
        newLiterals.add(variablesIntroduction);
        return new Clause(newLiterals);
    }

    private boolean isGroundClauseVacuouslyTrue(Clause c, Set<Literal> deterministic) {
        for (Literal l : c.literals()) {
            if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()) || SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())) {
                Boolean b = isSpecialGroundTrue(l);
                return b != null && b.booleanValue();
            } else if (this.deterministicPredicates.contains(new Pair<String, Integer>(l.predicate(), l.arity()))) {
                if ((!l.isNegated() && deterministic.contains(l)) || (l.isNegated() && !deterministic.contains(l.negation()))) {
                    return true;
                }
            }
        }
        return false;
    }

    private Clause removeSpecialAndDeterministicPredicates(Clause clause) {
        List<Literal> filtered = new ArrayList<Literal>();
        Set<String> specialPredicates = Sugar.setFromCollections(SpecialBinaryPredicates.SPECIAL_PREDICATES, SpecialVarargPredicates.SPECIAL_PREDICATES);
        for (Literal literal : clause.literals()) {
            if (!specialPredicates.contains(literal.predicate()) &&
                    !deterministicPredicates.contains(new Pair<String, Integer>(literal.predicate(), literal.arity()))) {
                filtered.add(literal);
            }
        }
        return new Clause(filtered);
    }

    private boolean isSpecialGroundTrue(Literal l) {
        if (SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())) {
            return specialBinaryPredicates.isTrueGround(l);
        } else if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate())) {
            return SpecialVarargPredicates.isTrueGround(l);
        }
        return false;
    }

    private Matching newM() {
        Matching m = new Matching();
        m.setSubsumptionMode(this.subsumptionMode);
        return m;
    }

    private Matching newM(Clause clause) {
        Matching m = new Matching(Sugar.<Clause>list(clause));
        m.setSubsumptionMode(this.subsumptionMode);
        return m;
    }

    public void setActiveRuleSubsampling(int numSamples) {
        this.activeRuleSubsample = numSamples;
    }

    public void setActiveRuleSubsamplingLevelStep(int levelStep) {
        this.activeRuleSubsamplingLevelStep = levelStep;
    }

    public void setMode(int mode) {
        this.mode = mode;
    }

    public void setSatSolver(SatSolver solver) {
        this.satSolver = solver;
    }

    public void setSubsumptionMode(int subsumptionMode) {
        this.subsumptionMode = subsumptionMode;
    }


    public static void main(String[] args) {


        Set<Clause> B = Sugar.set(Clause.parse("bond(X,X)"));

        Clause C = Clause.parse("s(X)");


        System.out.println(new TheorySolver().solve(B, Sugar.set(Literal.parseLiteral("!bond(a,a)"))));


//        int numDepths = 5;
//        int numPositions = 6;
//        List<Clause> theory = Sugar.<Clause>list(
//
////                Clause.parse("!cutting(key:X,pos:P,num:C),key(key:X)"),
////                Clause.parse("!cutting(key:X,pos:P,num:C),position(pos:P)"),
////                Clause.parse("!cutting(key:X,pos:P,num:C),depth(num:C)"),
//                Clause.parse("!cutting(key:X,pos:P,num:C1),!cutting(key:X,pos:P,num:C2),@eq(num:C1,num:C2)"),
//
//
////                Clause.parse("!lockCutting(lock:X,pos:P,num:C),lock(lock:X)"),
////                Clause.parse("!lockCutting(lock:X,pos:P,num:C),position(pos:P)"),
////                Clause.parse("!lockCutting(lock:X,pos:P,num:C),depth(num:C)"),
//                Clause.parse("!opens(key:K,lock:L),!cutting(key:K,pos:P,num:C),lockCutting(lock:L,pos:P,num:C)")
//
//        );
//
//        StringBuilder sb = new StringBuilder();
//        sb.append("!key(key:X),!position(pos:P),");
//        for (int i = 1; i <= numPositions; i++){
//            sb.append("cutting(key:X,pos:P,num:"+i+")");
//            if (i < numPositions){
//                sb.append(", ");
//            }
//        }
//        theory.add(Clause.parse(sb.toString()));
//
//        sb = new StringBuilder();
//        sb.append("!lock(lock:X),!position(pos:P),");
//        for (int i = 1; i <= numPositions; i++){
//            sb.append("cutting(lock:X,pos:P,num:"+i+")");
//            if (i < numPositions){
//                sb.append(", ");
//            }
//        }
//        theory.add(Clause.parse(sb.toString()));
//
//
//        //blocking rule
//        sb = new StringBuilder();
//        sb.append("opens(key:K,lock:L),");
//        for (int i = 1; i <= numPositions; i++){
//            sb.append("!cutting(key:K,pos:"+i+",num:C"+i+"), !lockCutting(lock:L,pos:"+i+",num:C"+i+")");
//            if (i < numPositions){
//                sb.append(", ");
//            }
//        }
//        theory.add(Clause.parse(sb.toString()));
//
//        //no two-equal-keys rule
//        sb = new StringBuilder();
//        sb.append("@eq(key:K1,key:K2),");
//        for (int i = 1; i <= numPositions; i++){
//            sb.append("!cutting(key:K1,pos:"+i+",num:C"+i+"), !cutting(key:K2,pos:"+i+",num:C"+i+")");
//            if (i < numPositions){
//                sb.append(", ");
//            }
//        }
//        //theory.add(Clause.parse(sb.toString()));
//
//
//        Set<Literal> deterministic = new HashSet<Literal>();
//        for (int i = 1; i <= numDepths; i++){
//            deterministic.add(Literal.parseLiteral("depth(num:"+i+")"));
//        }
//        for (int i = 1; i <= numPositions; i++){
//            deterministic.add(Literal.parseLiteral("position(pos:"+i+")"));
//        }
//
//        int numLocks = 100;
//        for (int k = 0; k < numLocks; k++){
//            deterministic.add(Literal.parseLiteral("key(key:k"+(k+1)+")"));
//            deterministic.add(Literal.parseLiteral("opens(key:k"+(k+1)+",lock:l"+(k+1)+")"));
//        }
//
//        Random random = new Random(1);
//        for (int i = 0; i < numLocks; i++){
//            deterministic.add(Literal.parseLiteral("opens(key:k"+(random.nextInt(numLocks)+1)+",lock:l"+(random.nextInt(numLocks)+1)+")"));
//        }
//
//        deterministic.add(Literal.parseLiteral("key(key:g)"));
//        for (int l = 0; l < numLocks; l++){
//            deterministic.add(Literal.parseLiteral("lock(lock:l"+(l+1)+")"));
//            deterministic.add(Literal.parseLiteral("opens(key:g,lock:l"+(l+1)+")"));
//        }
//
//
//
//        TheorySolver ps = new TheorySolver();
//        ps.mode = CUTTING_PLANES;
//        ps.activeRuleSubsample = Integer.MAX_VALUE;
//        ps.restartSequence = new IntegerFunction() {
//            @Override
//            public int f(int n) {
//                return n*n+1;
//            }
//        };
//
//        long m1 = System.currentTimeMillis();
//
//        Set<Literal> solution = ps.solve(theory, new HashSet<Literal>(), deterministic);
//        long m2 = System.currentTimeMillis();
//
//        if (solution == null){
//            System.out.println("NO SOLUTION FOUND");
//            System.exit(0);
//        }
//
//        for (Literal l : solution){
//            if (l.predicate().equals("cutting")){
//                System.out.println(l);
//            }
//        }
//
//        for (Literal l : solution){
//            if (l.predicate().equals("lockCutting")){
//                System.out.println(l);
//            }
//        }
//
//        System.out.println(solution);
//        System.out.println("TIME: "+(m2-m1)/1e3+"s");
    }

}
