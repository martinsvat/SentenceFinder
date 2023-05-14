/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package ida.ilp.logic;

import ida.ilp.logic.subsumption.CustomPredicate;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SolutionConsumer;
import ida.utils.Sugar;
import ida.utils.VectorUtils;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by kuzelkao_cardiff on 05/10/17.
 */
public class LeastHerbrandModel {

    public Set<Literal> herbrandModel(List<? extends Clause> clauses) {
        Pair<List<Clause>, List<Literal>> rulesAndFacts = rulesAndFacts(clauses);
        return herbrandModel(rulesAndFacts.r, rulesAndFacts.s);
    }

    public Set<Literal> herbrandModel(Collection<Clause> rules, Iterable<Literal> groundEvidence, Collection<Clause> hardRules) {
        Set<Literal> groundNegatedConstraints = Sugar.set();
        List<Clause> constraints = Sugar.list();
        for (Clause hardRule : hardRules) {
            if (hardRule.countLiterals() == 1 && LogicUtils.isGround(hardRule)) {
                groundNegatedConstraints.addAll(hardRule.literals());
            } else {
                constraints.add(hardRule);
            }
        }
        return herbrandModel(rules, groundEvidence, constraints, groundNegatedConstraints);
    }

    // should be generalized somehow
    public Set<Literal> herbrandModel(Collection<Clause> rules, Iterable<Literal> groundEvidence, Collection<Clause> hardRules, Collection<Literal> groundNegatedConstraints) {
        // hard rules have only negative literals!
        for (Clause constraint : hardRules) {
            if (LogicUtils.positiveLiterals(constraint).size() > 0) {
                throw new IllegalStateException("Hard rules are supposed to be constraints only (no positive literals).");
            }
        }
        hardRules = hardRules.stream().map(LogicUtils::flipSigns).collect(Collectors.toList());

        MultiMap<Pair<String, Integer>, Literal> herbrand = new MultiMap<Pair<String, Integer>, Literal>();

        Set<Pair<String, Integer>> headSignatures = new HashSet<Pair<String, Integer>>();
        for (Clause rule : rules) {
            Literal head = head(rule);
            Pair<String, Integer> headSignature = new Pair<String, Integer>(head.predicate(), head.arity());
            headSignatures.add(headSignature);
            herbrand.set(headSignature, new HashSet<Literal>());
        }

        for (Literal groundLiteral : groundEvidence) {
            herbrand.put(new Pair<String, Integer>(groundLiteral.predicate(), groundLiteral.arity()), groundLiteral);
        }

        List<Literal> groundBanned = groundNegatedConstraints.stream().map(Literal::negation).collect(Collectors.toList());

        boolean changed;
        do {
            int herbrandSize0 = VectorUtils.sum(herbrand.sizes());
            Clause cWorld = new Clause(Sugar.flatten(herbrand.values()));
            Matching matching = new Matching(Sugar.list(cWorld));

            for (Literal l : groundBanned) {
                if (cWorld.containsLiteral(l)) {
                    return null;
                }
            }

            for (Clause constraint : hardRules) {
                if (matching.subsumption(constraint, 0)) {
                    // there is some constraint violated
                    return null;
                }
            }

            for (Pair<String, Integer> predicate : headSignatures) {
                //may overwrite the previous ones which is actually what we want
                matching.getEngine().addCustomPredicate(new TupleNotIn(predicate.r, predicate.s, herbrand.get(predicate)));
            }
            for (Clause rule : rules) {
                Literal head = head(rule);
                Pair<String, Integer> headSignature = new Pair<String, Integer>(head.predicate(), head.arity());
                SolutionConsumer solutionConsumer = new HerbrandSolutionConsumer(head, headSignature, herbrand);
                matching.getEngine().addSolutionConsumer(solutionConsumer);
                if (LogicUtils.isGround(head)) {
                    Clause query = new Clause(flipSigns(rule.literals()));
                    if (matching.subsumption(query, 0)) {
                        herbrand.put(headSignature, head);
                    }
                } else {
                    Clause query = new Clause(flipSigns(Sugar.union(rule.literals(), new Literal(tupleNotInPredicateName(head.predicate(), head.arity()), true, head.arguments()))));
                    matching.allSubstitutions(query, 0, Integer.MAX_VALUE); // Ondra psal pres email ze to nize muze skoncit v nekonecne smycce
//                    Pair<Term[], List<Term[]>> substitutions;
//                    do {
//                 //       not super optimal but the rule grounding will dominate the runtime anyway...
//                        substitutions = matching.allSubstitutions(query, 0, 512);
//                    } while (substitutions.s.size() > 0);
                }
                matching.getEngine().removeSolutionConsumer(solutionConsumer);
            }
            int herbrandSize1 = VectorUtils.sum(herbrand.sizes());
            changed = herbrandSize1 > herbrandSize0;
        } while (changed);
        return Sugar.setFromCollections(Sugar.flatten(herbrand.values()));
    }


    public Set<Literal> herbrandModel(Collection<Clause> rules, Collection<Literal> groundEvidence) {
        return herbrandModel(rules, groundEvidence, Sugar.set());
    }

    private Literal head(Clause c) {
        for (Literal l : c.literals()) {
            if (!l.isNegated()) {
                return l;
            }
        }
        return null;
    }

    private static List<Literal> flipSigns(Iterable<Literal> c) {
        List<Literal> lits = new ArrayList<Literal>();
        for (Literal l : c) {
            lits.add(l.negation());
        }
        return lits;
    }

    private Pair<List<Clause>, List<Literal>> rulesAndFacts(List<? extends Clause> clauses) {
        List<Literal> groundFacts = new ArrayList<Literal>();
        List<Clause> rest = new ArrayList<Clause>();
        for (Clause c : clauses) {
            if (c.countLiterals() == 1 && LogicUtils.isGround(c)) {
                groundFacts.add(Sugar.chooseOne(c.literals()));
            } else {
                rest.add(c);
            }
        }
        return new Pair<List<Clause>, List<Literal>>(rest, groundFacts);
    }

    private static String tupleNotInPredicateName(String predicate, int arity) {
        return "@tuplenotin-" + predicate + "/" + arity;
    }


    private class HerbrandSolutionConsumer implements SolutionConsumer {

        private Literal head;

        private Pair<String, Integer> headSignature;

        private MultiMap<Pair<String, Integer>, Literal> herbrand;

        private HerbrandSolutionConsumer(Literal head, Pair<String, Integer> headSignature, MultiMap<Pair<String, Integer>, Literal> herbrand) {
            this.head = head;
            this.headSignature = headSignature;
            this.herbrand = herbrand;
        }

        @Override
        public void solution(Term[] template, Term[] solution) {
            herbrand.put(headSignature, LogicUtils.substitute(head, template, solution));
        }
    }

    private class TupleNotIn implements CustomPredicate {

        private Set<Literal> literals;

        private String name;

        private String predicate;

        TupleNotIn(String predicate, int arity, Set<Literal> literals) {
            this.predicate = predicate;
            this.name = tupleNotInPredicateName(predicate, arity);
            this.literals = literals;
        }

        @Override
        public String name() {
            return name;
        }

        @Override
        public boolean isSatisfiable(Term... arguments) {
            if (Sugar.countNulls(arguments) > 0) {
                return true;
            }
            //System.out.println("? "+!literals.contains(new Literal(predicate, arguments))+" -- "+new Literal(predicate, arguments)+" -- "+literals);
            return !literals.contains(new Literal(predicate, arguments));
        }
    }

    public static void main(String[] args) {
//        List<Clause> clauses = Sugar.list(Clause.parse("ahoj(a)"),
//        Clause.parse("q(X), !ahoj(X)"), Clause.parse("ahoj(X),!q(X)"));
        List<Clause> clauses = Sugar.list(Clause.parse("ahoj(a)"),
                Clause.parse("q(X), !ahoj(X)"));
        System.out.println(new LeastHerbrandModel().herbrandModel(clauses));
    }


}