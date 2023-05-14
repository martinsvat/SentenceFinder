/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/*
 * LogicUtils.java
 *
 * Created on 12. leden 2008, 17:35
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package ida.ilp.logic;

import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.sentences.caches.LiteralsCache;
import ida.utils.Sugar;
import ida.utils.collections.Counters;
import ida.utils.collections.FakeMap;
import ida.utils.collections.ValueToIndex;
import ida.utils.hypergraphs.Hypergraph;
import ida.utils.hypergraphs.HypergraphUtils;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * Class harbouring several useful methods for manipulation with Clauses, Literals and Terms
 *
 * @author Ondra
 */
public class LogicUtils {

    private static boolean pseudoPrologNotation = false;
    private static boolean trimTicks = true;

    /**
     * Creates a new instance of LogicUtils
     */
    private LogicUtils() {
    }

    /**
     * Constructs a new variable which is not contained iterable the given clause.
     *
     * @param c clause that is used to constrain the possible new variables - the new variable cannot be contained iterable it
     * @return new variable which is not contained iterable Clause c
     */
    public static Variable freshVariable(Clause c) {
        return freshVariable(c.variables(), 0);
    }

    /**
     * Constructs a new variable which is not contained iterable the given set of variables.
     *
     * @param variables set of variables that is used to constrain the possible new variables - the new variable cannot be contained iterable it
     * @return
     */
    public static Variable freshVariable(Set<Variable> variables) {
        return freshVariable(variables, 0);
    }

    /**
     * Constructs a new variable which is not contained iterable the given set of variables. The name of the variable will be
     * Vi where i >= index and Vi is not jet contained iterable the set <em>variables</em>,
     *
     * @param variables set of variables that is used to constrain the possible new variables - the new variable cannot be contained iterable it
     * @param index     the index from which the name of the new variable should be searched for.
     * @return
     */
    public static Variable freshVariable(Set<Variable> variables, int index) {
        Variable var = null;
        do {
            var = Variable.construct("V" + (index++));
        } while (variables.contains(var));
        return var;
    }

    // todo: extend this to functionality with Set<Variable> variables (alreadyIn) as the other methods work with
    public static List<Variable> freshVariables(Map<Pair<Predicate, Integer>, String> typing, Predicate predicate) {
        if (null == typing) {
            return Sugar.listFromCollections(freshVariables(Sugar.set(), predicate.getArity()));
        }
        List<Variable> retVal = Sugar.list();
        for (int idx = 0; idx < predicate.getArity(); idx++) {
            retVal.add(Variable.construct("V" + idx, typing.get(new Pair<>(predicate, idx))));
        }
        return retVal;
    }

    public static List<Variable> freshVariables(Collection<Variable> alreadyIn, Map<Pair<Predicate, Integer>, String> typing, Predicate predicate) {
        List<Variable> retVal = Sugar.list();
        Set<String> namesTaken = alreadyIn.stream().map(Variable::name).collect(Collectors.toSet());
        int order = namesTaken.size();
        for (int idx = 0; idx < predicate.getArity(); idx++) {
            while (namesTaken.contains("V" + order)) {
                order++;
            }
            retVal.add(Variable.construct("V" + order, typing.get(new Pair<>(predicate, idx))));
            namesTaken.add("V" + order);
        }
        return retVal;
    }


    public static Set<Variable> freshVariables(Set<Variable> variables, int num) {
        Set<Variable> retVal = new HashSet<Variable>();
        Set<Variable> all = new HashSet<Variable>(variables);
        for (int i = 0; i < num; i++) {
            Variable v = freshVariable(all, i + 1 + variables.size());
            all.add(v);
            retVal.add(v);
        }
        return retVal;
    }

    /**
     * Converts a PrologList containing just instances of class Function into a Clause
     *
     * @param pl PrologList containing just instances of class Function
     * @return clause constructed from the set of function symbols (using the method toLiteral of class Function)
     */
    public static Clause clauseFromFunctionsList(PrologList pl) {
        Set<Literal> literals = new HashSet<Literal>();
        for (int i = 0; i < pl.countItems(); i++) {
            Function f = (Function) pl.get(i);
            literals.add(f.toLiteral());
        }
        return new Clause(literals);
    }

    /**
     * Creates a clause from Clause c iterable which all occurences of Term a are replaced by Term b
     *
     * @param c the clause
     * @param a the term to be replaced
     * @param b the term by which it should be replaced
     * @return new clause with substituted values
     */
    public static Clause substitute(Clause c, Term a, Term b) {
        return substitute(c, new Term[]{a}, new Term[]{b});
    }


    public static Literal substitute(Literal l, Term a, Term b) {
        return substitute(l, new Term[]{a}, new Term[]{b});
    }

    /**
     * Creates a new literal from l iterable which all occurences of Terms from source are replaced by respective Terms iterable image
     *
     * @param l      the literal
     * @param source the terms to be replaced
     * @param image  the terms by which they should be replaced
     * @return the new substituted literal
     */
    public static Literal substitute(Literal l, Term[] source, Term[] image) {
        Map<Term, Term> substitution = new HashMap<Term, Term>();
        for (int i = 0; i < source.length; i++) {
            substitution.put(source[i], image[i]);
        }
        return substitute(l, substitution);
    }

    /**
     * Creates a new Literal from Literal l by substituting values according to a substitution represented
     * by the Map substitution. For each pair "key"-"value" iterable the Map, all occurences of "key" are replaced by
     * "value".
     *
     * @param l            the literal
     * @param substitution the substitution represented as Map
     * @return the substituted literal
     */
    public static Literal substitute(Literal l, Map<Term, Term> substitution) {
        Literal newLiteral = new Literal(l.predicate(), l.isNegated(), l.arity());
        for (int i = 0; i < l.arity(); i++) {
//            if (substitution.containsKey(l.get(i))) {
//                newLiteral.set(substitution.get(l.get(i)), i);
//            } else {
//                newLiteral.set(l.get(i), i);
//            }
            newLiteral.set(substitute(l.get(i), substitution), i);
        }
        return newLiteral;
    }

    /**
     * Removes enclosing apostrophes (quotes) from a term
     *
     * @param term the term to be unquoted
     * @return Term with removed apostrophes (quotes)
     */
    public static Term unquote(Term term) {
        String name = term.name();
        if (name.length() > 0 && name.charAt(0) == '\'' && name.charAt(name.length() - 1) == '\'') {
            name = name.substring(1, name.length() - 1);
        }
        return ParserUtils.parseTerm(name.toCharArray(), 0, ')', new HashMap<Variable, Variable>(), new HashMap<Constant, Constant>()).r;
    }

    /**
     * Creates a nice variable name for a given id. For example, for id = 0, we get
     * A, for id = 1 we get B... then A1, ..., Z1, A2,... etc.
     *
     * @param id unique identifier of variable
     * @return string which is a name of the variable assigned to the given id
     */
    public static String niceVariableName(int id) {
        if (id <= ((int) 'Z' - (int) 'A')) {
            return String.valueOf((char) ((int) 'A' + id));
        } else {
            return String.valueOf((char) ((int) 'A' + id % ((int) 'Z' - (int) 'A'))) + (id / ((int) 'Z' - (int) 'A'));
        }
    }

    /**
     * Creates a new clause iterable which it replaces all terms iterable a clause by the respective variables (basically it makes the
     * first letters of constants upper-case and replaces them by instances of class Variable).
     *
     * @param c the clause
     * @return the new variabilized clause
     */
    public static Clause variabilizeClause(Clause c) {
        return variabilizeClause(c, null);
    }

    public static Clause variabilizeClause(Clause c, Clause template) {
        System.out.println("todo: add types here!");
        Map<Pair<String, Integer>, Literal> map = new HashMap<Pair<String, Integer>, Literal>();
        if (template != null) {
            for (Literal l : template.literals()) {
                map.put(new Pair<String, Integer>(l.predicate(), l.arity()), l);
            }
        }
        Map<Term, Term> substitution = new HashMap<Term, Term>();
        Set<Variable> usedVariables = new HashSet<Variable>(c.variables());
        Pair<String, Integer> query = new Pair<String, Integer>();
        int freshVariableIndex = 1;
        for (Literal l : c.literals()) {
            query.set(l.predicate(), l.arity());
            Literal templateLit = map.get(query);
            for (int i = 0; i < l.arity(); i++) {
                if ((template == null || !templateLit.get(i).name().equals("#")) && l.get(i) instanceof Constant && !substitution.containsKey(l.get(i))) {
                    Variable newVar = toVariable(l.get(i));
                    if (usedVariables.contains(newVar)) {
                        newVar = LogicUtils.freshVariable(usedVariables, freshVariableIndex++);
                    }
                    substitution.put(l.get(i), newVar);
                    usedVariables.add(newVar);
                }
            }
        }
        return LogicUtils.substitute(c, substitution);
    }

    /**
     * Basically, it makes every first letter of a term an upper case, so it becomes a variable, and returns such obtained variable.
     *
     * @param literal
     * @return
     */
    public static Literal variabilizeLiteral(Literal literal) {
        return new Literal(literal.predicate(),
                literal.isNegated(),
                literal.argumentsStream().map(LogicUtils::toVariable).collect(Collectors.toList()));
    }

    public static Variable toVariable(Term term) {
        return Variable.construct(Sugar.firstCharacterToUpperCase(term.name()), term.type());
    }

    public static Variable toVariable(Term term, String type) {
        return Variable.construct(Sugar.firstCharacterToUpperCase(term.name()), type);
    }

    public static Constant toConstant(Term term) {
        return Constant.construct(Sugar.firstCharacterToLowerCase(term.name()), term.type());
    }

    public static Constant toConstant(Term term, String type) {
        return Constant.construct(Sugar.firstCharacterToLowerCase(term.name()), type);
    }

    public static Term parseTerm(String s) {
        s = s.trim();
        if (s.charAt(0) == '[') {
            return Function.parseFunction(s, new FakeMap<Variable, Variable>(), new FakeMap<Constant, Constant>());
        } else if (Character.isLowerCase(s.charAt(0))) {
            return Constant.construct(s);
        } else {
            return Variable.construct(s);
        }
    }

    /**
     * Creates a new clause iterable which it replaces all terms iterable a clause by the respective variables (basically it makes the
     * first letters of variables lower-case and replaces them by instances of class Constant).
     *
     * @param c the clause
     * @return the new "constantized" clause
     */
    public static Clause constantizeClause(Clause c) {
        Set<Literal> literals = new LinkedHashSet<>();
        for (Literal l : c.literals()) {
            literals.add(constantize(l));
        }
        return new Clause(literals);
    }

    public static Literal constantize(Literal l) {
        Literal newPred = new Literal(l.predicate(), l.isNegated(), l.arity());
        for (int i = 0; i < l.arity(); i++) {
            newPred.set(Constant.construct(Sugar.firstCharacterToLowerCase(l.get(i).name()), l.get(i).type()), i);
        }
        return newPred;
    }

    /**
     * Creates a list of predicate names which are not contained iterable Clause c. The list
     * will contain "count" elements.
     *
     * @param c     Clause which is used to constrain the possible predicate names - predicate already contained
     *              iterable c cannto be contained iterable the generated list.
     * @param count number of predicate names to be generated
     * @return list of new predicate names
     */
    public static List<String> freshPredicateNames(Clause c, int count) {
        List<String> retVal = new ArrayList<String>();
        for (int i = 0; i < Integer.MAX_VALUE; i++) {
            if (retVal.size() == count) {
                break;
            }
            String pred = "pred_" + i;
            if (c.getLiteralsByPredicate(pred).isEmpty()) {
                retVal.add("pred" + i);
            }
        }
        return retVal;
    }

    public static List<String> freshPredicateNames(Set<String> c, int count) {
        List<String> retVal = new ArrayList<String>();
        for (int i = 0; i < Integer.MAX_VALUE; i++) {
            if (retVal.size() == count) {
                break;
            }
            String pred = "pred_" + i;
            if (!c.contains(pred)) {
                retVal.add("pred" + i);
            }
        }
        return retVal;
    }

    /**
     * Checks if the given clause is ground (a clause is ground if it contains no variables)
     *
     * @param c clause to be checked
     * @return true if c contains no variables, false otherwise
     */
    public static boolean isGround(Clause c) {
        return c.variables().isEmpty();
    }

    public static boolean isGround(Literal l) {
        for (int i = 0; i < l.arity(); i++) {
            if (l.get(i) instanceof Variable) {
                return false;
            }
        }
        return true;
    }

    /**
     * Given two Clauses a and b, it constructs two new equivalent clauses which
     * do not share any variables.
     *
     * @param a the first clause
     * @param b the second clause
     * @return pair of Clauses (x,y) such that the intersection of a.variables() and b.variables() is empty
     */
    public static Pair<Clause, Clause> standardizeApart(Clause a, Clause b) {
        Pair<Clause, Clause> retVal = new Pair<Clause, Clause>();
        int i = 0;
        for (Clause c : standardizeApart(Sugar.list(a, b))) {
            if (i == 0) {
                retVal.r = c;
            } else {
                retVal.s = c;
            }
            i++;
        }
        return retVal;
    }

    /**
     * Given two Clauses a and b, it constructs two new equivalent clauses which
     * do not share any variables.
     *
     * @param clauses the clauses which should be standardized apart
     * @return collection of Clauses such that for any two a, b of them, the intersection of a.variables() and b.variables() is empty
     */
    public static Collection<Clause> standardizeApart(Collection<Clause> clauses) {
        List<Clause> retVal = new ArrayList<Clause>();
        Map<Pair<Variable, Integer>, Variable> vars = new HashMap<Pair<Variable, Integer>, Variable>();
        Set<Variable> allVariables = new HashSet<Variable>();
        for (Clause c : clauses) {
            for (Variable v : c.variables()) {
                allVariables.add(v);
            }
        }
        int i = 0;
        for (Clause c : clauses) {
            Set<Literal> literals = new HashSet<Literal>();
            Pair<Variable, Integer> queryPair = new Pair<Variable, Integer>();
            for (Literal l : c.literals()) {
                Literal newLiteral = new Literal(l.predicate(), l.isNegated(), l.arity());
                for (int j = 0; j < l.arity(); j++) {
                    if (l.get(j) instanceof Variable) {
                        queryPair.set((Variable) l.get(j), i);
                        Variable var = null;
                        if ((var = vars.get(queryPair)) == null) {
                            Pair<Variable, Integer> insertPair = new Pair<Variable, Integer>(queryPair.r, queryPair.s);
                            var = freshVariable(allVariables);
                            allVariables.add(var);
                            vars.put(insertPair, var);
                        }
                        newLiteral.set(var, j);
                    } else {
                        newLiteral.set(l.get(j), j);
                    }
                }
                literals.add(newLiteral);
            }
            retVal.add(new Clause(literals));
            i++;
        }
        return retVal;
    }

    public static boolean isTreelike(Clause c) {
        return HypergraphUtils.isTreelike(clause2hypergraph(c));
    }

    public static boolean isAcyclic(Clause c) {
        return HypergraphUtils.isAcyclic(clause2hypergraph(c));
    }

    private static Hypergraph clause2hypergraph(Clause c) {
        ValueToIndex<Variable> vertexIDs = new ValueToIndex<Variable>();
        ValueToIndex<Set<Integer>> edgeIDs = new ValueToIndex<Set<Integer>>();
        Hypergraph h = new Hypergraph();
        for (Literal l : c.literals()) {
            Set<Integer> edge = new HashSet<Integer>();
            for (int i = 0; i < l.arity(); i++) {
                if (l.get(i) instanceof Variable) {
                    edge.add(vertexIDs.valueToIndex((Variable) l.get(i)));
                }
            }
            h.addEdge(edgeIDs.valueToIndex(edge), edge);
        }
        return h;
    }

    public static Clause randomlyRenameVariables(Clause clause, int newVariableIndex) {
        return randomlyRenameVariables(clause, newVariableIndex, new Random());
    }

    public static Clause randomlyRenameVariables(Clause clause, int newVariableIndex, Random random) {
        List<Variable> newVariables = new ArrayList<Variable>();
        int numVariables = clause.variables().size();
        for (int i = 0; i < numVariables; i++) {
            newVariables.add(Variable.construct(niceVariableName(newVariableIndex + i)));
        }
        Collections.shuffle(newVariables, random);
        Map<Term, Term> substitution = new HashMap<Term, Term>();
        int index = 0;
        for (Variable oldVar : clause.variables()) {
            substitution.put(oldVar, newVariables.get(index++));
        }
        return substitute(clause, substitution);
    }

    public static Clause randomlyRenameConstants(Clause clause, int newConstantIndex) {
        return randomlyRenameConstants(clause, newConstantIndex, new Random());
    }

    public static Clause randomlyRenameConstants(Clause clause, int newConstantIndex, Random random) {
        List<Constant> newConstants = new ArrayList<Constant>();
        int numConstants = 0;
        for (Term term : clause.terms()) {
            if (term instanceof Constant) {
                numConstants++;
            }
        }
        for (int i = 0; i < numConstants; i++) {
            newConstants.add(Constant.construct(niceVariableName(newConstantIndex + i).toLowerCase()));
        }
        Collections.shuffle(newConstants, random);
        Map<Term, Term> substitution = new HashMap<Term, Term>();
        int index = 0;
        for (Term oldTerm : clause.terms()) {
            if (oldTerm instanceof Constant) {
                substitution.put(oldTerm, newConstants.get(index++));
            }
        }
        return substitute(clause, substitution);
    }

    public static Set<Variable> variables(Collection<Clause>... clauses) {
        Set<Variable> retVal = new HashSet<Variable>();
        for (Collection<Clause> clauseColl : clauses) {
            for (Clause c : clauseColl) {
                retVal.addAll(c.variables());
            }
        }
        return retVal;
    }

    public static Set<Term> terms(Collection<Clause>... clauses) {
        Set<Term> retVal = new HashSet<Term>();
        for (Collection<Clause> clauseColl : clauses) {
            for (Clause c : clauseColl) {
                retVal.addAll(c.terms());
            }
        }
        return retVal;
    }

    public static Set<String> predicateNamesOfLiterals(Collection<Literal>... literals) {
        Set<String> retVal = new HashSet<String>();
        for (Collection<Literal> literalColl : literals) {
            for (Literal l : literalColl) {
                retVal.add(l.predicate());
            }
        }
        return retVal;
    }

    public static Set<Pair<String, Integer>> predicates(Collection<Clause> clauses) {
        return predicates(clauses, false);
    }

    public static Set<Pair<String, Integer>> predicates(Collection<Clause> clauses, boolean ignoreSpecialPredicates) {
        Set<Pair<String, Integer>> retVal = new HashSet<Pair<String, Integer>>();
        for (Clause c : clauses) {
            retVal.addAll(predicates(c, ignoreSpecialPredicates));
        }
        return retVal;
    }

    public static Set<Pair<String, Integer>> predicates(Clause c) {
        return predicates(c, false);
    }

    public static Set<Pair<String, Integer>> predicates(Clause c, boolean ignoreSpecialPredicates) {
        Set<Pair<String, Integer>> retVal = new HashSet<Pair<String, Integer>>();
        for (Literal l : c.literals()) {
            if (!ignoreSpecialPredicates || (!SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate()) && !SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()))) {
                retVal.add(new Pair<String, Integer>(l.predicate(), l.arity()));
            }
        }
        return retVal;
    }

    public static Set<String> predicateNames(Collection<Clause>... clauses) {
        Set<String> retVal = new HashSet<String>();
        for (Collection<Clause> clauseColl : clauses) {
            for (Clause c : clauseColl) {
                retVal.addAll(c.predicates());
            }
        }
        return retVal;
    }

    public static Set<Literal> atoms(Clause clause) {
        Set<Literal> retVal = new HashSet<Literal>();
        for (Literal l : clause.literals()) {
            if (l.isNegated()) {
                retVal.add(l.negation());
            } else {
                retVal.add(l);
            }
        }
        return retVal;
    }

    public static Set<Literal> atoms(Collection<Clause>... clauses) {
        Set<Literal> retVal = new HashSet<Literal>();
        for (Collection<Clause> clauseColl : clauses) {
            for (Clause c : clauseColl) {
                retVal.addAll(atoms(c));
            }
        }
        return retVal;
    }

    public static boolean isGround(Collection<Clause>... clauses) {
        for (Collection<Clause> clauseColl : clauses) {
            for (Clause c : clauseColl) {
                if (!isGround(c)) {
                    return false;
                }
            }
        }
        return true;
    }

    public static List<Clause> flipSignsClauses(Collection<Clause> clauses) {
        return clauses.stream().map(LogicUtils::flipSigns).collect(Collectors.toList());
    }

    public static Clause flipSigns(Clause c) {
        List<Literal> literals = new ArrayList<Literal>(c.countLiterals());
        // tady udelat optimalizaci napr
        for (Literal l : c.literals()) {
            literals.add(l.negation());
        }
        return new Clause(literals);
    }

    public static List<Literal> flipSigns(Collection<Literal> literals) {
        List<Literal> retVal = new ArrayList<Literal>();
        for (Literal l : literals) {
            retVal.add(l.negation());
        }
        return retVal;
    }

    /**
     * Note here that it suppose a flat substitution, i.e. no substitution chains are supported. For such behavior, you must flatten the substitution first.
     *
     * @param term
     * @param substitution
     * @return
     */
    public static Term substitute(Term term, Map<? extends Term, ? extends Term> substitution) {
        Map<Term, Term> subs = new HashMap<Term, Term>();
        if (term instanceof Constant) {
            return term;
        } else if (term instanceof Variable) {
            return substitution.containsKey(term) ? substitution.get(term) : term;
        } else if (term instanceof Function) {
            Function func = (Function) term;
            Term[] args = new Term[func.arity()];
            for (int argIdx = 0; argIdx < func.arity(); argIdx++) {
                args[argIdx] = substitute(func.get(argIdx), substitution);
            }
            return new Function(func.name(), args);
        }
        throw new IllegalStateException("Not known instance of Term.");
    }


    public static Clause substitute(Clause c, Term[] variables, Term[] terms) {
        Map<Term, Term> subs = new HashMap<Term, Term>();
        for (int i = 0; i < variables.length; i++) {
            subs.put(variables[i], terms[i]);
        }
        return substitute(c, subs);
    }

    public static Clause substitute(Clause c, Map<? extends Term, ? extends Term> substitution) {
        Set<Literal> literals = new HashSet<Literal>();
        for (Literal l : c.literals()) {
            Literal cl = ((Literal) l).copy();
            for (int j = 0; j < l.arity(); j++) {
                if (substitution.containsKey(l.get(j))) {
                    cl.set(substitution.get(l.get(j)), j);
                } else if (l.get(j) instanceof Function) {
                    cl.set(substitute(l.get(j), substitution), j);
                }
            }
            literals.add(cl);
        }
        return new Clause(c.getQuantifier(), literals);
    }


    // this is not parallel friendly :(
    public static void substituteStatefullyPreparation(Term[] variables) {
        for (int idx = 0; idx < variables.length; idx++) {
            ((Variable) variables[idx]).setStatefullIndex(idx);
        }
    }


    // this method assumes that variables has set up the index their are in the given by substituteStatefullyPreparation
    /*public static Clause substituteStatefully(Clause c, Term[] variables, Term[] terms){

    }*/

    // this is not parallel friendly :(
    // this method assumes that variables has set up the index their are in the given by substituteStatefullyPreparation
    public static List<Literal> substituteStatefully(Clause c, Term[] terms, boolean removeSpecialPredicates) {
        List<Literal> retVal = new ArrayList<>(c.countLiterals());
        for (Literal literal : c.literals()) {
            if (removeSpecialPredicates && (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(literal.predicate()) || SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(literal.predicate()))) {
                continue;
            }
            retVal.add(substituteStatefully(literal, terms));
        }
        return retVal;
    }

    // this method assumes that variables has set up the index their are in the given by substituteStatefullyPreparation
    public static Literal substituteStatefully(Literal l, Term[] terms) {
        Literal newLiteral = new Literal(l.predicate(), l.isNegated(), l.arity());
        for (int idx = 0; idx < l.arity(); idx++) {
            Term argument = l.get(idx);
            if (argument instanceof Variable) {
                newLiteral.set(terms[((Variable) argument).getStatefullIndex()], idx);
            } else {
                newLiteral.set(argument, idx);
            }
        }
        return newLiteral;
    }

    public static boolean isModelOf(Set<Literal> possibleWorld, Clause clause) {
        for (Literal l : clause.literals()) {
            if (possibleWorld.contains(l)) {
                return true;
            }
        }
        return false;
    }

    public static boolean isModelOf(Set<Literal> possibleWorld, Collection<Clause> theory) {
        for (Clause c : theory) {
            if (!isModelOf(possibleWorld, c)) {
                return false;
            }
        }
        return true;
    }

    public static Literal termToLiteral(Term term) {
        if (term instanceof Constant) {
            return new Literal(term.name());
        } else if (term instanceof Function) {
            return ((Function) term).toLiteral();
        } else if (term instanceof Variable) {
            throw new IllegalArgumentException("Variables cannot be converted into literals.");
        } else {
            throw new IllegalArgumentException("Only constants and functions supported.");
        }
    }

    public static Set<Constant> constantsFromLiterals(Collection<Literal> literals) {
        Set<Constant> retVal = new HashSet<Constant>();
        for (Literal literal : literals) {
            retVal.addAll(constantsFromLiteral(literal));
        }
        return retVal;
    }

    // as most of the methods, it does not look into function
    public static Set<Constant> constantsFromLiteral(Literal literal) {
        Set<Constant> retVal = new HashSet<Constant>();
        for (Term t : literal.terms()) {
            if (t instanceof Constant) {
                retVal.add((Constant) t);
            }
        }
        return retVal;
    }


    public static Set<Constant> constants(Term[] substitution) {
        Set<Constant> retVal = Sugar.set();
        for (Term term : substitution) {
            if (term instanceof Constant) {
                retVal.add((Constant) term);
            }
        }
        return retVal;
    }

    public static Set<Constant> constants(Clause c) {
        Set<Constant> retVal = new HashSet<Constant>();
        for (Term t : c.terms()) {
            if (t instanceof Constant) {
                retVal.add((Constant) t);
            }
        }
        return retVal;
    }

    public static Set<Constant> constants(Collection<Clause> coll) {
        Set<Constant> retVal = new HashSet<Constant>();
        for (Clause c : coll) {
            retVal.addAll(constants(c));
        }
        return retVal;
    }


    private static Literal literalTemplate(Literal l) {
        int j = 0;
        Literal normalized = new Literal(l.predicate(), l.isNegated(), l.arity());
        for (int i = 0; i < l.arity(); i++) {
            if (l.get(i) instanceof Variable) {
                Variable v = (Variable) l.get(i);
                normalized.set(Variable.construct("V" + (j++), v.type()), i);
            } else {
                normalized.set(l.get(i), i);
            }
        }
        return normalized;
    }

    public static Set<Literal> allGroundAtoms(Collection<Clause> clauses) {
        return allGroundAtoms_impl(clauses, new HashSet<Constant>());
    }

    public static Set<Literal> allGroundAtoms(Collection<Pair<String, Integer>> predicates, Collection<Constant> constants) {
        List<Clause> clauses = new ArrayList<Clause>();
        for (Pair<String, Integer> p : predicates) {
            clauses.add(new Clause(newLiteral(p.r, p.s)));
        }
        return allGroundAtoms_impl(clauses, constants);
    }

    private static Set<Literal> allGroundAtoms_impl(Collection<Clause> clauses, Collection<Constant> constants) {
        Set<Literal> retVal = new HashSet<Literal>();
        Set<Constant> constantSet = new HashSet<Constant>();
        constantSet.addAll(constants);
        for (Clause c : clauses) {
            constantSet.addAll(constants(c));
        }
        Literal lit = new Literal("", true, constantSet.size());
        int i = 0;
        for (Constant c : constantSet) {
            lit.set(c, i++);
        }
        Set<Literal> normalized = new HashSet<Literal>();
        //not optimal but not a bottleneck
        for (Clause c : clauses) {
            for (Literal l : c.literals()) {
                normalized.add(literalTemplate(l));
            }
        }
        Matching m = new Matching(Sugar.list(new Clause(lit)));
        for (Literal l : normalized) {
            if (!l.isNegated()) {
                l = l.negation();
            }
            Pair<Term[], List<Term[]>> p = m.allSubstitutions(new Clause(l), 0, Integer.MAX_VALUE);
            for (Term[] subs : p.s) {
                retVal.add(substitute(l, p.r, subs).negation());
            }
        }
        return retVal;
    }

    public static Set<Clause> allGroundings(Collection<Clause> clauses, Collection<Constant> constants) {
        Set<Clause> retVal = new HashSet<Clause>();
        Literal lit = new Literal("", true, constants.size());
        int i = 0;
        for (Constant c : constants) {
            lit.set(c, i++);
        }
        Matching m = new Matching(Sugar.list(new Clause(lit)));
        for (Clause c : clauses) {
            Literal template = new Literal("l", true, c.variables().size());
            i = 0;
            for (Variable v : c.variables()) {
                template.set(v, i++);
            }
            Pair<Term[], List<Term[]>> p = m.allSubstitutions(new Clause(template), 0, Integer.MAX_VALUE);
            for (Term[] subs : p.s) {
                retVal.add(substitute(c, p.r, subs));
            }
        }
        return retVal;
    }

    public static Literal newLiteral(String predicate, int arity) {
        Literal l = new Literal(predicate, arity);
        for (int i = 0; i < arity; i++) {
            l.set(Variable.construct("V" + i), i);
        }
        return l;
    }

    public static Literal newLiteral(Predicate predicate, Set<Variable> variables) {
        return newLiteral(predicate.getName(), predicate.getArity(), variables);
    }


    public static Literal newLiteral(String predicate, int arity, Collection<Variable> freshVariables) {
        Literal l = new Literal(predicate, arity);
        int i = 0;
        for (Variable v : freshVariables) {
            l.set(v, i);
            i++;
            if (i >= arity) {
                break;
            }
        }
        return l;
    }

    public static Clause induced(Clause clause, Set<? extends Term> terms) {
        List<Literal> literals = new ArrayList<Literal>();
        outerLoop:
        for (Literal l : clause.literals()) {
            for (int i = 0; i < l.arity(); i++) {
                if (!terms.contains(l.get(i))) {
                    continue outerLoop;
                }
            }
            literals.add(l);
        }
        return new Clause(literals);
    }

    public static Collection<Literal> allSubstitution(Literal literal, Set<Constant> constants) {
        List<Variable> variables = Sugar.listFromCollections(variables(literal));
        List<Literal> accumulator = Sugar.list();
        Map<Term, Term> map = new HashMap<>();
        allSubstitutionFinder(0, variables, constants, map, accumulator, literal);
        return accumulator;
    }

    private static void allSubstitutionFinder(int variableIdx, List<Variable> variables, Set<Constant> constants, Map<Term, Term> substitution, List<Literal> accumulator, Literal literal) {
        if (variableIdx >= variables.size()) {
            accumulator.add(substitute(literal, substitution));
            return;
        }
        Variable variable = variables.get(variableIdx);
        for (Constant constant : constants) {
            if ((null == constant.type() && null == variable.type())
                    || (null != variable.type() && variable.type().equals(constant.type()))) {
                substitution.put(variable, constant);
                allSubstitutionFinder(variableIdx + 1, variables, constants, substitution, accumulator, literal);
                //substitution.remove(variable); no needed
            }
        }
    }

    /* old version
    // generalize to term
    public static Set<Literal> allSubstitution(Literal literal, Set<Constant> constants) {
        List<Variable> variables = Sugar.listFromCollections(variables(literal));
        tady to udelat chytreji pro ten typovany priklad :))
        return Combinatorics.variationsWithRepetition(constants, variables.size())
                .stream()
                .map(variation -> {
                    Map<Term, Term> map = new HashMap<>();
                    IntStream.range(0, variables.size())
                            .forEach(idx -> map.put(variables.get(idx), variation.get(idx)));
                    return LogicUtils.substitute(literal, map);
                })
                //.collect(LinkedHashSet::new, LinkedHashSet::add, LinkedHashSet::add);
                .collect(Collectors.toSet());
    }*/

    public static Set<Variable> variables(Literal literal) {
        return literal.argumentsStream()
                .map(LogicUtils::collectVariables)
                .collect(LinkedHashSet::new, LinkedHashSet::addAll, LinkedHashSet::addAll);
    }

    public static Set<Variable> variables(Clause c) {
        return c.literals().stream()
                .map(LogicUtils::variables)
                .collect(LinkedHashSet::new, LinkedHashSet::addAll, LinkedHashSet::addAll);
    }

    public static Set<Variable> collectVariables(Term term) {
        Set<Variable> result = Sugar.set();
        if (term instanceof Variable) {
            result.add((Variable) term);
        } else if (term instanceof Function || term instanceof PrologList) {
            Stream<Term> stream = null;
            if (term instanceof Function) {
                stream = ((Function) term).streamArguments();
            } else {
                stream = ((PrologList) term).streamArguments();
            }
            result = stream.map(LogicUtils::collectVariables)
                    .collect(LinkedHashSet::new, LinkedHashSet::addAll, LinkedHashSet::addAll);
        }
        return result;
    }

    public static Set<Literal> positiveLiterals(Clause clause) {
        return filteredLiterals(clause, (literal) -> !literal.isNegated()).collect(Collectors.toSet());
    }

    public static Set<Literal> negativeLiterals(Clause clause) {
        return filteredLiterals(clause, (literal) -> literal.isNegated()).collect(Collectors.toSet());
    }

    public static long negativeLiteralsCount(Clause clause) {
        return filteredLiterals(clause, (literal) -> literal.isNegated()).count();
    }

    public static Stream<Literal> filteredLiterals(Clause clause, java.util.function.Predicate<Literal> filter) {
        return clause.literals().stream().filter(filter);
    }

    public static void t1() {
        System.out.println(variabilizeClause(Clause.parse("lit(a,A), lit(b,c)"), Clause.parse("lit(x,#)")));
        System.out.println(randomlyRenameConstants(Clause.parse("l1(a,b), l2(b,c), l3(c,d)"), 1));
    }

    public static void t2() {
        //Clause clause = Clause.parse("b(X,a,X,Y,f(c,X,f(X,Y)),Q)");
        Clause clause = Clause.parse("b(X,a,b,Y,Q)");
        System.out.println("variables");
        System.out.println("\t" + clause);
        variables(clause.literals().iterator().next()).forEach(variable -> System.out.println("\t\t" + variable));
        System.out.println("constants");
        Set<Constant> constants = constants(clause);
        constants.forEach(c -> System.out.println("\t" + c));

        System.out.println("\nallSubstitutions ground (the same clause)");
        allSubstitution(clause.literals().iterator().next(), constants).forEach(ground -> System.out.println("\t" + ground));
    }


    public static void main(String[] args) {

        tHistogram();
        System.out.println("substitution probably does not works on composed terms! check! -- hopefully, it's solved");
        tSubstitution();

        t1();
        t2();
    }

    private static void tSubstitution() {
        Literal l = Literal.parseLiteral("p(f(f(X,Y),b(c,z,s,X)),X)");
        Map<Term, Term> substitution = new HashMap<>();
        substitution.put(Variable.construct("X"), Function.parseFunction("f(XZ,Y)"));
        Literal substituted = LogicUtils.substitute(l, substitution);
        System.out.println("before\t" + l);
        System.out.println("after \t" + substituted);
    }

    private static void tHistogram() {
        System.out.println("histogram check");
        Literal literal = Literal.parseLiteral("p(X,X,Y,Z,Z,f(X,Z))");
        System.out.println(literal);
        Counters<Variable> counter = variableHistogram(literal);
        counter.toMap().entrySet().forEach(entry -> System.out.println(entry.getKey() + "\t" + entry.getValue()));
    }

    /**
     * Compute t (or k) of the jk-clause.
     *
     * @param clause
     * @return
     */
    public static int computeMaxT(Clause clause) {
        return clause.literals().stream()
                .mapToInt(LogicUtils::computeT)
                .max().orElse(0);
    }

    public static int computeT(Literal literal) {
        return 1 + literal.argumentsStream()
                .mapToInt(LogicUtils::computeT)
                .sum();
    }

    public static int computeT(Term term) {
        if (term instanceof Variable) {
            return 1;
        } else if (term instanceof Constant) {
            return 1;
        } else if (term instanceof Function) {
            return 1 + ((Function) term).streamArguments()
                    .mapToInt(LogicUtils::computeT)
                    .sum();
        }
        throw new IllegalArgumentException();
    }

    public static Counters<Variable> variableHistogram(Term term) {
        if (term instanceof Variable) {
            return new Counters<>(Sugar.list((Variable) term));
        } else if (term instanceof Constant) {
            return new Counters<>();
        } else if (term instanceof Function) {
            return (((Function) term).streamArguments())
                    .map(LogicUtils::variableHistogram)
                    .reduce(new Counters<>(), Counters::addAll);
        }
        throw new IllegalArgumentException("unknown term implementation (nor variable, class or function");
    }

    public static Counters<Variable> variableHistogram(Literal literal) {
        return literal.argumentsStream() // it cannot be run in parallel here :(
                .map(LogicUtils::variableHistogram)
                .reduce(new Counters<>(), Counters::addAll);
    }

    public static Counters<Variable> variableHistogram(Clause clause) {
        return Sugar.parallelStream(clause.literals(), true) // parametrize if you want
                .map(LogicUtils::variableHistogram)
                .reduce(new Counters<>(), Counters::addAll);
    }

    /**
     * Renames variables in the term to fresh ones, e.g. f(X,Y,X) and startingPoint=2 => f(V2,V3,V2). The mapping parameter holds mapping from old to new variables (and is updated by the way of processing).
     *
     * @param term
     * @param startingPoint
     * @param mapping
     * @return
     */
    public static Term renameToFreshVariables(Term term, int startingPoint, Map<Variable, Variable> mapping) {
        if (term instanceof Constant) {
            return term;
        } else if (term instanceof Variable) {
            Variable v = (Variable) term;
            if (!mapping.containsKey(v)) {
                mapping.put(v, Variable.construct("V" + (startingPoint + mapping.size())));
            }
            return mapping.get(v);
        } else if (term instanceof Function) {
            Function func = (Function) term;
            Term[] arg = new Term[func.arity()];
            for (int argIdx = 0; argIdx < func.arity(); argIdx++) {
                arg[argIdx] = renameToFreshVariables(func.get(argIdx), startingPoint, mapping);
            }
            return new Function(func.name(), arg);
        }
        throw new IllegalStateException("unkonw implementation of term\t" + term);
    }

    /**
     * Returns true iff the given clause is range restricted, meaning that all variables in positive literals occur in some negative literal.
     *
     * @param clause
     * @return
     */
    public static boolean isRangeRestricted(Clause clause) {
        Set<Variable> headVariables = null;
        Set<Variable> bodyVariables = new HashSet<>();
        for (Literal literal : clause.literals()) {
            if (literal.isNegated()) {
                bodyVariables.addAll(variables(literal));
            } else {
                if (null == headVariables) {
                    headVariables = variables(literal);
                } else if (null != headVariables) {
                    throw new IllegalStateException("the input clause can be horn at most (i.e. having at most one positive literal) but given:\t" + clause);
                }
            }
        }
        return isRangeRestricted(headVariables, bodyVariables);
    }

    public static boolean isRangeRestricted(HornClause rule) {
        return isRangeRestricted(LogicUtils.variables(rule.head()), LogicUtils.variables(rule.body()));
    }

    private static boolean isRangeRestricted(Set<Variable> headVariables, Set<Variable> bodyVariables) {
        return bodyVariables.containsAll(headVariables);
    }


    public static Literal reverseArguments(Literal literal) {
        List<Term> arguments = literal.argumentsStream().collect(Collectors.toList());
        Collections.reverse(arguments);
        return new Literal(literal.predicate(), literal.isNegated(), arguments);
    }

    public static Set<Constant> constants(Set<Literal> literals) {
        return constants(new Clause(literals));
    }

    /**
     * returns ~predicates instead of !predicate, because of subsumption testing of clauses containing negations
     *
     * @param clause
     * @return
     */
    public static Clause replaceNegationSing(Clause clause) {
        return new Clause(clause.literals().stream()
                .map(l -> {
                    if (l.isNegated()) {
//                        l = new Literal("!~" + l.predicate(), false, l.argumentsStream().collect(Collectors.toList()));
                        l = LiteralsCache.getInstance().constructAndGet("!~" + l.predicate(), false, l.arguments());
                    }
                    return l;
                }).collect(Collectors.toList()));
    }


    public static Set<Literal> loadEvidence(String line) {
        Set<Literal> literals = Clause.parse(trimTicks ? line.replace("\"", "") : line).literals();
        if (!pseudoPrologNotation) {
            literals = literals.stream().map(LogicUtils::constantize).collect(Collectors.toSet());
        }
        return literals;
    }

    public static Set<Literal> loadEvidence(Path path) {
        Set<Literal> literals = null;
        try {
            literals = Files.readAllLines(path, Charset.forName("latin1"))
                    .stream()
                    .filter(line -> line.trim().length() > 0)
                    .flatMap(line -> loadEvidence(line).stream())
                    .collect(Collectors.toSet());
        } catch (IOException e) {
            e.printStackTrace();
        }
        return literals;
    }

    public static Clause addTyping(Clause clause, Map<Pair<Predicate, Integer>, String> typing) {
        //return new Clause(clause.literals().stream().map(l -> addTyping(l, typing)).collect(Collectors.toList()));
        Set<Literal> literals = Sugar.set();
        Set<Literal> special = Sugar.set();


        for (Literal literal : clause.literals()) {
            if (SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(literal.predicate()) || SpecialVarargPredicates.SPECIAL_PREDICATES.contains(literal.predicate())) {
                special.add(literal);
            } else {
                literals.add(literal);
            }
        }

        List<Literal> literalsTyped = Sugar.list();
        List<Literal> specialTyped = Sugar.list();
        Map<Term, Term> mapping = new HashMap<>();
        for (Literal literal : literals) {
            Predicate predicate = Predicate.create(literal.getPredicate());
            List<Term> arguments = Sugar.list();
            for (int idx = 0; idx < literal.arity(); idx++) {
                Pair<Predicate, Integer> key = new Pair<>(predicate, idx);
                Term term = literal.get(idx);
                Term typed = addTyping(term, typing.get(key));
                if (mapping.containsKey(term)) {
                    Term mapped = mapping.get(term);
                    if (!mapped.equals(typed)) {
                        throw new IllegalStateException();
                    }
                    typed = mapped;
                } else {
                    mapping.put(term, typed);
                }
                arguments.add(typed);
            }
            literalsTyped.add(new Literal(literal.predicate(), literal.isNegated(), arguments));
        }

        for (Literal literal : special) {
            List<Term> terms = literal.argumentsStream().map(t -> mapping.get(t)).collect(Collectors.toList());
            specialTyped.add(new Literal(literal.predicate(), literal.isNegated(), terms));
        }

        return new Clause(Sugar.iterable(literalsTyped, specialTyped));
    }

    // only flat ;)
    public static Literal addTyping(Literal literal, Map<Pair<Predicate, Integer>, String> typing) {
        Predicate predicate = Predicate.create(literal.predicate(), literal.arity());
        return new Literal(literal.predicate(),
                literal.isNegated(),
                IntStream.range(0, literal.arity())
                        .mapToObj(idx -> addTyping(literal.get(idx), typing.get(new Pair<>(predicate, idx))))
                        .collect(Collectors.toList()));
    }

    private static Term addTyping(Term term, String type) {
        if (null == type) {
            System.out.println("what is a problem here?");
            //throw new NotImplementedException();
            throw new UnsupportedOperationException("Not implemented.");
        }
        type = (null == type) ? "-1" : type;
        if (term instanceof Constant) {
            return Constant.construct(term.name(), type);
        } else if (term instanceof Variable) {
            return Variable.construct(term.name(), type);
        }
        //throw new NotImplementedException();

        throw new UnsupportedOperationException("Not implemented.");
    }

    private static Term untype(Term term) {
        if (term instanceof Constant) {
            if (term.name().startsWith("-1:")) {
                // unfortunately, hack to be compatible with -1: which is not recognized as a type
                return Constant.construct(term.name().substring("-1:".length()));
            }
            return Constant.construct(term.name());
        } else if (term instanceof Variable) {
            if (term.name().startsWith("-1:")) {
                // unfortunately, hack to be compatible with -1: which is not recognized as a type
                return Variable.construct(term.name().substring("-1:".length()));
            }
            return Variable.construct(term.name());
        }
        //throw new NotImplementedException();

        throw new UnsupportedOperationException("Not implemented.");
    }

    public static Collection<Clause> addTyping(Collection<Clause> clauses, Map<Pair<Predicate, Integer>, String> typing) {
        Collection retVal = (clauses instanceof Set) ? Sugar.set() : Sugar.list();
        for (Clause clause : clauses) {
            retVal.add(addTyping(clause, typing));
        }
        return retVal;
    }


    public static boolean anyUntyped(Clause clause) {
        for (Literal literal : clause.literals()) {
            if (anyUntyped(literal.argumentsStream())) {
                return true;
            }
        }
        return false;
    }

    public static boolean anyUntyped(Collection<? extends Term> terms) {
        return anyUntyped(terms.stream());
    }

    public static boolean anyUntyped(Stream<? extends Term> terms) {
        return terms.anyMatch(term -> null == term.type() || term.type().length() < 1);
    }

    public static boolean areSameTypes(Term first, Term second) {
        if (null == first.type() && null == second.type()) {
            return true;
        }
        if (null == first.type() || null == second.type()) {
            return false;
        }
        return first.type().equals(second.type());
    }

    public static Clause untype(Clause c) {
        return new Clause(c.literals().stream().map(LogicUtils::untype).collect(Collectors.toList()));
    }

    public static Literal untype(Literal l) {
        return new Literal(l.predicate(), l.isNegated(), l.argumentsStream().map(LogicUtils::untype).collect(Collectors.toList()));
    }

    public static Set<Literal> untype(Set<Literal> literals) {
        return literals.stream().map(LogicUtils::untype).collect(Collectors.toSet());
    }

    public static Set<Literal> addTyping(Set<Literal> evidence, Map<Pair<Predicate, Integer>, String> typing) {
        return evidence.stream().map(l -> addTyping(l, typing)).collect(Collectors.toSet());
    }

    // logic programmings constraints == only negative literals
    public static Set<Clause> constraints(Collection<Clause> clauses) {
        return clauses.stream().filter(c -> positiveLiterals(c).isEmpty()).collect(Collectors.toSet());
    }

    public static Set<Clause> definiteRules(Collection<Clause> clauses) {
        return clauses.stream().filter(c -> positiveLiterals(c).size() == 1).collect(Collectors.toSet());
    }

    public static Clause removeSpecialPredicates(Clause clause) {
        return new Clause(clause.literals().stream().filter(l -> !SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()) && !SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())).collect(Collectors.toList()));
    }

    public static boolean isDefiniteRule(Clause c) {
        return positiveLiterals(c).size() == 1;
    }

    public static boolean isConstraint(Clause c) {
        return positiveLiterals(c).isEmpty();
    }

    public static String toRNotation(Literal literal) {
        return toRNotation(literal, "r");
    }

    public static String toRNotation(Triple<String, String, String> triple, String predicate) {
        return predicate + "(" + triple.getR() + "," + triple.getS() + "," + triple.getT() + ")";
    }

    public static String toRNotation(Literal literal, String predicate) {
        if (literal.arity() == 1) {
            String entity = literal.get(0).toString();
            String attribute = literal.getPredicate().getR();
            return predicate + "(" + entity + "," + attribute + ")";
        } else if (literal.arity() == 2) {
            String arg1 = literal.get(0).toString();
            String arg2 = literal.get(1).toString();
            String relation = literal.getPredicate().r;
            return predicate + "(" + arg1 + "," + relation + "," + arg2 + ")";
        }
        //throw new NotImplementedException();

        throw new UnsupportedOperationException("Not implemented.");
    }

    /*
    public static List<Clause> folSkolemization(Clause clause, boolean disjunctionOnInput, boolean skolemizeFirstVariable, SkolemizationFactory factory) {
        // should resolve cases
        // E x E y phi(x, y)
        // V x E y phi(x, y)
        // E x V y phi(x, y)
        List<Clause> result = Sugar.list();
        Pair<String, String> zsArity1 = factory.getNext(1);
        Literal z1Literal = new Literal(zsArity1.r, clause.getQuantifier().getFirstVariable());
        Literal s1Literal = new Literal(zsArity1.s, clause.getQuantifier().getFirstVariable());
        result.add(new Clause(z1Literal, s1Literal));
        if (disjunctionOnInput) {
            for (Literal literal : clause.literals()) {
                Literal negation = literal.negation();
                result.add(new Clause(negation, z1Literal));
                result.add(new Clause(negation, s1Literal));
            }
        } else {
            result.add(new Clause(Sugar.union(Sugar.list(z1Literal), clause.literals())));
            result.add(new Clause(Sugar.union(Sugar.list(s1Literal), clause.literals())));
        }

        if (skolemizeFirstVariable) {
            Pair<String, String> zsArity0 = factory.getNext(0);
            Literal s0Literal = new Literal(zsArity0.s);
            result.add(new Clause(z1Literal.negation(), s0Literal));
        } else {
            result.add(new Clause(z1Literal));
        }
        return result;
    }
    */

}
