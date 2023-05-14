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
 * Clause.java
 *
 * Created on 30. listopad 2006, 16:36
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package search.ilp.logic;

import search.sentences.SentenceState;
import search.utils.Sugar;
import search.utils.collections.MultiMap;
import search.utils.tuples.Pair;

import java.io.UnsupportedEncodingException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Class for storing sets of positive first-order-logic literals. There is only one copy of each literal in in any Clause.
 * <p>
 * ok
 */
public class Clause {

    public static final char DELIMITER = '|';

    private LinkedHashSet<Literal> literals = new LinkedHashSet<Literal>();

    private MultiMap<String, Literal> literalsByName;

    private MultiMap<Term, Literal> literalsByTerms;

    private int hashCode = -1;

    private Quantifier quantifier = null;

    private Clause quantifierExtended;
    private Clause quantifierExtendedWithoutOrder;
    private Clause negationRepresentation;
    private Clause quantifiedClause;
    private boolean cliffhanger;
    private boolean decomposable;
    private String fullyCannonic;
    private String partiallyCannonic;
    private boolean frozen;

    public Clause() {
    }

    public Clause(Quantifier quantifier, Iterable<? extends Literal> literals) {
        this(literals);
        this.quantifier = quantifier;
        computeDecomposability();
    }

    private void computeDecomposability() {
        this.decomposable = connectedComponents().size() != 1;
    }


    public Clause(Quantifier quantifier, Literal... literals) {
        this(literals);
        this.quantifier = quantifier;
        computeDecomposability();
    }

    /**
     * Creates a new instance of class Clause. All literals in the collection "literals"
     * are locked for changes.
     *
     * @param literals a collection of literals to be stored in this object.
     */
    public Clause(Iterable<? extends Literal> literals) {
        // tady udelat optimalizaci napr
        for (Literal l : literals) {
            l.allowModifications(false);
            this.addLiteral(l);
        }
    }

    public Clause(Literal... literals) {
        for (Literal literal : literals) {
            literal.allowModifications(false);
            this.addLiteral(literal);
        }
    }


    public static Clause create(Quantifier quantifier, Literal... literals) {
        return new Clause(quantifier, literals);
    }

    /**
     * Adds literals from collection c.
     *
     * @param c the collection of literals to be added.
     */
    public void addLiterals(Collection<Literal> c) {
        this.hashCode = -1;
        for (Literal l : c) {
            this.addLiteral(l);
        }
    }

    /**
     * Adds literal l.
     *
     * @param literal the literal to be added.
     */
    public void addLiteral(Literal literal) {
        this.hashCode = -1;
        if (!this.literals.contains(literal)) {
            this.literals.add(literal);
        }
        if (this.literalsByName != null) {
            this.literalsByName.put(literal.predicate(), literal);
        }
        if (this.literalsByTerms != null) {
            for (int i = 0; i < literal.arity(); i++) {
                this.literalsByTerms.put(literal.get(i), literal);
            }
        }
    }

    /**
     * Removes literal
     *
     * @param literal the literal to be removed.
     */
    public void removeLiteral(Literal literal) {
        this.hashCode = -1;
        if (this.literals.contains(literal)) {
            this.literals.remove(literal);
        }
        if (this.literalsByName != null) {
            this.literalsByName.remove(literal.predicate(), literal);
        }
        if (this.literalsByTerms != null) {
            for (int i = 0; i < literal.arity(); i++) {
                this.literalsByTerms.remove(literal.get(i), literal);
            }
        }
    }

    private void initLiteralsByTerms() {
        this.literalsByTerms = new MultiMap<Term, Literal>();
        for (Literal literal : literals) {
            for (int i = 0; i < literal.arity(); i++) {
                literalsByTerms.put(literal.get(i), literal);
            }
        }
    }

    private void initLiteralsByName() {
        this.literalsByName = new MultiMap<String, Literal>();
        for (Literal literal : literals) {
            this.literalsByName.put(literal.predicate(), literal);
        }
    }

    /**
     * Checks if the set of literals contained in this clause is a subset of literals in Clause "clause".
     *
     * @param clause the clause for which the relation "subset-of" is tested
     * @return
     */
    public boolean isSubsetOf(Clause clause) {
        HashSet<Literal> set = new HashSet<Literal>();
        set.addAll(clause.literals);
        for (Literal l : literals) {
            if (!set.contains(l)) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return number of unique literals
     */
    public int countLiterals() {
        return literals.size();
    }

    /**
     * Creates a map of frequencies of terms in the Clause "mod literals", which means
     * that it returns a Map in which terms are keys and values are the numbers of occurences
     * of these terms in literals (multiple occurence of a term in one literal is counted as one occurence).
     *
     * @return a map with frequencies of terms in the clause.
     */
    public Map<Term, Integer> termFrequenciesModLiterals() {
        if (literalsByTerms == null) {
            initLiteralsByTerms();
        }
        HashMap<Term, Integer> frequencies = new HashMap<Term, Integer>();
        for (Map.Entry<Term, Set<Literal>> entry : this.literalsByTerms.entrySet()) {
            frequencies.put(entry.getKey(), entry.getValue().size());
        }
        return frequencies;
    }

    /**
     * Creates a map of frequencies of variables in the Clause "mod literals", which means
     * that it returns a Map in which variables are keys and values are the numbers of occurences
     * of these variables in literals (multiple occurence of a variable in one literal is counted as one occurence).
     *
     * @return a map with frequencies of terms in the clause.
     */
    public Map<Variable, Integer> variableFrequenciesModLiterals() {
        if (literalsByTerms == null) {
            initLiteralsByTerms();
        }
        HashMap<Variable, Integer> frequencies = new HashMap<Variable, Integer>();
        for (Map.Entry<Term, Set<Literal>> entry : this.literalsByTerms.entrySet()) {
            if (entry.getKey() instanceof Variable) frequencies.put((Variable) entry.getKey(), entry.getValue().size());
        }
        return frequencies;
    }

    /**
     * @return literals in the Clause
     */
    public LinkedHashSet<Literal> literals() {
        return literals;
    }

    /**
     * Computes the set of predicate-names which appear in the clause. This method uses caching, so
     * while the first call to it may be a bit expensive, the subsequent calls should be very fast.
     *
     * @return set of all predicate names used in the Clause
     */
    public Set<String> predicates() {
        if (literalsByName == null) {
            initLiteralsByName();
        }
        return literalsByName.keySet();
    }

    /**
     * Collects the set of all literals in the Clause which are based on predicate name
     * "predicate". This method uses caching, so
     * while the first call to it may be a bit expensive, the subsequent calls should be very fast.
     *
     * @param predicate the predicate name of literals that we want to obtain.
     * @return the set of literals based on predicate "predicate"
     */
    public Collection<Literal> getLiteralsByPredicate(String predicate) {
        if (literalsByName == null) {
            initLiteralsByName();
        }
        return literalsByName.get(predicate);
    }

    /**
     * Collects the set of literals which contain Term term in their arguments. This method uses caching, so
     * while the first call to it may be a bit expensive, the subsequent calls should be very fast.
     *
     * @param term
     * @return the set of literals which contain "term"
     */
    public Collection<Literal> getLiteralsByTerm(Term term) {
        if (literalsByTerms == null) {
            initLiteralsByTerms();
        }
        return literalsByTerms.get(term);
    }

    /**
     * Checks if the Clause contains a given literal.
     *
     * @param literal literal whose presence is tested.
     * @return true if the Clause contains "literal", false otherwise.
     */
    public boolean containsLiteral(Literal literal) {
        return this.literals.contains(literal);
    }

    /**
     * @return the set of all variables contained in the Clause.
     */
    public Set<Variable> variables() {
        if (literalsByTerms == null) {
            initLiteralsByTerms();
        }
        HashSet<Variable> set = new HashSet<Variable>();
        for (Map.Entry<Term, Set<Literal>> entry : literalsByTerms.entrySet()) {
            if (entry.getKey() instanceof Variable && entry.getValue().size() > 0) {
                set.add((Variable) entry.getKey());
            }
        }
        return set;
    }

    /**
     * @return the set of all terms (i.e. constants, variables and function symbols) contained in the Clause.
     */
    public Set<Term> terms() {
        if (literalsByTerms == null) {
            initLiteralsByTerms();
        }
        return literalsByTerms.keySet();
    }

    public static Clause parse(byte[] bytes) throws UnsupportedEncodingException {
        return Clause.parse(new String(bytes, "UTF-8"));
    }

    /**
     * Constructs a clause from its string representation. Clauses are assumed to be represented using a prolog-like syntax (which we call pseudo-prolog).
     * Variables start with upper-case letters, constants with lower-case letters, digits or apostrophes.
     * An example of a syntactically correct clause is shown below:<br />
     * <br />
     * literal(a,b), anotherLiteral(A,b), literal(b,'some longer text... ')<br />
     *
     * @param str string representation of the Clause
     * @return new instance of the class Clause corresponding to the string representation.
     */
    public static Clause parse(String str) {
        return parse(str, DELIMITER, null);
    }

    public static Clause parse(String str, char literalSeparator, Quantifier quantifier) {
        return parse(str, literalSeparator, quantifier, new HashMap<>());
    }

    public static Clause parse(String str, char literalSeparator, Quantifier quantifier, Map<String, Literal> literalsCache) {
        // if there is a literal corresponding to a string in the cache, the literal will be taken; otherwise new predicate is constructed
        str = str.trim();
        if (str.isEmpty()) {
            return new Clause(Sugar.<Literal>list());
        }
        if (str.charAt(str.length() - 1) == '.') {
            str = str.substring(0, str.length() - 1);
        }
        str = str + literalSeparator + " ";
        int brackets = 0;//()
        boolean inQuotes = false;
        boolean ignoreNext = false;
        boolean expectingLiteralSeparator = false;
        List<String> split = new ArrayList<String>();
        char[] chars = str.toCharArray();
        StringBuilder sb = new StringBuilder();
        for (char c : chars) {
            if (ignoreNext) {
                sb.append(c);
                ignoreNext = false;
            } else if (inQuotes) {
                sb.append(c);
                if (c == '\'') {
                    inQuotes = false;
                }
            } else {
                switch (c) {
                    case '\\':
                        ignoreNext = true;
                        break;
                    case '\t':
                    case ' ':
                    case '\n':
                        break;
                    case '\'':
                        inQuotes = !inQuotes;
                        sb.append(c);
                        break;
                    case '(':
                        brackets++;
                        sb.append(c);
                        break;
                    case ')':
                        brackets--;
                        expectingLiteralSeparator = true;
                        sb.append(c);
                        break;
                    default:
                        if (expectingLiteralSeparator && c == literalSeparator) {
                            expectingLiteralSeparator = false;
                            if (brackets == 0) {
                                split.add(sb.toString());
                                sb = new StringBuilder();
                            } else {
                                sb.append(c);
                            }
                        } else {
                            sb.append(c);
                        }
                        break;
                }
            }
        }
        HashMap<Variable, Variable> variables = new HashMap<Variable, Variable>();
        HashMap<Constant, Constant> constants = new HashMap<Constant, Constant>();
        List<Literal> parsedLiterals = new ArrayList<Literal>();
        for (String s : split) {
            s = s.trim();
            if (s.length() > 0) {
                if (literalsCache.containsKey(s)) {
                    parsedLiterals.add(literalsCache.get(s));
                } else {
                    parsedLiterals.add(Literal.parseLiteral(s, variables, constants));
                }
            }
        }
        int anonymousIndex = 1;
        for (Literal l : parsedLiterals) {
            for (int i = 0; i < l.arity(); i++) {
                if (l.get(i).name().equals("_")) {
                    Variable an = Variable.construct("_" + (anonymousIndex++));
                    while (variables.containsKey(an.name())) {
                        an = Variable.construct("_" + (anonymousIndex++), l.get(i).type());
                    }
                    l.set(an, i);
                    variables.put(an, an);
                }
            }
        }
        return new Clause(quantifier, parsedLiterals);
    }

    @Override
    public String toString() {
        return this.toPrologLikeString(", ", Literal.negationSign);
    }

    public String toString(String separator, String negationSign) {
        return this.toPrologLikeString(separator, negationSign);
    }

    public String toString(String separator) {
        return toString(separator, Literal.negationSign);
    }


    private String toPrologLikeString(String separator, String negationSign) {
        if (this.literals.size() == 0) {
            return "#EmptyClause";
        }
        StringBuilder sb = new StringBuilder();
        int i = 0;
        int numLiterals = this.literals.size();
        for (Literal l : this.literals) {
            sb.append(l.toString(negationSign));
            if (i < numLiterals - 1) {
                sb.append(separator);
            }
            i++;
        }
        return sb.toString();
    }

    @Override
    public int hashCode() {
        if (this.hashCode == -1) {
            this.hashCode = this.literals.hashCode();
        }
        return this.hashCode;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof Clause) {
            Clause c = (Clause) o;
            boolean quantifiersEqual = false;
            //= this.quantifier == c.quantifier; // quick workaround, since quantifiers are generated only once at the start
            if (null == this.quantifier) {
                quantifiersEqual = this.quantifier == c.quantifier;
            } else {
                quantifiersEqual = this.quantifier.getQuantifiers() == c.quantifier.getQuantifiers()
                        && (this.quantifier.getVariables() == c.quantifier.getVariables()
                        || this.quantifier.getVariables().equals(c.quantifier.getVariables())) // ugly hack, this should be insie quantifier
                ;
            }
            return this.isSubsetOf(c) && c.isSubsetOf(this) && quantifiersEqual;
        } else {
            return false;
        }
    }

    /**
     * Returns the set of connected components. Two parts of a clause are called term-disconnected if they have no term in common,
     * they are called variable-disconnected if they have no variable in common.
     *
     * @return the set of term-connected components
     */
    public Collection<Clause> connectedComponents() {
        return connectedComponents(false);
    }


    /**
     * Returns the set of connected components. Two parts of a clause are called term-disconnected if they have no term in common,
     * they are called variable-disconnected if they have no variable in common.
     *
     * @param justVariables
     * @return the set of term-connected components if justVariables == true, otherwise returns the set of variable-connected components
     */
    public Collection<Clause> connectedComponents(boolean justVariables) {
        return connectedComponents(justVariables, new HashSet<Term>());
    }

    public Collection<Clause> connectedComponents(boolean justVariables, Set<Term> ignoredTerms) {
        if (literalsByTerms == null) {
            initLiteralsByTerms();
        }
        Collection<? extends Term> remainingTerms;
        Set<Literal> allLiteralsInSomeComponent = new HashSet<Literal>();
        if (justVariables) {
            remainingTerms = Sugar.collectionDifference(this.variables(), ignoredTerms);
        } else {
            remainingTerms = Sugar.collectionDifference(literalsByTerms.keySet(), ignoredTerms);
        }
        List<Clause> components = new ArrayList<Clause>();
        while (remainingTerms.size() > 0) {
            Pair<Clause, Set<? extends Term>> pair = connectedComponent(Sugar.chooseOne(remainingTerms), ignoredTerms, justVariables);
            components.add(pair.r);
            allLiteralsInSomeComponent.addAll(pair.r.literals());
            remainingTerms = Sugar.collectionDifference(remainingTerms, pair.s);
        }
        for (Literal l : Sugar.collectionDifference(this.literals, allLiteralsInSomeComponent)) {
            components.add(new Clause(Sugar.set(l)));
        }
        return components;
    }

    private Pair<Clause, Set<? extends Term>> connectedComponent(Term termInComponent, Set<Term> ignoredTerms, boolean justVariables) {
        Set<Term> closed = new HashSet<Term>();
        Stack<Term> open = new Stack<Term>();
        Set<Term> openSet = new HashSet<Term>();
        for (Literal literal : getLiteralsByTerm(termInComponent)) {
            for (int i = 0; i < literal.arity(); i++) {
                if ((!justVariables || literal.get(i) instanceof Variable) && !ignoredTerms.contains(literal.get(i))) {
                    open.push(literal.get(i));
                }
            }
        }
        while (!open.isEmpty()) {
            Term term = open.pop();
            if (!closed.contains(term)) {
                for (Literal literal : getLiteralsByTerm(term)) {
                    for (int i = 0; i < literal.arity(); i++) {
                        if (!closed.contains(literal.get(i)) && !openSet.contains(literal.get(i))) {
                            if ((!justVariables || literal.get(i) instanceof Variable) && !ignoredTerms.contains(literal.get(i))) {
                                open.push(literal.get(i));
                                openSet.add(literal.get(i));
                            }
                        }
                    }
                }
                if (!ignoredTerms.contains(term)) {
                    closed.add(term);
                }
            }
        }
        Set<Literal> lits = new HashSet<Literal>();
        outerLoop:
        for (Literal literal : literals()) {
            for (int i = 0; i < literal.arity(); i++) {
                if ((!justVariables || literal.get(i) instanceof Variable) && closed.contains(literal.get(i))) {
                    lits.add(literal);
                    continue outerLoop;
                }
            }
        }
        return new Pair<Clause, Set<? extends Term>>(new Clause(lits), closed);
    }

    public static void main(String[] args) {
        Clause c = Clause.parse("professor(a1) v !taughtBy(a2,a1,a3) v !courseLevel(a2,Level_500)", 'v', null);
        for (Clause comp : c.connectedComponents(false, Sugar.<Term>set(Constant.construct("a1")))) {
            System.out.println(comp);
        }
    }

    public String toFOL(boolean printQuantifiers, boolean fullQuantifiers) {
        return toFOL(printQuantifiers, fullQuantifiers, false);
    }

    public String toFOL(boolean printQuantifiers, boolean fullQuantifiers, boolean printFeatures) {
        StringBuilder quantifiers = new StringBuilder();
        if (printQuantifiers) {
            quantifiers.append(this.quantifier.quantifierToString(0));
            if (fullQuantifiers || isSecondVariableUsed()) {
                quantifiers.append(this.quantifier.quantifierToString(1));
            }
        }
        return (printFeatures && this.isFrozen() ? "*" : "") + quantifiers + this.literals.stream().map(Literal::toString).collect(Collectors.joining(" " + DELIMITER + " "));
    }

    public Quantifier getQuantifier() {
        return quantifier;
    }


    public SentenceState getWFOMCSkolemization(SkolemizationFactory factory) {
        if (!isFirstVariableUsed()) {
            throw new IllegalStateException();
        }
        boolean secondVariableIsUsed = isSecondVariableUsed();
        List<Clause> skolemizedClauses = Sugar.list();
        if (TwoQuantifiers.FORALL_FORALL == quantifier.getQuantifiers()
                || (TwoQuantifiers.FORALL_EXISTS == quantifier.getQuantifiers() && !secondVariableIsUsed)) {
            skolemizedClauses.add(this);
        } else if (TwoQuantifiers.FORALL_EXISTS == quantifier.getQuantifiers()) {
            // for sure, second variable is used
            // unit propagation takes place
            Literal sLiteral = new Literal(factory.getNext(1), quantifier.getFirstVariable());
            for (Literal literal : literals) {
                skolemizedClauses.add(new Clause(literal.negation(), sLiteral));
            }
        } else if (!secondVariableIsUsed) {
            // either E x V y or E x E y, but only x is used in the clause, so it is the same as E x
            Literal sLiteral = new Literal(factory.getNext(0));
            for (Literal literal : literals) {
                skolemizedClauses.add(new Clause(literal.negation(), sLiteral));
            }
        } else if (TwoQuantifiers.EXISTS_FORALL == quantifier.getQuantifiers()) {
            // E x V y
            Literal s0Literal = new Literal(factory.getNext(0));
            Literal s1Literal = new Literal(factory.getNext(1), quantifier.getFirstVariable());
            skolemizedClauses.add(new Clause(s0Literal.negation(), s1Literal));
            skolemizedClauses.add(new Clause(Sugar.union(Sugar.list(s1Literal), literals)));
        } else if (TwoQuantifiers.EXISTS_EXISTS == quantifier.getQuantifiers()) {
            // E x E y
            Literal s0Literal = new Literal(factory.getNext(0));
            for (Literal literal : literals) {
                skolemizedClauses.add(new Clause(literal.negation(), s0Literal));
            }
        } else {
            throw new IllegalStateException();
        }
        return new SentenceState(skolemizedClauses, null);
    }

    public boolean containsTerm(Term term) {
        for (Literal literal : literals) {
            if (literal.containsTerm(term)) {
                return true;
            }
        }
        return false;
    }

    public Clause getQuantifierExtendedClause() {
        if (null == this.quantifierExtended) {
            this.quantifierExtended = toExtendedClause(quantifier.usedVariable);
        }
        return this.quantifierExtended;
    }

    public Clause getQuantifierExtendedClauseWithoutOrder() {
        if (null == this.quantifierExtendedWithoutOrder) {
            this.quantifierExtendedWithoutOrder = toExtendedClause(quantifier.usedVariablesWithoutOrder);
        }
        return this.quantifierExtendedWithoutOrder;
    }

    private Clause toExtendedClause(Map<Variable, Literal> map) {
        List<Literal> literals = Sugar.listFromCollections(this.literals);
        for (Variable variable : this.quantifier.getVariables()) {
            if (this.containsTerm(variable)) {
                literals.add(map.get(variable));
            }
        }
        return new Clause(literals);
    }

    public Clause negationToSpecialPrefix() {
        if (null == this.negationRepresentation) {
            if (this.containsNegatedLiteral()) {
                this.negationRepresentation = LogicUtils.replaceNegationSing(this);
            } else {
                this.negationRepresentation = this;
            }
        }
        return this.negationRepresentation;
    }

    private boolean containsNegatedLiteral() {
        for (Literal literal : literals) {
            if (literal.isNegated()) {
                return true;
            }
        }
        return false;
    }

    public boolean isFirstVariableUsed() {
        return usedVariable(0);
    }

    private boolean usedVariable(int idx) {
        return containsTerm(quantifier.getVariable(idx));
    }

    public boolean isSecondVariableUsed() {
        return usedVariable(1);
    }

    public String quantifierToName(boolean addSecond) {
        // if addSecond is false, only the first one is given
        String firstVariableConstraint = quantifier.isCountingQuantifier() && quantifier.firstVariableCardinality > -1 ? "" + quantifier.firstVariableCardinality : "";
        String secondVariableConstraint = quantifier.isCountingQuantifier() && quantifier.secondVariableCardinality > -1 ? "" + quantifier.secondVariableCardinality : "";
        if (addSecond) {
            switch (quantifier.getQuantifiers()) {
                case FORALL_FORALL:
                    return "Forallforall";
                case FORALL_EXISTS:
                    return "Forallexists" + secondVariableConstraint;
                case EXISTS_FORALL:
                    return "Exists" + firstVariableConstraint + "forall";
                case EXISTS_EXISTS:
                    return "Exists" + firstVariableConstraint + "exists" + secondVariableConstraint;
                default:
                    throw new IllegalStateException();
            }
        } else {
            if (TwoQuantifiers.startsWithForall(quantifier.getQuantifiers())) {
                return "Forall";
            } else {
                return "Exists" + firstVariableConstraint;
            }
        }
    }


    public String singleVariableQuantifierToName(int variableIdx) {
        // if addSecond is false, only the first one is given
        String constraint = "";
        if (0 == variableIdx && quantifier.firstVariableCardinality > -1) {
            constraint = quantifier.firstVariableCardinality + "";
        } else if (1 == variableIdx && quantifier.secondVariableCardinality > -1) {
            constraint = quantifier.secondVariableCardinality + "";
        }

        String result = "";
        if (0 == variableIdx) {
            result = TwoQuantifiers.startsWithForall(quantifier.getQuantifiers()) ? "Forall" : "Exists";
        } else {
            result = TwoQuantifiers.FORALL_FORALL == quantifier.getQuantifiers()
                    || TwoQuantifiers.EXISTS_FORALL == quantifier.getQuantifiers()
                    ? "Forall" : "Exists";
        }
        return result + constraint;
    }

    public boolean hasSameQuantifier(Clause second) {
        if (null == this.quantifier || null == second.getQuantifier()) {
            return false;
        }
        return this.quantifier.equals(second.getQuantifier());
    }

    public boolean startsWithTheSameQuantifier(Clause second) {
        if (null == this.quantifier && null == second.getQuantifier()) {
            return true;
        }
        return TwoQuantifiers.startsWithForall(quantifier.getQuantifiers()) == TwoQuantifiers.startsWithForall(second.getQuantifier().getQuantifiers());
    }

    public Clause getQuantifiedClause() { // TODO check this w.r.t. getExtendedClause,...
        if (this.quantifiedClause == null) {
            List<Literal> lits = Sugar.listFromCollections(literals);
            lits.add(new Literal(TwoQuantifiers.startsWithForall(quantifier.getQuantifiers()) ? "Forall" : "Exists", quantifier.getVariable(0)));
            lits.add(new Literal((quantifier.getQuantifiers() == TwoQuantifiers.FORALL_FORALL || quantifier.getQuantifiers() == TwoQuantifiers.EXISTS_FORALL) ? "Forall" : "Exists", quantifier.getVariable(1)));
            this.quantifiedClause = new Clause(lits);
        }
        return this.quantifiedClause;
    }

    public String getProver9Format() {
        StringBuilder sb = new StringBuilder();
        sb.append(TwoQuantifiers.startsWithForall(quantifier.getQuantifiers()) ? "all" : "exists").append(" ").append(quantifier.getVariable(0)).append(" ");
        if (isSecondVariableUsed()) {
            sb.append(TwoQuantifiers.FORALL_EXISTS == quantifier.getQuantifiers() || TwoQuantifiers.EXISTS_EXISTS == quantifier.getQuantifiers() ? "exists" : "all").append(" ").append(quantifier.getVariable(1)).append(" ");
        }
        sb.append("(");
        sb.append(toString(" | ", "-"));
        sb.append(")");
        sb.append(".");
        return sb.toString();
    }

    public boolean isCliffhanger() {
        return cliffhanger;
    }

    public void setCliffhanger(boolean cliffhanger) {
        this.cliffhanger = cliffhanger;
    }

    public boolean hasCountingQuantifier() {
        if (null == this.quantifier) {
            return false;
        }
        return this.quantifier.isCountingQuantifier();
    }

    public boolean isDecomposable() {
        return decomposable;
    }

    public boolean isLexicographicallySame(Clause clause, boolean ignoreSecondVariableIfNotUsed) {
        return this.getCannonic(ignoreSecondVariableIfNotUsed).equals(clause.getCannonic(ignoreSecondVariableIfNotUsed));
    }

    public String getCannonic(boolean ignoreSecondVariableIfNotUsed) {
        if (null == this.fullyCannonic) {
            // ignoreSecondVariableIfNotUsed : true -> naper to v poradi kvantifikatoru ktere tam je ; false -> snaz se minimalizovat i preskladani promennych v kvantifikatoru
            this.fullyCannonic = this.quantifier.quantifierToString(0) + " " +
                    this.quantifier.quantifierToString(1) + " " +
                    literals.stream().map(Literal::toString).collect(Collectors.joining(" | "));

            boolean isSecondVariableUsed = isSecondVariableUsed();
            boolean isDecomposable = isDecomposable();
            StringBuilder sb = new StringBuilder();
            if (isSecondVariableUsed && (
                    quantifier.getQuantifiers() == TwoQuantifiers.FORALL_FORALL
                            || (quantifier.getQuantifiers() == TwoQuantifiers.FORALL_EXISTS && isDecomposable)
                            || (quantifier.getQuantifiers() == TwoQuantifiers.EXISTS_FORALL && isDecomposable)
                            || (quantifier.getQuantifiers() == TwoQuantifiers.EXISTS_EXISTS && isDecomposable)
                            || (quantifier.getQuantifiers() == TwoQuantifiers.EXISTS_EXISTS && !quantifier.isCountingQuantifier())
            )) {
                // however, this is not literally lexicographically minimal, but it's cannonical so it should be enough for now
                Variable x = quantifier.getFirstVariable();
                Variable y = quantifier.getSecondVariable();
                HashMap<Term, Term> substitution = new HashMap<>();
                substitution.put(x, y);
                substitution.put(y, x);
                String basic = literals.stream().map(Literal::toString).sorted().collect(Collectors.joining(" | "));
                String swapped = literals.stream().map(l -> LogicUtils.substitute(l, substitution)).map(Literal::toString).sorted().collect(Collectors.joining(" | "));
                if (basic.compareTo(swapped) <= 0) {
                    sb.append(quantifier.quantifierToString(0))
                            .append(quantifier.quantifierToString(1))
                            .append(basic);
                } else {
                    sb.append(quantifier.quantifierToString(1).replaceFirst(y.toString(), x.toString()))
                            .append(quantifier.quantifierToString(0).replaceFirst(x.toString(), y.toString()))
                            .append(swapped);
                }
            } else {
                sb.append(quantifier.quantifierToString(0));
                if (isSecondVariableUsed) {
                    sb.append(quantifier.quantifierToString(1));
                }
                sb.append(literals.stream().map(Literal::toString).sorted().collect(Collectors.joining(" | ")));
            }
            this.partiallyCannonic = sb.toString();
        }
        return ignoreSecondVariableIfNotUsed ? this.partiallyCannonic : fullyCannonic;
    }

    public void freeze() {
        this.frozen = true;
    }

    public boolean isFrozen() {
        return this.frozen;
    }
}