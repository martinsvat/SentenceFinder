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

package ida.ilp.logic;

import ida.ilp.logic.quantifiers.Quantifier;
import ida.ilp.logic.quantifiers.TwoQuantifiers;
import ida.sentences.SentenceState;
import ida.sentences.caches.ClausesCache;
import ida.sentences.caches.LiteralsCache;
import ida.utils.Sugar;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;

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
    public static final String LITERALS_DELIMITER = " " + DELIMITER + " ";

    private LinkedHashSet<Literal> literals = new LinkedHashSet<Literal>();

    private MultiMap<String, Literal> literalsByName;

    private MultiMap<Term, Literal> literalsByTerms;

    private int hashCode = -1;

    private Quantifier quantifier = null;

    private Clause quantifierExtended;
    private Clause negationRepresentation;
    private Boolean cliffhanger;
    private Boolean decomposable;
    private String fullyCannonic;
    private Set<Pair<String, Integer>> predicates;
    private Clause swap;
    private SentenceState sentence;
    private int idx = -1;

    public Clause() {
    }

    public Clause(Quantifier quantifier, Iterable<? extends Literal> literals) {
        this(literals);
        this.quantifier = quantifier;
    }

    public Clause(Quantifier quantifier, Literal... literals) {
        this(literals);
        this.quantifier = quantifier;
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

    public static Clause create(Quantifier quantifier, Collection<Literal> literals) {
        return new Clause(quantifier, literals);
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
        // TODO cache this using variableSet cache !!!
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

    public static Clause parseWithQuantifier(String str) {
        str = str.trim();

        Integer id = null;
        if (str.startsWith("[")) {
            String[] split = str.substring(1).split("]", 2);
            id = Integer.parseInt(split[0]);
            str = split[1].trim();
        }

        if (str.startsWith("(") && str.endsWith(")")) {
            str = str.substring(1, str.length() - 1);
        }
        Pair<Quantifier, String> pair = Quantifier.parseAndGetRest(str);
        Clause clause = new Clause(pair.getR(), parse(pair.getS()).literals);
        if (null != id) {
            clause.setId(id);
        }
        return ClausesCache.getInstance().get(clause);
    }

    public static Clause parse(String str, char literalSeparator, Quantifier quantifier) {
        LiteralsCache literalsCache = LiteralsCache.getInstance();
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
                Literal literal = Literal.parseLiteral(s, variables, constants);
                parsedLiterals.add(literalsCache.get(literal));
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
                quantifiersEqual = this.quantifier.getQuantifiers().equals(c.quantifier.getQuantifiers())
                        && (this.quantifier.getUsedVariables() == c.quantifier.getUsedVariables()
                        || this.quantifier.getUsedVariables().equals(c.quantifier.getUsedVariables())) // ugly hack, this should be insie quantifier
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

    public String toFOL() {
        return toFOL(false);
    }

    public String toFOL(boolean printFeatures) {
        return //(printFeatures && this.isFrozen() ? "*" : "") +
                (null == quantifier ? "" : quantifier.getPrefix())
                        + " " + this.literals.stream().map(Literal::toString).collect(Collectors.joining(" " + DELIMITER + " "));
    }

    public Quantifier getQuantifier() {
        return quantifier;
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
            this.quantifierExtended = toExtendedClause();
        }
        return this.quantifierExtended;
    }

    private Clause toExtendedClause() {
        List<Literal> literals = Sugar.listFromCollections(this.literals);
        literals.addAll(this.quantifier.getRepresentation(this.isDecomposable()));
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


    // TODO merge with the one below?
    public String quantifierToName() {
        // if addSecond is false, only the first one is given
        String firstVariableConstraint = quantifier.isCountingQuantifier() && quantifier.firstVariableCardinality > -1 ? "" + quantifier.firstVariableCardinality : "";
        String secondVariableConstraint = quantifier.isCountingQuantifier() && quantifier.secondVariableCardinality > -1 ? "" + quantifier.secondVariableCardinality : "";
        switch (quantifier.getQuantifiers()) {
            case FORALL:
                return "Forall";
            case EXISTS:
                return "Exists" + firstVariableConstraint;
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
    }

    // TODO merge with the one above?
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

    public String getProver9Format() {
        if (hasCountingQuantifier()) {
            throw new IllegalStateException();
        }
        StringBuilder sb = new StringBuilder();
        sb.append(TwoQuantifiers.startsWithForall(quantifier.getQuantifiers()) ? "all" : "exists").append(" ").append(quantifier.getVariable(0)).append(" ");
        if (quantifier.numberOfUsedVariables > 1) {
            sb.append(TwoQuantifiers.FORALL_EXISTS == quantifier.getQuantifiers() || TwoQuantifiers.EXISTS_EXISTS == quantifier.getQuantifiers() ? "exists" : "all").append(" ").append(quantifier.getVariable(1)).append(" ");
        }
        sb.append("(");
        sb.append(toString(" | ", "-"));
        sb.append(")");
        sb.append(".");
        return sb.toString();
    }

    public boolean isCliffhanger() {
        if (null == cliffhanger) {
            cliffhanger = countLiterals() == 1 && !hasCountingQuantifier() &&
                    ((TwoQuantifiers.FORALL == quantifier.getQuantifiers() && 1 == Sugar.chooseOne(getPredicates()).getS()) // Vx U(x) or Vx ~U(x)
                            || (TwoQuantifiers.FORALL_FORALL == quantifier.getQuantifiers() && 2 == variables().size()) // Vx Vy B(x,y) or whatever similar except Vx B(x,x)
                    );
        }
        return cliffhanger;
    }

    public boolean hasCountingQuantifier() {
        if (null == this.quantifier) {
            return false;
        }
        return this.quantifier.isCountingQuantifier();
    }

    public boolean isDecomposable() {
        if (null == decomposable) {
            // the exact, general, approach would be
            // this.decomposable = connectedComponents().size() != 1;
            // our 2-variable approach allows for doing this
//            this.decomposable = true;
            if (null == quantifier) {
                this.decomposable = false;
            } else {
                this.decomposable = 2 == quantifier.numberOfUsedVariables;
                for (Literal literal : literals) {
                    if (literal.getVariableSet().size() > 1) {
                        this.decomposable = false;
                        break;
                    }
                }
            }
        }
        return decomposable;
    }

    public String getCannonic() {
        return getCannonic(false);
    }

    public String getCannonic(boolean printNumber) {
        if (null == this.fullyCannonic) {
            if (null == this.quantifier) {
                this.fullyCannonic = toFOL();
            } else {
                this.fullyCannonic = "(" + this.quantifier.getPrefix() + " " + literals.stream().map(Literal::toString).sorted().collect(Collectors.joining(LITERALS_DELIMITER)) + ")";
                if (isQuantifierSwitchable()) {
                    String mirror = "(" + this.quantifier.getMirror().getPrefix() + " " + literals.stream().map(Literal::getMirror).map(Literal::toString).sorted().collect(Collectors.joining(LITERALS_DELIMITER)) + ")";
                    if (this.fullyCannonic.compareTo(mirror) > 0) {
                        this.fullyCannonic = mirror;
                    }
                }
            }
        }
        return printNumber ? ("[" + getId() + "] " + this.fullyCannonic) : this.fullyCannonic;
    }

    // TODO most likely, shift this into quantifier :))
    private boolean isQuantifierSwitchable() {
        if (quantifier.isCountingQuantifier()) { // we cannot switch Vx E=1y B(x,y) the other way around E=1x Vy B(y,x)
            return TwoQuantifiers.EXISTS_EXISTS == quantifier.getQuantifiers() && quantifier.firstVariableCardinality == quantifier.secondVariableCardinality;
            // TODO what about decomposable Vx E=k y vs E=k x Vy ???
            // TODO here should be decomposible otherwise :)) !!!!!
        } else if (TwoQuantifiers.FORALL_FORALL == quantifier.getQuantifiers() || TwoQuantifiers.EXISTS_EXISTS == quantifier.getQuantifiers()) {
            return true;
        } else if (TwoQuantifiers.FORALL == quantifier.getQuantifiers() || TwoQuantifiers.EXISTS == quantifier.getQuantifiers()) {
            return false;
        }
        return isDecomposable(); // VxEy \phi(x) | \ro(y) or ExVy \phi(y) | \ro(x)
    }

    public Clause swap() {
        synchronized (this) {
            if (null == this.swap) {
                swap = ClausesCache.getInstance().get(new Clause(this.quantifier, literals.stream().map(Literal::getMirror).collect(Collectors.toList())));
                swap.swap = this;
            }
        }
        return swap;
    }

    public Set<Pair<String, Integer>> getPredicates() {
        synchronized (this) {
            if (null == predicates) {
                // TODO cache this & use overall cache
                predicates = literals.stream().map(Literal::getPredicate).collect(Collectors.toSet());
            }
        }
        return predicates;
    }

    public void setSentence(SentenceState sentenceState) {
        this.sentence = sentenceState;
    }

    public SentenceState getSentence() {
        return this.sentence;
    }

    public int getId() {
        return idx;
    }

    public void setId(int idx) {
        this.idx = idx;
    }

    public Clause getMirror() {
        if (1 == quantifier.numberOfUsedVariables) {
            return this;
        }
        return new Clause(quantifier.getMirror(), literals.stream().map(Literal::getMirror).toList());
    }
}