package search.sentences;

import search.ilp.logic.*;
import search.ilp.logic.subsumption.Matching;
import search.utils.Combinatorics;

import search.ilp.logic.*;

import search.utils.Sugar;
import search.utils.tuples.Pair;

import java.util.*;
import java.util.stream.Collectors;

public class SentenceState {
    private static final String CLAUSES_DELIMITER = " & ";
    public final SentenceSetup setup;
    public final List<Clause> clauses;
    public static final Matching isomorphisMatching = new Matching();
    private boolean containsSecondUnusedVariable;
    private int[] quantifierDistribution;
    private boolean decomposableForallExists;
    private List<Clause> predicateIsomorphicFullyQuantified;
    private List<Clause> predicateIsomorphic;
    private Set<Pair<String, Integer>> predicates;
    private Clause cellGraph;
    private String fullyCannonic;
    private String partiallyCannonic;

    public SentenceState(List<Clause> clauses, SentenceSetup setup) {
        this.clauses = clauses;
        this.setup = setup;
    }

    public static SentenceState create(SentenceSetup setup) {
        return create(Sugar.list(), setup);
    }

    public static List<SentenceState> parseMultiplePossibleQuantifiers(String line, HashMap<String, Quantifier> quantifierCache, Map<String, Literal> literalCache, SentenceSetup setup) {
        List<List<Clause>> parsedClauses = Sugar.list();

        for (String quantifiedClauseString : line.split(CLAUSES_DELIMITER)) {
            quantifiedClauseString = quantifiedClauseString.trim();
            if (!quantifiedClauseString.startsWith("(") || !quantifiedClauseString.endsWith(")")) {
                throw new IllegalStateException("Cannot parse part of input sentence:\t" + quantifiedClauseString + "\t of sentence\t" + line);
            }
            quantifiedClauseString = quantifiedClauseString.substring(1, quantifiedClauseString.length() - 1).trim();
            boolean found = false;
            for (Map.Entry<String, Quantifier> quantifier : quantifierCache.entrySet()) {
                if (quantifiedClauseString.startsWith(quantifier.getKey())) {
                    parsedClauses.add(Sugar.list(Clause.parse(quantifiedClauseString.substring(quantifier.getKey().length()),
                            Clause.DELIMITER,
                            quantifier.getValue())));
                    found = true;
                    break;
                }
            }

            if (!found) {
                List<Clause> partials = Sugar.list();
                for (Map.Entry<String, Quantifier> quantifier : quantifierCache.entrySet()) {
                    String partialQuantifier = quantifier.getKey();
                    int nthOccurence = nthOccurence(' ', 2, partialQuantifier);
                    partialQuantifier = partialQuantifier.substring(0, nthOccurence);
                    if (quantifiedClauseString.startsWith(partialQuantifier)) {
                        partials.add(Clause.parse(quantifiedClauseString.substring(partialQuantifier.length()),
                                Clause.DELIMITER,
                                quantifier.getValue()));
                    }
                }
                parsedClauses.add(partials);
                if (parsedClauses.isEmpty()) {
                    throw new IllegalStateException("Cannot parse quantifier of\t" + quantifiedClauseString + "\t of sentence\t" + line);
                }
            }
        }

        List<SentenceState> result = Sugar.list();
        SentenceState emptyState = SentenceState.create(setup);
        addEachSingleVariation(0, parsedClauses, emptyState, result);
        return result;
    }

    private static int nthOccurence(char c, int n, String string) {
        int idx = -1;
        while (true) {
            idx = string.indexOf(c, idx + 1);
            if (idx < 0) {
                return -1;
            }
            n--;
            if (0 == n) {
                return idx;
            }
        }
    }

    private static void addEachSingleVariation(int idx, List<List<Clause>> parsedClauses, SentenceState sentence, List<SentenceState> accumulator) {
        if (idx < 0 || idx > parsedClauses.size()) {
            return;
        } else if (parsedClauses.size() == idx) {
            accumulator.add(sentence);
        } else {
            for (Clause clause : parsedClauses.get(idx)) {
                addEachSingleVariation(idx + 1, parsedClauses, sentence.extend(clause), accumulator);
            }
        }
    }

    public SentenceState extend(Clause clause) {
        List<Clause> list = Sugar.listFromCollections(clauses);
        list.add(clause);
        return new SentenceState(list, setup);
    }

    public boolean containsIsomorphicClause(Clause clause, boolean ignoreSecondVariableIfNotUsed) {
        for (Clause innerClause : clauses) {
            if (setup.lexicographicalComparatorOnly
                    ? innerClause.isLexicographicallySame(clause, ignoreSecondVariableIfNotUsed)
                    : areIsomorphic(innerClause, clause, ignoreSecondVariableIfNotUsed)) {
                return true;
            }
        }
        return false;
    }

    public String toFol() {
        return toFol(true, false);
    }

    public String toFol(boolean printQuantifiers, boolean fullQuantifiers) {
        return toFol(printQuantifiers, fullQuantifiers, false);
    }

    public String toFol(boolean printQuantifiers, boolean fullQuantifiers, boolean printFeatures) {
        return clauses.stream().map(clause -> "(" + clause.toFOL(printQuantifiers, fullQuantifiers, printFeatures) + ")").collect(Collectors.joining(CLAUSES_DELIMITER));
    }

    public SentenceState getWFOMCSkolemization(SkolemizationFactory factory) {
        return new SentenceState(clauses.stream().flatMap(clause -> clause.getWFOMCSkolemization(factory).clauses.stream()).collect(Collectors.toList()), null);
    }

    public SentenceState getWFOMCSkolemization() {
        return getWFOMCSkolemization(SkolemizationFactory.getInstance());
    }

    private static SentenceState create(List<Clause> clauses, SentenceSetup setup) {
        return new SentenceState(clauses, setup);
    }

    public int getNumberOfClauses() {
        return this.clauses.size();
    }

    public SentenceState refineByExtendingClause(Clause originalClause, Literal singleLiteralExtension) {
        List<Clause> copiedClauses = Sugar.list();
        for (Clause innerClause : this.clauses) {
            if (innerClause == originalClause) {
                innerClause = new Clause(originalClause.getQuantifier(), Sugar.listFromCollections(innerClause.literals(), Sugar.list(singleLiteralExtension)));
            }
            copiedClauses.add(innerClause);
        }
        return new SentenceState(copiedClauses, setup);
    }

    public IsomorphismType isPredicateIsomorphic(SentenceState other) {
        if (!hasEqualQuantifierDistribution(other.getQuantifierDistribution())) {
            return IsomorphismType.NONE;
        }

        Clause myPartialRepresentation = predicateIsomorphic.get(0);
        Clause myFullRepresentation = predicateIsomorphicFullyQuantified.get(0);
        Pair<List<Clause>, List<Clause>> repre = other.getPredicateIsomorphicRepresentation();
//        int max = repre.getR().size() > howManyFlips ? howManyFlips : repre.getR().size();
//        for (int idx = 0; idx < max; idx++) {
        for (int idx = 0; idx < repre.getR().size(); idx++) {
            Clause partialRepresentation = repre.getR().get(idx);
            Clause fullRepresentation = repre.getS().get(idx);
            if (isomorphisMatching.isomorphism(myPartialRepresentation, partialRepresentation)) { // TODO make this faster using ICW
                if (containsSecondUnusedVariable() || decomposableForallExists) {
                    return isomorphisMatching.isomorphism(myFullRepresentation, fullRepresentation) ? IsomorphismType.YES : IsomorphismType.YES_WITH_SECOND_UNUSED_VARIABLE;
                }
                return IsomorphismType.YES;
            }
        }
        return IsomorphismType.NONE;
    }

    public Pair<List<Clause>, List<Clause>> getPredicateIsomorphicRepresentation() {
        // i.e. meaning when withFullQuantifiers is true, even unused variables are added into quantifier literals; otherwise only those used
        if (null == predicateIsomorphic || null == predicateIsomorphicFullyQuantified) {
            precomputePredicateIsomorphism();
        }
        return new Pair<>(predicateIsomorphic, predicateIsomorphicFullyQuantified);
    }

    private boolean hasEqualQuantifierDistribution(int[] quantifierDistribution) {
        if (null == this.quantifierDistribution) {
            precomputePredicateIsomorphism();
        }
        for (int idx = 0; idx < this.quantifierDistribution.length; idx++) {
            if (quantifierDistribution[idx] != this.quantifierDistribution[idx]) {
                return false;
            }
        }
        return true;
    }

    private int[] getQuantifierDistribution() {
        if (null == quantifierDistribution) {
            precomputePredicateIsomorphism();
        }
        return quantifierDistribution;
    }

    public boolean hasDecomposableForallExists() {
        if (null == quantifierDistribution) {
            precomputePredicateIsomorphism();
        }
        return decomposableForallExists;
    }

    public boolean containsSecondUnusedVariable() {
        if (null == quantifierDistribution) {
            precomputePredicateIsomorphism();
        }
        return this.containsSecondUnusedVariable;
    }

    private void precomputePredicateIsomorphism() {
        // precomputing distribution and usage of the second variable
        quantifierDistribution = new int[8];
        for (Clause clause : clauses) {
            boolean secondVariableUsed = clause.isSecondVariableUsed();
            this.containsSecondUnusedVariable |= !secondVariableUsed;
            if (clause.hasCountingQuantifier()) {
                // it would not be static, but rather dynamic (i.e. mapping of counting-quantifiers, ets...)
                quantifierDistribution[6]++;
            } else {
                if (secondVariableUsed) {
                    switch (clause.getQuantifier().getQuantifiers()) {
                        case FORALL_FORALL:
                            quantifierDistribution[0]++;
                            break;
                        case FORALL_EXISTS:
                            if (clause.isDecomposable()) {
                                quantifierDistribution[7]++;
                            } else {
                                quantifierDistribution[1]++;
                            }
                            break;
                        case EXISTS_FORALL:
                            if (clause.isDecomposable()) {
                                quantifierDistribution[7]++;
                            } else {
                                quantifierDistribution[2]++;
                            }
                            break;
                        case EXISTS_EXISTS:
                            quantifierDistribution[3]++;
                            break;
                        default:
                            break;
                    }
                } else {
                    if (TwoQuantifiers.startsWithForall(clause.getQuantifier().getQuantifiers())) {
                        // V x
                        quantifierDistribution[4]++;
                    } else {
                        // E x
                        quantifierDistribution[5]++;
                    }
                }
            }
        }

        this.decomposableForallExists = clauses.stream().anyMatch(clause -> clause.isSecondVariableUsed()
                && (TwoQuantifiers.FORALL_EXISTS == clause.getQuantifier().getQuantifiers() || TwoQuantifiers.EXISTS_FORALL == clause.getQuantifier().getQuantifiers())
                && clause.isDecomposable());
        predicateIsomorphic = Sugar.list();
        predicateIsomorphicFullyQuantified = Sugar.list();
        // precomputing predicate-isomorphism representation
        List<List<Pair<String, Integer>>> flips = Sugar.list();
        List<Pair<String, Integer>> binaryPredicates = Sugar.listFromCollections(getBinaryPredicates());
        if (setup.symmetryFlip) {
            // swaps
            for (int k = 0; k <= binaryPredicates.size(); k++) {
                flips.addAll(Combinatorics.subset(binaryPredicates, k));
            }
        } else {
            flips.add(Sugar.list());// default
        }
        for (List<Pair<String, Integer>> flip : flips) {
            Pair<Clause, Clause> pair = computeRepresentationWith(flipDirection(clauses, Sugar.setFromCollections(flip)), containsSecondUnusedVariable);
            predicateIsomorphic.add(pair.getR());
            predicateIsomorphicFullyQuantified.add(pair.getS());
        }
    }

    private Set<Pair<String, Integer>> getBinaryPredicates() {
        Set<Pair<String, Integer>> result = Sugar.set();
        for (Clause clause : clauses) {
            for (Pair<String, Integer> predicate : LogicUtils.predicates(clause)) {
                if (predicate.getS() == 2) {
                    result.add(predicate);
                }
            }
        }
        return result;
    }

    private Pair<Clause, Clause> computeRepresentationWith(List<Clause> clauses, boolean containsSecondUnusedVariable) {
        List<Literal> quantifiers = Sugar.list();
        List<Literal> fullQuantifiers = Sugar.list();
        List<Literal> representation = Sugar.list();
        int clauseIndex = 0;
        Supplier<? extends Term> unarySupplier = setup.isoPredicateNames ? VariableSupplier.create("u") : IdentitySupplier.create();
        Supplier<? extends Term> binarySupplier = setup.isoPredicateNames ? VariableSupplier.create("b") : IdentitySupplier.create();
        VariableSupplier variableSupplier = VariableSupplier.create("x");
        Supplier<? extends Term> unarySignSupplier = setup.isoSings ? VariableSupplier.create("su") : SingSupplier.create();
        Supplier<? extends Term> binarySignSupplier = setup.isoSings ? VariableSupplier.create("bu") : SingSupplier.create();
        List<Variable> clausesVariables = Sugar.list();
        for (Clause clause : clauses) {
            if (clause.literals().isEmpty()) {
                continue;
            }
            if (!clause.isFirstVariableUsed()) {
                throw new IllegalStateException();
            }
            Variable clauseVariable = Variable.construct("c" + clauseIndex++);
            clausesVariables.add(clauseVariable);

            // quantifiers part
            List<Literal> quantifier = Sugar.list();
            if (!clause.hasCountingQuantifier()
                    && ((clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_FORALL
                    || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_EXISTS))) {
                String name = TwoQuantifiers.startsWithForall(clause.getQuantifier().getQuantifiers()) ? "For2" : "Exi2";
                quantifier.add(new Literal(name,
                        variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                        clauseVariable));
                quantifier.add(new Literal(name,
                        variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                        clauseVariable));
            } else { // counting quantifiers
                quantifier.add(new Literal(clause.quantifierToName(true),
                        variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                        variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                        clauseVariable));
            }
            fullQuantifiers.addAll(quantifier);
            if (clause.isSecondVariableUsed()) {
                if ((TwoQuantifiers.FORALL_EXISTS == clause.getQuantifier().getQuantifiers() || TwoQuantifiers.EXISTS_FORALL == clause.getQuantifier().getQuantifiers())
                        && clause.isDecomposable()) {
                    quantifiers.add(new Literal(clause.singleVariableQuantifierToName(0),
                            variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                            clauseVariable));
                    quantifiers.add(new Literal(clause.singleVariableQuantifierToName(1),
                            variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                            clauseVariable));
                } else {
                    quantifiers.addAll(quantifier);
                }
            } else {
                quantifiers.add(new Literal(clause.quantifierToName(false),
                        variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                        clauseVariable));
            }

            // literals part
            for (Literal literal : clause.literals()) {
                if (1 == literal.arity()) {
                    representation.add(new Literal("P", unarySupplier.get(literal.predicate()),
                            unarySignSupplier.get((literal.isNegated() ? "!" : "") + literal.predicate()),
                            variableSupplier.get(literal.get(0).name() + clauseIndex), clauseVariable));
                } else if (2 == literal.arity()) {
                    representation.add(new Literal("R", binarySupplier.get(literal.predicate()),
                            binarySignSupplier.get((literal.isNegated() ? "!" : "") + literal.predicate()),
                            variableSupplier.get(literal.get(0).name() + clauseIndex), variableSupplier.get(literal.get(1).name() + clauseIndex), clauseVariable));
                } else {
                    throw new IllegalStateException();
                }
            }
        }

        for (Term variable : unarySupplier.values()) {
            representation.add(new Literal("Unary", variable));
        }
        for (Term variable : binarySupplier.values()) {
            representation.add(new Literal("Binary", variable));
        }
        for (Term variable : clausesVariables) {
            representation.add(new Literal("Clause", variable));
        }
        for (Term variable : unarySignSupplier.values()) {
            representation.add(new Literal("UnarySing", variable));
        }
        for (Term variable : binarySignSupplier.values()) {
            representation.add(new Literal("BinarySing", variable));
        }
        Clause predicateIsomorphic = new Clause(Sugar.union(representation, quantifiers));
        Clause predicateIsomorphicFullyQuantified = containsSecondUnusedVariable || decomposableForallExists ? new Clause(Sugar.union(representation, fullQuantifiers)) : predicateIsomorphic;
        return new Pair<>(predicateIsomorphic, predicateIsomorphicFullyQuantified);
    }

    private List<Clause> flipDirection(List<Clause> clauses, Set<Pair<String, Integer>> flip) {
        List<Clause> result = Sugar.list();
        boolean overallFlip = false;
        for (Clause clause : clauses) {
            boolean flipUsed = false;
            List<Literal> change = Sugar.list();
            for (Literal literal : clause.literals()) {
                if (flip.contains(literal.getPredicate())) {
                    flipUsed = true;
                    change.add(BinaryFlipCache.getInstance().getFlip(literal));
                } else {
                    change.add(literal);
                }
            }
            overallFlip |= flipUsed;
            result.add(flipUsed ? new Clause(clause.getQuantifier(), change) : clause);
        }
        return overallFlip ? result : clauses;
    }

    private boolean areIsomorphic(Clause first, Clause second, boolean ignoreSecondVariableIfNotPresent) {
        // todo sadly, this should be unified with the other method in SentenceFinder as they are the same!

        // here, we do not mess with isDecomposable
        if (!first.isSecondVariableUsed() && !second.isSecondVariableUsed() && ignoreSecondVariableIfNotPresent) {
            if ((TwoQuantifiers.startsWithForall(first.getQuantifier().getQuantifiers()) && TwoQuantifiers.startsWithForall(second.getQuantifier().getQuantifiers()))
                    || (TwoQuantifiers.startsWithExists(first.getQuantifier().getQuantifiers()) && TwoQuantifiers.startsWithExists(second.getQuantifier().getQuantifiers()) && first.getQuantifier().hasSameCardinalityConstraintOnVariable(second.getQuantifier(), 0))
            ) {
                return isomorphisMatching.isomorphism(first.getQuantifierExtendedClause(), second.getQuantifierExtendedClause());
            } else {
                return false;
            }
        }

        if (first.hasSameQuantifier(second)) {
            if (first.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_EXISTS
                    || first.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL
                    || first.hasCountingQuantifier()) {
                return isomorphisMatching.isomorphism(first.getQuantifierExtendedClause(), second.getQuantifierExtendedClause());
            } else {
                return isomorphisMatching.isomorphism(first, second);
            }
        } else {
            return false;
        }
    }

    public String toString() {
        return toString(true);
    }


    public String toString(boolean printQuantifiers) {
        if (this.clauses.isEmpty()) {
            return "{}";
        }
        return toFol(printQuantifiers, false);
    }


    public String getOutputPrenexAndSkolemForm(String delimiter) {
        for (Clause clause : clauses) {
            if (clause.hasCountingQuantifier()) {
                return "~";
            }
        }
        SentenceState skolemized = getWFOMCSkolemization(SkolemizationFactory.getOneFromStart());
//        return skolemized.prenexFormat() + delimiter + skolemized.toString(false);
        return skolemized.toString(false);
    }

    private String prenexFormat() {
        if (this.clauses.isEmpty()) {
            return "{}";
        }
        StringBuilder forall = new StringBuilder();
        StringBuilder exists = new StringBuilder();
        List<Clause> renamedClauses = Sugar.list();

        long variables = 0L;
        for (Clause clause : clauses) {
            HashMap<Term, Term> mapping = new HashMap<>();
            if (null == clause.getQuantifier()) { // case generated by FOL-skolemization
                for (Variable variable : clause.variables()) {
                    Variable newVariable = Variable.construct("x" + variables++);
                    forall.append("V ").append(newVariable).append(" ");
                    mapping.put(variable, newVariable);
                }
            } else {
                if (clause.isFirstVariableUsed()) {
                    Variable newVariable = Variable.construct("x" + variables++);
                    mapping.put(clause.getQuantifier().getVariable(0), newVariable);
                    if (clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_FORALL || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_EXISTS) {
                        forall.append("V ").append(newVariable).append(" ");
                    } else {
                        exists.append("E ").append(newVariable).append(" ");
                    }
                }

                if (clause.isSecondVariableUsed()) {
                    Variable newVariable = Variable.construct("x" + variables++);
                    mapping.put(clause.getQuantifier().getVariable(1), newVariable);
                    if (clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_FORALL || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL) {
                        forall.append("V ").append(newVariable).append(" ");
                    } else {
                        exists.append("E ").append(newVariable).append(" ");
                    }
                }
            }
            renamedClauses.add(LogicUtils.substitute(clause, mapping));
        }

        forall.append(" ");
        forall.append(exists);
        forall.append(" ");
        forall.append(renamedClauses.stream().map(clause -> "(" + clause.toFOL(false, false) + ")").collect(Collectors.joining(CLAUSES_DELIMITER)));
        return forall.toString();
    }

    public String debugOutput(boolean debug) {
        if (debug) {
            return "\t" + toFol(true, true);
        }
        return "";
    }

    public static SentenceState parse(String line, Map<String, Quantifier> quantifierCache, SentenceSetup setup, Map<String, Literal> literalsCache) {
        // assuming fully bracket output
        if (line.trim().length() == 0) {
            return new SentenceState(Sugar.list(), setup);
        }

        List<Clause> clauses = Sugar.list();
        for (String quantifiedClause : line.split(CLAUSES_DELIMITER)) {
            quantifiedClause = quantifiedClause.trim();
            quantifiedClause = quantifiedClause.substring(1, quantifiedClause.length() - 1);
            boolean frozen = false;
            if (quantifiedClause.startsWith("*")) {
                frozen = true;
                quantifiedClause = quantifiedClause.substring(1);
            }
            Quantifier quantify = null;
            String literals = null;
            for (Map.Entry<String, Quantifier> entry : quantifierCache.entrySet()) {
                String plainText = entry.getKey();
                if (quantifiedClause.startsWith(plainText)) {
                    quantify = entry.getValue();
                    literals = quantifiedClause.substring(plainText.length());
                    break;
                }
            }
            if (null == quantify) {
                throw new IllegalStateException("Cannot parse quantifier\t" + quantifiedClause);
            }
            Clause clause = Clause.parse(literals, Clause.DELIMITER, quantify);
            if (frozen) {
                clause.freeze();
            }
            clauses.add(clause);
        }
        return new SentenceState(clauses, setup);
    }

    public boolean containsPredicate(Pair<String, Integer> predicate) {
        if (null == predicates) {
            cachePredicates();
        }
        return predicates.contains(predicate);
    }

    public Set<Pair<String, Integer>> getPredicates() {
        if (null == predicates) {
            cachePredicates();
        }
        return predicates;
    }

    private void cachePredicates() {
        if (clauses.isEmpty()) {
            predicates = new Set<Pair<String, Integer>>() {
                @Override
                public int size() {
                    return 0;
                }

                @Override
                public boolean isEmpty() {
                    return false;
                }

                @Override
                public boolean contains(Object o) {
                    return true;
                }

                @Override
                public Iterator<Pair<String, Integer>> iterator() {
                    return null;
                }

                @Override
                public Object[] toArray() {
                    return new Object[0];
                }

                @Override
                public <T> T[] toArray(T[] a) {
                    return null;
                }

                @Override
                public boolean add(Pair<String, Integer> stringIntegerPair) {
                    return false;
                }

                @Override
                public boolean remove(Object o) {
                    return false;
                }

                @Override
                public boolean containsAll(Collection<?> c) {
                    return false;
                }

                @Override
                public boolean addAll(Collection<? extends Pair<String, Integer>> c) {
                    return false;
                }

                @Override
                public boolean retainAll(Collection<?> c) {
                    return false;
                }

                @Override
                public boolean removeAll(Collection<?> c) {
                    return false;
                }

                @Override
                public void clear() {

                }
            };
        } else {
            predicates = Sugar.set();
            clauses.forEach(clause -> clause.literals().forEach(literal -> predicates.add(literal.getPredicate())));
        }
    }

    public Clause getCellGraph() {
        return cellGraph;
    }

    public void setCellGraph(Clause cellGraph) {
        this.cellGraph = cellGraph;
    }

    public boolean isCliffhanger() {
        for (Clause clause : clauses) {
            if (clause.isCliffhanger()) {
                return true;
            }
        }
        return false;
    }

    public String getFullyQuantifiedLexicographicallyMinimal() {
        if (null == fullyCannonic) {
            precomputeCannonicals();
        }
        return fullyCannonic;
    }

    public String getPartiallyQuantifiedLexicographicallyMinimal() {
        if (null == partiallyCannonic) {
            precomputeCannonicals();
        }
        return partiallyCannonic;
    }

    private void precomputeCannonicals() {
        this.fullyCannonic = clauses.stream().map(clause -> clause.getCannonic(false)).sorted().collect(Collectors.joining(CLAUSES_DELIMITER));
        this.partiallyCannonic = clauses.stream().map(clause -> clause.getCannonic(true)).sorted().collect(Collectors.joining(CLAUSES_DELIMITER));
    }

    public boolean areLexicographicallySame(SentenceState other) {
        return getFullyQuantifiedLexicographicallyMinimal().equals(other.getFullyQuantifiedLexicographicallyMinimal());
    }

    public void freezeAllClauses() {
        for (Clause clause : clauses) {
            clause.freeze();
        }
    }
}
