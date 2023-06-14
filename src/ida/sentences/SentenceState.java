package ida.sentences;

import ida.hypergraphIsomorphism.*;
import ida.ilp.logic.*;
import ida.ilp.logic.quantifiers.Quantifier;
import ida.ilp.logic.quantifiers.TwoQuantifiers;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.sentences.caches.LiteralsCache;
import ida.utils.Combinatorics;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;

import java.util.*;
import java.util.stream.Collectors;

public class SentenceState {
    private static final String CLAUSES_DELIMITER = " & ";
    public final SentenceSetup setup;
    public final List<Clause> clauses;
    private Set<Pair<String, Integer>> predicates;
    private Clause cellGraph;
    private String cannonic;
    private String ultraCannonic; // negation swaps, relations swap
    private IsoClauseWrapper icw;
    private String canonicalCellGraph;

    public SentenceState(List<Clause> clauses, SentenceSetup setup) {
        this.clauses = clauses;
        this.setup = setup;
    }

    public static SentenceState create(SentenceSetup setup) {
        return create(Sugar.list(), setup);
    }

    public SentenceState extend(Clause clause) {
        List<Clause> list = Sugar.listFromCollections(clauses);
        list.add(clause);
        return new SentenceState(list, setup);
    }

    public SentenceState extend(SentenceState sentence) {
        return new SentenceState(Sugar.listFromCollections(clauses, sentence.clauses), setup);
    }


    public String toFol() {
        return toFol(false);
    }

    public String toFol(boolean printFeatures) {
        return clauses.stream().map(clause -> "(" + clause.toFOL(printFeatures) + ")").collect(Collectors.joining(CLAUSES_DELIMITER));
    }


    private static SentenceState create(List<Clause> clauses, SentenceSetup setup) {
        return new SentenceState(clauses, setup);
    }

    public int getNumberOfClauses() {
        return this.clauses.size();
    }


    public IsoClauseWrapper getICW(LiteralsCache cache) {
        if (null == this.icw) {
            this.icw = IsoClauseWrapper.create(computeRepresentationWith(clauses, cache));
            this.icw.getOriginalClause().setSentence(this);
        }
        return this.icw;
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

    // TODO think about how making this method faster and nicer :)) profile it!
    private Clause computeRepresentationWith(List<Clause> clauses, LiteralsCache cache) {
        List<Literal> quantifiers = Sugar.list();
        List<Literal> representation = Sugar.list();
        int clauseIndex = 0;
        Supplier<? extends Term> unarySupplier = setup.isomorphicSentences ? VariableSupplier.create("u") : IdentitySupplier.create();
        Supplier<? extends Term> binarySupplier = setup.isomorphicSentences ? VariableSupplier.create("b") : IdentitySupplier.create();
        VariableSupplier variableSupplier = VariableSupplier.create("x");
        Supplier<? extends Term> unarySignSupplier = setup.negations ? VariableSupplier.create("su") : SingSupplier.create();
        Supplier<? extends Term> binarySignSupplier = setup.negations ? VariableSupplier.create("bu") : SingSupplier.create();
        BiVariableSupplier orderSupplier = setup.permutingArguments ? BiVariableSupplier.create("o", "i") : null;
        List<Variable> clausesVariables = Sugar.list();
        for (Clause clause : clauses) {
            if (clause.literals().isEmpty()) {
                continue;
            }
            Variable clauseVariable = Variable.construct("c" + clauseIndex++);
            clausesVariables.add(clauseVariable);

            // quantifiers part
            if (clause.hasCountingQuantifier()) {
                // TODO add E=k x E=k y case here! and also Ex E=k y \phi(x) | \ro(y) |=| E=k x E y \phi(y) | \ro(x)
                if ((clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_EXISTS || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL)
                        && clause.isDecomposable()) { // Vx E=k y or E=k y Vx with decomposable clause
                    quantifiers.add(new Literal(clause.singleVariableQuantifierToName(0),
                            variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                            clauseVariable));
                    quantifiers.add(new Literal(clause.singleVariableQuantifierToName(1),
                            variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                            clauseVariable));
                } else {
                    quantifiers.add(new Literal(clause.quantifierToName(),
                            variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                            variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                            clauseVariable));
                }
            } else if (clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL
                    || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS
                    || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_FORALL
                    || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_EXISTS) {
                String name = TwoQuantifiers.startsWithForall(clause.getQuantifier().getQuantifiers()) ? "F" : "E2";
                quantifiers.add(new Literal(name,
                        variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                        clauseVariable));
                if (2 == clause.getQuantifier().numberOfUsedVariables) {
                    quantifiers.add(new Literal(name,
                            variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                            clauseVariable));
                }
            } else {// VxEy & ExVy cases
                if (clause.isDecomposable()) {
                    quantifiers.add(new Literal(clause.singleVariableQuantifierToName(0),
                            variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                            clauseVariable));
                    quantifiers.add(new Literal(clause.singleVariableQuantifierToName(1),
                            variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                            clauseVariable));
                } else {
                    quantifiers.add(new Literal(clause.quantifierToName(),
                            variableSupplier.get(clause.getQuantifier().getVariable(0).name() + clauseIndex),
                            variableSupplier.get(clause.getQuantifier().getVariable(1).name() + clauseIndex),
                            clauseVariable));
                }
            }

            // literals part
            for (Literal literal : clause.literals()) {
                if (1 == literal.arity()) {
                    representation.add(new Literal("P", unarySupplier.get(literal.predicate()),
                            unarySignSupplier.get((literal.isNegated() ? "!" : "") + literal.predicate()),
                            variableSupplier.get(literal.get(0).name() + clauseIndex), clauseVariable));
                } else if (2 == literal.arity()) {
                    String predicateName = "R";
                    Term predicate = binarySupplier.get(literal.predicate());
                    Term sign = binarySignSupplier.get((literal.isNegated() ? "!" : "") + literal.predicate());
                    Variable x = variableSupplier.get(literal.get(0).name() + clauseIndex);
                    Variable y = variableSupplier.get(literal.get(1).name() + clauseIndex);
                    if (null != orderSupplier) {
                        Pair<Variable, Variable> order = orderSupplier.get(predicate.name() + "o");
                        Literal originalOrder = new Literal(predicateName, predicate, sign, x, y, clauseVariable, order.getR());
                        Literal flippedOrder = new Literal(predicateName, predicate, sign, y, x, clauseVariable, order.getS());
                        representation.add(originalOrder);
                        representation.add(flippedOrder);
                    } else {
                        Literal originalOrder = new Literal(predicateName, predicate, sign, x, y, clauseVariable);
                        representation.add(originalOrder);
                    }
                } else {
                    throw new IllegalStateException();
                }
            }
        }

        for (Term variable : unarySupplier.values()) {
            representation.add(new Literal("Up", variable)); // unary
        }
        for (Term variable : binarySupplier.values()) {
            representation.add(new Literal("Bp", variable)); // binary
        }
        for (Term variable : clausesVariables) {
            representation.add(new Literal("C", variable)); // clause
        }
        for (Term variable : unarySignSupplier.values()) {
            representation.add(new Literal("Us", variable)); // unary sing
        }
        for (Term variable : binarySignSupplier.values()) {
            representation.add(new Literal("Bs", variable)); // binary sing
        }
        if (null != orderSupplier) {
            for (Map.Entry<String, Pair<Variable, Variable>> entry : orderSupplier.getMap().entrySet()) {
                Variable variable = Variable.construct(entry.getKey());
                representation.add(new Literal("Or", variable, entry.getValue().getR())); // order
                representation.add(new Literal("Or", variable, entry.getValue().getS())); // order
            }
        }

        List<Literal> isoRepresentation = Sugar.list();
        for (Literal literal : representation) {
            isoRepresentation.add(cache.get(literal));
        }
        for (Literal literal : quantifiers) {
            isoRepresentation.add(cache.get(literal));
        }

        return new Clause(isoRepresentation);
//        return new Clause(Sugar.union(representation, quantifiers));
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
                    change.add(literal.getFlipped());
                } else {
                    change.add(literal);
                }
            }
            overallFlip |= flipUsed;
            result.add(flipUsed ? new Clause(clause.getQuantifier(), change) : clause);
        }
        return overallFlip ? result : clauses;
    }

    private Clause flipDirection(Clause clause, Collection<Predicate> flip) {
        boolean flipUsed = false;
        List<Literal> change = Sugar.list();
        for (Literal literal : clause.literals()) {
            if (flip.contains(literal.pred())) {
                flipUsed = true;
                change.add(literal.getFlipped());
            } else {
                change.add(literal);
            }
        }
        return flipUsed ? new Clause(clause.getQuantifier(), change) : clause;
    }

    public String toString() {
        if (this.clauses.isEmpty()) {
            return "{}";
        }
        return toFol();
    }


    public String debugOutput(boolean debug) {
        if (debug) {
            return "\t" + toFol();
        }
        return "";
    }

    public static SentenceState parse(String line) {
        return parse(line, null);
    }

    public static SentenceState parse(String line, SentenceSetup setup) {
        // assuming fully bracket output
        if (line.trim().length() == 0) {
            return new SentenceState(Sugar.list(), setup);
        }

        List<Clause> clauses = Sugar.list();
        for (String quantifiedClause : line.split(CLAUSES_DELIMITER)) {
            quantifiedClause = quantifiedClause.trim();
            quantifiedClause = quantifiedClause.substring(1, quantifiedClause.length() - 1);
            Clause clause = Clause.parseWithQuantifier(quantifiedClause);
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
            // TODO cache this & use overall cache
            cachePredicates();
        }
        return predicates;
    }

    private void cachePredicates() {
        if (clauses.isEmpty()) {
            predicates = Sugar.set();
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

    public String getCannonic() {
        if (null == cannonic) {
            this.cannonic = clauses.stream().map(Clause::getCannonic).sorted().collect(Collectors.joining(CLAUSES_DELIMITER));
        }
        return cannonic;
    }

    public String getUltraCannonic() {
        if (null == ultraCannonic) {
            Set<Pair<String, Integer>> originalUnary = getPredicates();
            Set<Pair<String, Integer>> originalBinary = getBinaryPredicates(); // TODO why so complicated???

            List<Predicate> unary = fetchMinimalPredicates(originalUnary, 1);
            List<Predicate> binary = fetchMinimalPredicates(originalBinary, 2);

            List<Clause> canonPrefixes = toCannonPrefixes(toAnonymousPredicates(clauses));
            MultiList<Quantifier, Clause> grouped = groupByPrefixes(canonPrefixes);
            List<Quantifier> order = grouped.keySet().stream().sorted(Comparator.comparing(Quantifier::getPrefix)).toList();

            List<Clause> canonClause = createCannon(order, grouped, unary, binary, new HashMap<>(), Sugar.set(), Sugar.set()); // TODO for RL, may be return this instead :))
            this.ultraCannonic = canonClause.stream().map(Clause::getCannonic).sorted().collect(Collectors.joining(CLAUSES_DELIMITER));
        }
        return ultraCannonic;
    }

    private List<Clause> toAnonymousPredicates(List<Clause> clauses) {
        Map<Predicate, Predicate> map = new HashMap<>();
        List<Clause> retVal = Sugar.list();
        for (Clause clause : clauses) {
            List<Literal> lits = Sugar.list();
            for (Literal literal : clause.literals()) {
                if (!map.containsKey(literal.pred())) {
                    map.put(literal.pred(), Predicate.create("a" + map.keySet().size(), literal.arity()));
                }
//                Literal newLiteral = new Literal(map.get(literal.pred()).getName(), literal.isNegated(), literal.arguments());
                Literal newLiteral = LiteralsCache.getInstance().constructAndGet(map.get(literal.pred()).getName(), literal.isNegated(), literal.arguments());
                lits.add(newLiteral);
            }
            retVal.add(Clause.create(clause.getQuantifier(), lits));
        }
        return retVal;
    }

    private List<Clause> createCannon(List<Quantifier> order, MultiList<Quantifier, Clause> grouped, List<Predicate> unary, List<Predicate> binary, Map<Predicate, Predicate> predicateMapping, Set<Predicate> negationSwap, Set<Predicate> directionFlip) {
        if (order.isEmpty()) {
            return Sugar.list();
        }
        Quantifier quantifier = order.get(0);
        if (!grouped.containsKey(quantifier)) {
            throw new IllegalStateException();
        }
        List<Pair<String, List<Clause>>> results = Sugar.list();
        List<Clause> clausesToGo = Sugar.listFromCollections(grouped.get(quantifier));
//        System.out.println("* solving quantifier\t" + quantifier);
        for (Clause clause : clausesToGo) {
//            System.out.println("\t and " + clause.toFOL());
            Clause changed = getConsistent(clause, predicateMapping, negationSwap, directionFlip);
//            System.out.println("\t     -> " + changed.toFOL());
            List<Configuration> minimals = generateAllMinimals(changed, unary, binary, predicateMapping, negationSwap, directionFlip);
            grouped.get(quantifier).remove(clause);
            List<Quantifier> nextOrder = order;
            if (grouped.get(quantifier).isEmpty()) {
                nextOrder = order.subList(1, order.size());
            }
            if (minimals.isEmpty() || minimals.stream().map(c -> c.getClause().getCannonic()).collect(Collectors.toSet()).size() != 1) {
                throw new IllegalStateException();
            }
            String restMinimal = null;
            List<Clause> mins = null;
            for (Configuration config : minimals) { // instead, this could be done in a way that we take all clauses that are interconnected with decision mady in here
                List<Clause> rest = createCannon(nextOrder, grouped, config.freeUnary, config.freeBinary, config.mapping, config.negationSwap, config.directionSwap);
                String currentRest = rest.stream().map(Clause::getCannonic).sorted().collect(Collectors.joining(CLAUSES_DELIMITER));
                if (null == restMinimal || currentRest.compareTo(restMinimal) < 0) {
                    restMinimal = currentRest;
                    mins = rest;
                }
            }
            mins.add(minimals.get(0).getClause());
            results.add(new Pair<>(toCannon(mins), mins));
            grouped.put(quantifier, clause);
        }
        results.sort(Comparator.comparing(Pair::getR));
        return results.get(0).getS();
    }

    private List<Configuration> generateAllMinimals(Clause clause, List<Predicate> freeUnary, List<Predicate> freeBinary, Map<Predicate, Predicate> predicateMapping, Set<Predicate> negationSwap, Set<Predicate> directionFlip) {
        // if the original predicate is mapped, then its direction swap and negation is handled as well
        // get lexicographically minimal clause (or more if they equal) w.r.t. predicate names, negations, direction
        Set<Predicate> positivePredicates = Sugar.set();
        Set<Predicate> negativePredicates = Sugar.set();
        Set<Predicate> unsetUnary = Sugar.set();
        Set<Predicate> unsetBinary = Sugar.set();
        for (Literal literal : clause.literals()) {
            if (!predicateMapping.containsValue(literal.pred())) {
                if (1 == literal.arity()) {
                    unsetUnary.add(literal.pred());
                } else if (2 == literal.arity()) {
                    unsetBinary.add(literal.pred());
                }
                if (literal.isNegated()) {
                    negativePredicates.add(literal.pred());
                } else {
                    positivePredicates.add(literal.pred());
                }
            }
        }
        if (unsetUnary.isEmpty() && unsetBinary.isEmpty()) {// all is set from the previous steps!
            return Sugar.list(new Configuration(freeUnary, freeBinary, predicateMapping, negationSwap, directionFlip, clause));
        }
        String minimal = null;
        List<Configuration> all = Sugar.list();
        List<Map<Predicate, Predicate>> mappings = generateMappings(Sugar.listFromCollections(unsetUnary), freeUnary.subList(0, unsetUnary.size()),
                Sugar.listFromCollections(unsetBinary), freeBinary.subList(0, unsetBinary.size()));
        List<Predicate> binaryPredicates = freeBinary.subList(0, unsetBinary.size());
        List<Predicate> restUnary = freeUnary.subList(unsetUnary.size(), freeUnary.size());
        List<Predicate> restBinary = freeBinary.subList(unsetBinary.size(), freeBinary.size());
        Set<Predicate> bothPolarity = Sugar.intersection(positivePredicates, negativePredicates);
        Set<Predicate> negativePredicatesOnly = Sugar.setDifference(negativePredicates, positivePredicates);

        for (Map<Predicate, Predicate> mapping : mappings) {
            Clause changed = getConsistent(clause, mapping, Sugar.set(), Sugar.set());
            // this set is the only subset of signs that need to be swapped to get a lexicographically minimal version
            List<Predicate> bothPolarityImage = bothPolarity.stream().map(mapping::get).collect(Collectors.toList());
            for (List<Predicate> negations : Combinatorics.allSubsets(bothPolarityImage)) {
                negativePredicatesOnly.forEach(predicate -> negations.add(mapping.get(predicate))); // these have to be swapped for sure
                Clause flippedNegations = flipNegations(changed, negations);
                for (List<Predicate> flips : Combinatorics.allSubsets(binaryPredicates)) {
                    Clause direction = flipDirection(flippedNegations, flips);
                    int compare = (null == minimal ? -1 : (direction.getCannonic().compareTo(minimal)));
                    if (compare < 0) {
                        minimal = direction.getCannonic();
                        all.clear();
                    }
                    if (compare <= 0) {
                        all.add(new Configuration(restUnary, restBinary, join(mapping, predicateMapping),
                                Sugar.union(negationSwap, negations),
                                Sugar.union(directionFlip, flips),
                                direction));
                    }
                }
            }
        }
        return all;
    }

    private Map<Predicate, Predicate> join(Map<Predicate, Predicate> mapping, Map<Predicate, Predicate> predicateMapping) {
        HashMap<Predicate, Predicate> map = new HashMap<>();
        map.putAll(mapping);
        map.putAll(predicateMapping);
        return map;
    }

    private List<Map<Predicate, Predicate>> generateMappings(List<Predicate> sourceUnary, List<Predicate> imageUnary, List<Predicate> sourceBinary, List<Predicate> imageBinary) {
        if (sourceUnary.size() != imageUnary.size() || sourceBinary.size() != imageBinary.size()) {
            throw new IllegalStateException();
        }
        List<Map<Predicate, Predicate>> unaries = allPossibleMappings(sourceUnary, imageUnary);
        List<Map<Predicate, Predicate>> binaries = allPossibleMappings(sourceBinary, imageBinary);
        if (unaries.isEmpty() && binaries.isEmpty()) {
            throw new IllegalStateException();
        }
        if (unaries.isEmpty()) {
            unaries.add(new HashMap<>());
        }
        if (binaries.isEmpty()) {
            binaries.add(new HashMap<>());
        }
        List<Map<Predicate, Predicate>> retVal = Sugar.list();
        for (Map<Predicate, Predicate> f1 : unaries) {
            for (Map<Predicate, Predicate> f2 : binaries) {
                retVal.add(join(f1, f2));
            }
        }
        return retVal;
    }

    private List<Map<Predicate, Predicate>> allPossibleMappings(List<Predicate> original, List<Predicate> permuteable) {
        List<Map<Predicate, Predicate>> retVal = Sugar.list();
        for (List<Predicate> permutation : Combinatorics.permutations(permuteable)) {
            Map<Predicate, Predicate> current = new HashMap<>();
            for (int idx = 0; idx < original.size(); idx++) {
                current.put(original.get(idx), permutation.get(idx));
            }
            retVal.add(current);
        }
        return retVal;
    }

    private String toCannon(List<Clause> clauses) {
        return clauses.stream().map(Clause::getCannonic).sorted().collect(Collectors.joining(CLAUSES_DELIMITER));
    }

    private Clause getConsistent(Clause clause, Map<Predicate, Predicate> predicateMapping, Set<Predicate> negationSwap, Set<Predicate> directionFlip) {
        return new Clause(clause.getQuantifier(), clause.literals().stream()
                .map(literal -> {
                    if (predicateMapping.containsKey(literal.pred())) {
                        Predicate newPredicate = predicateMapping.get(literal.pred());
                        //Literal changedLiteral = LiteralsCache.getInstance().get(new Literal(newPredicate.getName(), literal.isNegated(), literal.arguments()));
                        Literal changedLiteral = LiteralsCache.getInstance().constructAndGet(newPredicate.getName(), literal.isNegated(), literal.arguments());
                        if (negationSwap.contains(newPredicate)) {
                            changedLiteral = changedLiteral.getNegatedPair();
                        }
                        if (directionFlip.contains(newPredicate)) {
                            changedLiteral = changedLiteral.getFlipped();
                        }
                        return changedLiteral;
                    }
                    return literal; // nothing is changed
                }).toList());
    }

    private MultiList<Quantifier, Clause> groupByPrefixes(List<Clause> clauses) {
        MultiList<Quantifier, Clause> retVal = new MultiList<>();
        clauses.forEach(c -> retVal.put(null == c.getQuantifier()
                        ? Quantifier.create(TwoQuantifiers.EMPTY, Sugar.list(Variable.construct("x"), Variable.construct("y")))
                        : c.getQuantifier(),
                c));
        return retVal;
    }

    private List<Clause> toCannonPrefixes(List<Clause> clauses) {
        return clauses.stream().map(clause -> {
            if (clause.isDecomposable()) {
//            if (clause.getQuantifier().isSwappable()) {
                Quantifier quantifier = clause.getQuantifier();
                if (quantifier.getPrefix().compareTo(quantifier.getMirror().getPrefix()) > 0) {
                    return new Clause(quantifier.getMirror(), clause.literals().stream().map(literal -> literal.getMirror(quantifier.flipSubstitution())).toList());
                }
            }
            return clause;
        }).collect(Collectors.toList());
    }

    private List<Predicate> fetchMinimalPredicates(Set<Pair<String, Integer>> pred, int arity) {
        return setup.predicates.stream().filter(predicate -> predicate.getArity() == arity).sorted(Comparator.comparing(Predicate::toString)).limit(pred.size()).collect(Collectors.toList());
    }

    private Clause flipNegations(Clause clause, Collection<Predicate> flip) {
        boolean flipUsed = false;
        List<Literal> change = Sugar.list();
        for (Literal literal : clause.literals()) {
            if (flip.contains(literal.pred())) {
                flipUsed = true;
//                    change.add(BinaryFlipCache.getInstance().getFlip(literal)); // TODO this could be cached, just at the start !!!!
                change.add(literal.negation());
            } else {
                change.add(literal);
            }
        }
        return flipUsed ? new Clause(clause.getQuantifier(), change) : clause;
    }

    public int countLiterals() {
        return clauses.stream().mapToInt(Clause::countLiterals).sum();
    }

    public void freeMemory() {
        this.ultraCannonic = null;
        this.cannonic = null;
        if (null != icw && null != icw.getOriginalClause() && null != icw.getOriginalClause().getSentence()) {
            icw.getOriginalClause().setSentence(null); // this is far beyond how an object should behave :'(
        }
        this.icw = null;
        this.cellGraph = null;
        this.canonicalCellGraph = null;
    }

    public void setCanonicalCellGraph(String cellGraph) {
        this.canonicalCellGraph = cellGraph;
    }

    public String getCanonicalCellGraph() {
        return canonicalCellGraph;
    }
}
