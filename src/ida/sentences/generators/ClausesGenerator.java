package ida.sentences.generators;

import ida.ilp.logic.*;
import ida.ilp.logic.quantifiers.Quantifier;
import ida.ilp.logic.quantifiers.TwoQuantifiers;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.caches.ClausesCache;
import ida.sentences.filters.SingleFilter;
import ida.sentences.filters.JoiningFilter;
import ida.utils.Combinatorics;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

public class ClausesGenerator {
    private final List<Literal> literals;
    private final List<Quantifier> quantifiers;
    private final MultiList<Quantifier, Quantifier> successors;
    private final Map<Quantifier, Quantifier> mirrors;
    private final Matching isomorphisMatching = new Matching();
    public final boolean useLogger;
    private final List<Triple<String, SentenceState, SentenceState>> logger;
    private final Map<Predicate, Predicate> followers;
    private final Map<Predicate, Predicate> ifollowers;
    private final Set<Predicate> roots;
    private ConcurrentHashMap.KeySetView<Long, Boolean> forbiddens;
    private int bitsPerClause;

    public ClausesGenerator(List<Literal> literals, List<Quantifier> quantifiers, MultiList<Quantifier, Quantifier> successors, Map<Quantifier, Quantifier> mirrors, Map<Predicate, Predicate> followers, boolean useLogger) {
        this.literals = literals;
        this.quantifiers = quantifiers;
        this.successors = successors;
        this.mirrors = mirrors;
        this.useLogger = useLogger;
        this.logger = Collections.synchronizedList(new ArrayList<>());
        this.followers = followers;
        this.ifollowers = new HashMap<>();
        if (null != followers) {
            for (Map.Entry<Predicate, Predicate> predicatePredicateEntry : followers.entrySet()) {
                ifollowers.put(predicatePredicateEntry.getValue(), predicatePredicateEntry.getKey());
            }
        }
        Set<Predicate> allPredicates = null == literals ? Sugar.set() : literals.stream().map(Literal::pred).collect(Collectors.toSet());
        this.roots = null == followers ? Sugar.set() : Sugar.setDifference(allPredicates, Sugar.setFromCollections(followers.values()));
    }

    public ClausesGenerator(List<Literal> literals, List<Quantifier> quantifiers, MultiList<Quantifier, Quantifier> successors, Map<Quantifier, Quantifier> mirrors, Map<Predicate, Predicate> followers) {
        this(literals, quantifiers, successors, mirrors, followers, false);
    }

    public List<Clause> generateClauses(List<SingleFilter<Clause>> filters) {
        return generateClauses(filters, -1);
    }

    public List<Clause> generateClauses(List<SingleFilter<Clause>> filters, int maxIterations) {
        List<Clause> all = Sugar.list();
        List<Clause> layer = Sugar.list(new Clause());
        int iteration = 0;
        while (!layer.isEmpty()) {
            if (maxIterations > 0 && maxIterations <= iteration) {
                break;
            }
            System.out.println("# clauses layer size is " + layer.size() + " & overall " + all.size());
            List<Clause> nextLayer = Sugar.list();
            Set<String> cannonics = ConcurrentHashMap.newKeySet();
            for (Clause clause : layer) {
                refinements(clause, literals, quantifiers, successors, mirrors).parallelStream()
                        .filter(refinement -> isApproved(refinement, filters))
                        .forEach(refinement -> {
                            synchronized (cannonics) {
                                if (cannonics.add(refinement.getCannonic())) {
                                    nextLayer.add(refinement);
                                    all.add(refinement);
                                }
                            }
                        });
            }
            layer = nextLayer;
            iteration++;
        }
        return all;
    }

    public List<Clause> refinements(Clause clause, List<Literal> literals, List<Quantifier> quantifiers, MultiList<Quantifier, Quantifier> successors, Map<Quantifier, Quantifier> mirrors) {
        List<Clause> retVal = Sugar.list();
        for (Literal literal : literals) {
            if (clause.literals().contains(literal)) {
                continue;
            }
            Quantifier mirrored = null;
            Set<Quantifier> quantifiersToGo = Sugar.set();
            if (null == clause.getQuantifier() || TwoQuantifiers.EMPTY == clause.getQuantifier().getQuantifiers()) { // this can happen only for the empty clause
                if (0 != clause.countLiterals()) {
                    throw new IllegalStateException();
                }
                quantifiersToGo = Sugar.setFromCollections(quantifiers);
            } else {
                Quantifier originalQuantifier = clause.getQuantifier();
                quantifiersToGo.add(originalQuantifier);
                if (successors.containsKey(originalQuantifier)) {
                    quantifiersToGo.addAll(successors.get(originalQuantifier));
                    if (mirrors.containsKey(originalQuantifier)) {
                        throw new IllegalStateException(); // just a sanity check
                    }
                }

                if (clause.isDecomposable() && 2 == originalQuantifier.numberOfUsedVariables
                        && 1 < literal.getVariableSet().size() && mirrors.containsKey(originalQuantifier)) {
                    // 1 < literal.getVariableSet().size() says that the new clause would not be decomposable anymore
                    mirrored = mirrors.get(originalQuantifier);
                    quantifiersToGo.add(mirrored);
                }
                // the idea of this is as follows: we have a decomposable two-quantifier clause (single-quantifier is a trivial case)
                // as far as the extension leads to decomposable clause (variable-wise), then just use the original quantifier
                // however, if the extension would lead to a non-decomposable clause, then we have to add the swapped (mirrored) quantifier as well (and change variable naming of these)
            }

            Set<Variable> commonVariables = Sugar.union(clause.variables(), literal.getVariableSet());
            for (Quantifier quantifier : quantifiersToGo) {
                if (!commonVariables.equals(quantifier.getUsedVariables())) {
                    continue;
                }
                List<Literal> currentLiterals = Sugar.listFromCollections(clause.literals());
                currentLiterals.add(literal);
                if (mirrored == quantifier) {
                    currentLiterals = currentLiterals.stream().map(Literal::getMirror).toList();
                }
                retVal.add(new Clause(quantifier, currentLiterals));
            }
        }
        return retVal;
    }

    private boolean isApproved(Clause refinement, List<SingleFilter<Clause>> predicates) {
        // this can be done in parallel
        for (SingleFilter<Clause> filter : predicates) {
            if (!filter.test(refinement)) {
                return false;
            }
        }
        return true;
    }

    public SingleFilter<Clause> maxLiterals(int l) {
        return new SingleFilter<>("MaxLiterals:" + l, (clause) -> {
            boolean val = clause.countLiterals() <= l;
            if (useLogger && !val) {
                log(null, clause, "MaxLiterals");
            }
            return val;
        });
    }

    public SingleFilter<Clause> maxLiteralsPerCountingClause(int l) {
        return new SingleFilter<>("MaxLiteralsPerCountingClause:" + l, (clause) -> {
            boolean val = !clause.hasCountingQuantifier() || clause.countLiterals() <= l;
            if (useLogger && !val) {
                log(null, clause, "MaxLiteralsPerCountingClause");
            }
            return val;
        });
    }

    // counting-related contradiction will be handled by another class :))
    public SingleFilter<SentenceState> contradictionFilter(Path pathToProver9, int secondsLimit) {
        if (null == pathToProver9 || !pathToProver9.toFile().exists()) {
            return new SingleFilter<>("CFwithNonexistingPath", (clause) -> true);
        }

        String maxSeconds = "" + secondsLimit;
        return new SingleFilter<>("ContradictionFilter" + secondsLimit,
                sentence -> {
                    StringBuilder sos = new StringBuilder();
                    sentence.clauses.stream().filter(clause -> !clause.hasCountingQuantifier())
                            .forEach(clause -> sos.append(clause.getProver9Format()).append("\n"));
                    if (sos.isEmpty()) {
                        return true;
                    }
                    boolean val = !isProveable(sos.toString(), pathToProver9, maxSeconds);

                    if (useLogger && !val) {
                        log(sentence, null, "ContradictionFilter");
                    }
                    return val;
                });
    }

    public SingleFilter<Clause> naiveTautologyFilter() {
        return new SingleFilter<>("NaiveTautologyFilter", (clause) -> {
            boolean val = clause.hasCountingQuantifier() || clause.literals().stream().noneMatch(l -> clause.containsLiteral(l.getNegatedPair()));
            if (useLogger && !val) {
                log(null, clause, "NaiveTautologyFilter");
            }
            return val;
        });
    }


    public SingleFilter<Clause> tautologyFilter(Path pathToProver9, int secondsLimit) {
        if (null == pathToProver9 || !pathToProver9.toFile().exists()) {
            return new SingleFilter<>("TFwithNonexistingPath", (clause) -> true);
        }

        String maxSeconds = "" + secondsLimit;
        return new SingleFilter<>("TautologyFilter" + secondsLimit,
                (clause) -> {
                    boolean val = true;
                    if (clause.hasCountingQuantifier()) {
                        val = true;
                    } else {
                        StringBuilder sos = new StringBuilder();
                        sos.append("-(");
                        sos.append(clause.getProver9Format());
                        sos.deleteCharAt(sos.length() - 1);
                        sos.append(").");
                        val = !isProveable(sos.toString(), pathToProver9, maxSeconds);
                    }
                    if (useLogger && !val) {
                        log(null, clause, "TautologyFilter");
                    }
                    return val;
                });
    }

    private boolean isProveable(String setOfSentences, Path pathToProver9, String maxSecond) {
        try {
            File file = File.createTempFile("problem", ".in");
            String sb = "set(quiet).\n" +
                    "assign(max_seconds, " + maxSecond + ").\n" +
                    "assign(max_proofs, 0).\n" +
                    "formulas(sos).\n" +
                    setOfSentences +
                    "end_of_list.\n";
            Files.write(file.toPath(), Sugar.list(sb));

            ProcessBuilder processBuilder = new ProcessBuilder();
            processBuilder.command(pathToProver9.toString(), "-f", file.getAbsolutePath());
            Process process = processBuilder.start();

            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            boolean proved = false;
            String line;
            while ((line = reader.readLine()) != null) {
                proved |= line.contains("THEOREM PROVED");
            }

            int exitCode = process.waitFor();
            Files.deleteIfExists(file.toPath());
            return proved;
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public SingleFilter<SentenceState> reflexiveAtoms() {
        return new SingleFilter<>("ReflexiveAtoms", (sentence) -> {
            boolean val = true;
            if (sentence.countLiterals() < 2) {
                val = true;
            } else {
                Set<Pair<String, Integer>> binaryPredicates = Sugar.set();
                Set<Pair<String, Integer>> nonReflexiveOccurrences = Sugar.set();
                for (Clause clause : sentence.clauses) {
                    for (Literal literal : clause.literals()) {
                        if (2 == literal.arity()) {
                            binaryPredicates.add(literal.getPredicate());
                            if (!literal.get(0).equals(literal.get(1))) {
                                nonReflexiveOccurrences.add(literal.getPredicate());
                            }
                        }
                    }
                }
                val = nonReflexiveOccurrences.containsAll(binaryPredicates);
            }
            if (useLogger && !val) {
                log(sentence, null, "ReflexiveAtoms");
            }
            return val;
        });
    }


    public SingleFilter<Clause> thetaSubsumptionFilter() {
        // TODO this could be cached if it's too slow
        // TODO this is not thread-safe
        return new SingleFilter<>("ThetaSubsumptionFilter",
                (clause) -> {
                    boolean val = true;
                    if (clause.hasCountingQuantifier() || 1 == clause.getQuantifier().numberOfUsedVariables) {
                        val = true;
                    } else {
                        boolean reduceable;
                        switch (clause.getQuantifier().getQuantifiers()) {
                            case FORALL_FORALL:
                                reduceable = isReducibleDisjunction(clause, false);
                                break;
                            case FORALL_EXISTS:
                                if (clause.isDecomposable()) {
                                    reduceable = isReducibleConjunction(clause, true) || isReducibleDisjunction(clause, true);
                                } else {
                                    reduceable = isReducibleConjunction(clause, true);
                                }
                                break;
                            case EXISTS_FORALL:
                                if (clause.isDecomposable()) {
                                    reduceable = isReducibleConjunction(clause, true) || isReducibleDisjunction(clause, true);
                                } else {
                                    reduceable = isReducibleDisjunction(clause, true);
                                }
                                break;
                            case EXISTS_EXISTS:
                                reduceable = isReducibleConjunction(clause, false);
                                break;
                            default:
                                throw new IllegalStateException();
                        }
//                        return !reduceable;
                        val = !reduceable;
                    }
                    if (useLogger && !val) {
                        log(null, clause, "ThetaSubsumptionFilter");
                    }
                    return val;
                });
    }

    private boolean isReducibleDisjunction(Clause clause, boolean xToXOnly) {
        for (Literal literal : clause.literals()) {
            Clause shorther = makeShorterClause(clause, literal);
            if (xToXOnly) {
                Variable x = clause.getQuantifier().getVariable(0);
                Pair<Term[], List<Term[]>> pair = isomorphisMatching.allSubstitutions(clause.negationToSpecialPrefix(), shorther.negationToSpecialPrefix()); // TODO this is not thread-safe
                int sourceIdx = 0;
                for (; sourceIdx < pair.getR().length; sourceIdx++) {
                    if (pair.getR()[sourceIdx].equals(x)) {
                        break;
                    }
                }
                for (Term[] terms : pair.getS()) {
                    if (terms[sourceIdx].equals(x)) {
                        return true;
                    }
                }
            } else if (isomorphisMatching.subsumption(clause.negationToSpecialPrefix(), shorther.negationToSpecialPrefix())) {
                return true;
            }
        }
        return false;
    }

    private boolean isReducibleConjunction(Clause clause, boolean xToXOnly) {
        List<Literal> literals = clause.literals().stream().toList(); // to make fast approach
        Map<Term, Term> sub = new HashMap<>();
        sub.put(clause.getQuantifier().getVariable(1), clause.getQuantifier().getVariable(0));
        for (int outerIdx = 0; outerIdx < literals.size(); outerIdx++) {
            Literal alpha = literals.get(outerIdx);
            for (int innerIdx = outerIdx + 1; innerIdx < literals.size(); innerIdx++) {
                Literal beta = literals.get(innerIdx);
                if (alpha.pred().equals(beta.pred()) && alpha.isNegated() == beta.isNegated()) {
                    if (xToXOnly) {
                        if (alpha.equals(beta)
                                || LogicUtils.substitute(alpha, sub).equals(beta)
                                || LogicUtils.substitute(beta, sub).equals(alpha)) {
                            return true;
                        }
                    } else {
                        if (isomorphisMatching.subsumption(new Clause(alpha), new Clause(beta)) // .negationToSpecialPrefix() is inside
                                || isomorphisMatching.subsumption(new Clause(beta), new Clause(alpha))) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    private Clause makeShorterClause(Clause clause, Literal literal) {
        List<Literal> lits = Sugar.list();
        for (Literal innerLiteral : clause.literals()) {
            if (literal != innerLiteral) {
                lits.add(innerLiteral);
            }
        }
        return new Clause(lits);
    }

    public JoiningFilter connectedComponents() {
        return new JoiningFilter("ConnectedComponents", (alpha, beta) -> {
            boolean val = alpha.clauses.isEmpty() || !Sugar.intersection(alpha.getPredicates(), beta.getPredicates()).isEmpty();
            if (useLogger && !val) {
                log(alpha, beta, "ConnectedComponents");
            }
            return val;
        });
    }
    public JoiningFilter maxOverallLiterals(int l) { // TODO write tests!
        return new JoiningFilter("MaxOverallLiterals:" + l, (alpha,beta) -> {
            boolean val = alpha.countLiterals() + beta.literals().size() <= l;
            if (useLogger && !val) {
                log(alpha, beta, "MaxOverallLiterals");
            }
            return val;
        });
    }


    // this is not the nicest implementation every
    // in order not to add two same clauses into a sentence ;)
    public JoiningFilter disjunctiveClauses() {
        return new JoiningFilter("DisjunctiveClauses", (alpha, beta) -> {
            boolean val = true;
            for (Clause clause : alpha.clauses) {
                if ((clause.getId() == beta.getId() && clause.getId() >= 0) ||
                        clause.equals(beta) ||
                        (clause.getQuantifier().equals(beta.getQuantifier())
                                && clause.getQuantifier().isSwappable()
                                && clause.equals(beta.swap()))) {
                    val = false;
                    break;
                }
            }
            if (useLogger && !val) {
                log(alpha, beta, "DisjunctiveClauses");
            }
            return val;
        });
    }

    // this is not optimized
    public JoiningFilter languageBias() {
        return new JoiningFilter("LanguageBias", (alpha, beta) -> {
            boolean val = true;
            Set<Pair<String, Integer>> inside = alpha.getPredicates();
            Set<Predicate> possible = whichFollows(inside);
            for (Literal literal : beta.literals()) {
                if (!inside.contains(literal.getPredicate()) && !possible.contains(literal.pred())) {
                    // connections like (U1 & U2 & U3) vs (U1 & U3 & U4)
                    val = canFollow(literal.pred(), beta.getPredicates(), inside);
                }
            }
            if (useLogger && !val) {
                log(alpha, beta, "LanguageBias");
            }
            return val;
        });
    }

    private boolean canFollow(Predicate pred, Set<Pair<String, Integer>> predicates, Set<Pair<String, Integer>> inside) {
        if (inside.contains(pred.getPair())) {
            return true;
        }
        Predicate previousMust = ifollowers.get(pred);
        if (null == previousMust) {
            return true;
        }
        if (inside.contains(previousMust.getPair())) {
            return true;
        }
        return predicates.contains(previousMust.getPair()) && canFollow(previousMust, predicates, inside);
    }

    private Set<Predicate> whichFollows(Set<Pair<String, Integer>> predicates) {
        Set<Predicate> retVal = Sugar.set();
        for (Pair<String, Integer> predicate : predicates) {
            Predicate follower = followers.get(Predicate.create(predicate));
            if (null != follower) {
                retVal.add(follower);
            }
        }
        retVal.addAll(roots);
        return retVal;
    }


    private boolean quantifiersConfiguration(Clause alpha, Clause beta, TwoQuantifiers one, TwoQuantifiers second) {
        return (alpha.getQuantifier().getQuantifiers() == one && beta.getQuantifier().getQuantifiers() == second)
                || (alpha.getQuantifier().getQuantifiers() == second && beta.getQuantifier().getQuantifiers() == one);
    }

    private boolean decideC2C2(Clause alpha, Clause beta) {
        if (!alpha.hasCountingQuantifier() || !beta.hasCountingQuantifier()) {
            return false; // not this case!
        }
        // E=k x phi(x) & E=l x phi(x) is a contradiction
        if (1 == alpha.getQuantifier().numberOfUsedVariables && 1 == beta.getQuantifier().numberOfUsedVariables) {
            return alpha.getQuantifier().firstVariableCardinality != beta.getQuantifier().secondVariableCardinality
                    && alpha.literals().equals(beta.literals());
        } else if (2 == alpha.getQuantifier().numberOfUsedVariables && 2 == beta.getQuantifier().numberOfUsedVariables) {
            // Vx E=k y phi(x,y) & Vx E=l y phi(x,y) , phi has 1 literal -> contradiction
            // E=k x Ey phi(x,y) & E=l x Vy phi(x,y) , phi has 1 literal -> contradiction
            if (1 == alpha.countLiterals() && alpha.literals().equals(beta.literals())) {
                return (alpha.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_EXISTS && beta.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_EXISTS && alpha.getQuantifier().secondVariableCardinality != beta.getQuantifier().secondVariableCardinality)
                        || (alpha.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL && beta.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL && alpha.getQuantifier().firstVariableCardinality != beta.getQuantifier().firstVariableCardinality);
            }
        }
        return false;
    }

    private boolean decideFo2C2(Clause alpha, Clause beta) {
        if (alpha.hasCountingQuantifier() || !beta.hasCountingQuantifier()) {
            return false; // not this case!
        }
        if (1 == alpha.getQuantifier().numberOfUsedVariables && 1 == beta.getQuantifier().numberOfUsedVariables) {
            boolean equalLiterals = alpha.literals().equals(beta.literals());
            // it is a question if we want to prune these
            // Vx phi(x) & E=k x phi(x) is a contradiction
            if (TwoQuantifiers.FORALL == alpha.getQuantifier().getQuantifiers() && equalLiterals) {
                return true;
            }

            // Vx phi(x) & E=k x ~phi(x) is a contradiction if phi has exactly one literal
            if (TwoQuantifiers.FORALL == alpha.getQuantifier().getQuantifiers()
                    && alpha.countLiterals() == 1
                    && beta.countLiterals() == 1
                    && beta.literals().contains(Sugar.chooseOne(alpha.literals()).getNegatedPair())) {
                return true;
            }

            // E=k phi(x) |~~ Ex phi(x) for n < k is the conjunction of zero anyway
            return TwoQuantifiers.EXISTS == alpha.getQuantifier().getQuantifiers() && equalLiterals;
        } else if (2 == alpha.getQuantifier().numberOfUsedVariables && 2 == beta.getQuantifier().numberOfUsedVariables) {
            boolean equalLiterals = alpha.literals().equals(beta.literals());
            boolean mirrorEquals = alpha.literals().stream().map(Literal::getMirror).collect(Collectors.toSet()).equals(beta.literals());

            // it is a question if we want to prune these
            // Vx Vy phi(x, y) & Vx E=k y phi(x, y) produces non-zero spectra only for n=k
            // Vx Vy phi(x, y) & E=k x Vy phi(x, y)
            // Vx Vy phi(x, y) & E=k x E=l y phi(x, y)
            if (hasQuantifier(alpha, TwoQuantifiers.FORALL_FORALL) &&
                    (hasQuantifier(beta, TwoQuantifiers.FORALL_EXISTS)
                            || hasQuantifier(beta, TwoQuantifiers.EXISTS_FORALL)
                            || hasQuantifier(beta, TwoQuantifiers.EXISTS_EXISTS))
                    && (equalLiterals || mirrorEquals)) {
                return true;
            }

            // Vx Vy phi(x, y) & Vx E=k y ~phi(x, y) is a contradiction; phi has exactly 1 literal
            // Vx Vy phi(x, y) & E=k x Vy ~phi(x, y) is a contradiction; phi has exactly 1 literal
            // Vx Vy phi(x, y) & E=k x E=l y ~phi(x, y) is a contradiction; phi has exactly 1 literal
            if (hasQuantifier(alpha, TwoQuantifiers.FORALL_FORALL) &&
                    (hasQuantifier(beta, TwoQuantifiers.FORALL_EXISTS)
                            || hasQuantifier(beta, TwoQuantifiers.EXISTS_FORALL)
                            || hasQuantifier(beta, TwoQuantifiers.EXISTS_EXISTS))
                    && 1 == alpha.countLiterals()
                    && 1 == beta.countLiterals()
                    && (beta.containsLiteral(Sugar.chooseOne(alpha.literals()).getNegatedPair())
                    || beta.containsLiteral(Sugar.chooseOne(alpha.literals()).getNegatedPair().getMirror()))) {
                return true;
            }

            // Vx E=k y phi(x, y) & Vx Ey phi(x, y) produces non-zero spectra only for n>=k
            // Vx E=k y phi(x) | rho(y) & Vx Ey phi(x) | rho(y) (special case subsumed by the one above)
            // E=k x Vy phi(x) | rho(y) & Vx Ey phi(x) | rho(y) produces non-zero spectra only for n>=k
            // E=k x Vy phi(x, y) & Vx Ey phi(x, y)
            if (hasQuantifier(alpha, TwoQuantifiers.FORALL_EXISTS)) {
                if ((equalLiterals && hasQuantifier(beta, TwoQuantifiers.FORALL_EXISTS))
                        || (mirrorEquals && hasQuantifier(beta, TwoQuantifiers.EXISTS_FORALL) && alpha.isDecomposable() && beta.isDecomposable())) {
                    return true;
                }
            }// TODO double-exists case resolve

            // TODO maybe some decomposable cases are forgotten here
            // Vx E=k y phi(x, y) & Ex Vy phi(x, y) produces non-zero spectra only for n=k
            if (hasQuantifier(alpha, TwoQuantifiers.EXISTS_FORALL) && hasQuantifier(beta, TwoQuantifiers.FORALL_EXISTS) && equalLiterals) {
                return true;
            }
            // TODO phi(x) could be here phi'(x) on the right side, couldn't it?
            // Vx E=k y phi(x) | rho(y) & Ex Vy phi(x) | rho(y)
//            if (hasQuantifier(alpha, TwoQuantifiers.EXISTS_FORALL) && hasQuantifier(beta, TwoQuantifiers.EXISTS_FORALL)
//                    && mirrorEquals && alpha.isDecomposable() && beta.isDecomposable()) {
//                return true;
//            }

            // E=k x Vy phi(x, y) & Ex Vy phi(x, y) produces non-zero spectra only for n>=k
            if (hasQuantifier(alpha, TwoQuantifiers.EXISTS_FORALL) && hasQuantifier(beta, TwoQuantifiers.EXISTS_FORALL) && equalLiterals) {
                return true;
            }

            // E=k x E=l y phi(x,y) & Ex Ey phi(x,y)
            if (hasQuantifier(alpha, TwoQuantifiers.EXISTS_EXISTS) && hasQuantifier(beta, TwoQuantifiers.EXISTS_EXISTS)
                    && (equalLiterals || mirrorEquals)) {
                return true;
            }
            // TODO write this on slack !
        } else if (hasQuantifier(alpha, TwoQuantifiers.FORALL) && 2 == beta.getQuantifier().numberOfUsedVariables) {
            boolean alphaSubsumesBeta = beta.literals().containsAll(alpha.literals());
            if ((hasQuantifier(beta, TwoQuantifiers.EXISTS_EXISTS) && alphaSubsumesBeta && beta.getQuantifier().firstVariableCardinality < 0)
                    || (hasQuantifier(beta, TwoQuantifiers.FORALL_EXISTS) && alphaSubsumesBeta)
            ) {
                return true;
            }
        }
        return false;
    }


    private boolean decideFo2Fo2(Clause alpha, Clause beta) {
        if (alpha.hasCountingQuantifier() || beta.hasCountingQuantifier()) {
            return false; // not this case!
        }
        boolean equalLiterals = alpha.literals().equals(beta.literals());
        boolean betaSubsumesAlpha = alpha.literals().containsAll(beta.literals());
        boolean alphaSubsumesBeta = beta.literals().containsAll(alpha.literals());

        // Vx phi(x) |= Ex phi'(x)
        if (quantifiersConfiguration(alpha, beta, TwoQuantifiers.FORALL, TwoQuantifiers.EXISTS)) {
            if ((hasQuantifier(alpha, TwoQuantifiers.FORALL) && alphaSubsumesBeta)
                    || hasQuantifier(beta, TwoQuantifiers.FORALL) && betaSubsumesAlpha) {
                return true;
            }
        }

        Set<Literal> mirrorLiteralsAlpha = alpha.literals().stream().map(Literal::getMirror).collect(Collectors.toSet());
        boolean mirrorEquals = mirrorLiteralsAlpha.equals(beta.literals());
        boolean betaSubsumesMirrorAlpha = mirrorLiteralsAlpha.containsAll(beta.literals());
        boolean alphaSubsumesMirrorBeta = beta.literals().containsAll(mirrorLiteralsAlpha);

        // TODO this is new, write that on slack
        // Vx phi(x) |= Vx Qy phi(x) | rho(x,y)
        // Vx phi(x) |= E/V x Ey phi(y) | rho(x,y)
        if (hasQuantifier(alpha, TwoQuantifiers.FORALL) || hasQuantifier(beta, TwoQuantifiers.FORALL)) {
            if ((hasQuantifier(alpha, TwoQuantifiers.FORALL) && (alphaSubsumesBeta || alphaSubsumesMirrorBeta)
                    || (hasQuantifier(beta, TwoQuantifiers.FORALL) && (betaSubsumesAlpha || betaSubsumesMirrorAlpha)))) {
                return true;
            }
        }


        // Vx Vy phi(x, y)  |= Vx Vy phi'(x, y)  -- that's at the start of isRedundant
        //                  |= Vx Ey
        //                  |= Ex Vy
        //                  |= Ex Ey
        if (hasQuantifier(alpha, TwoQuantifiers.FORALL_FORALL) || hasQuantifier(beta, TwoQuantifiers.FORALL_FORALL)) {
            if ((hasQuantifier(alpha, TwoQuantifiers.FORALL_FORALL) && (alphaSubsumesBeta || alphaSubsumesMirrorBeta))
                    || (hasQuantifier(beta, TwoQuantifiers.FORALL_FORALL) && (betaSubsumesAlpha || betaSubsumesMirrorAlpha))) {
                return true;
            }
        }

        // Vx Ey phi(x, y) |= Vx Ey phi'(x, y)  -- that's at the start of isRedundant
        // Vx Ey phi(x, y) |= Ex Ey phi'(x, y)
        // Vx Ey phi(x) | rho(y) |= Ex Ey phi'(x) | rho'(y)
        if (quantifiersConfiguration(alpha, beta, TwoQuantifiers.FORALL_EXISTS, TwoQuantifiers.EXISTS_EXISTS)) {
            if ((hasQuantifier(alpha, TwoQuantifiers.FORALL_EXISTS) && (alphaSubsumesBeta || alphaSubsumesMirrorBeta)) // ExEy is swappable so we don't have to make more complicate conditions
                    || hasQuantifier(beta, TwoQuantifiers.FORALL_EXISTS) && (betaSubsumesAlpha || betaSubsumesMirrorAlpha)) {
                return true;
            }
        }

        // Ex Vy phi(x, y) |= Ex Vy phi'(x, y) -- that's at the start of isRedundant
        // Ex Vy phi(x, y) |= Ex Ey phi'(x, y)
        // Ex Vy phi(x) | rho(y) |= Ex Ey phi'(x) | rho'(y)
        if (quantifiersConfiguration(alpha, beta, TwoQuantifiers.EXISTS_FORALL, TwoQuantifiers.EXISTS_EXISTS)) {
            if ((hasQuantifier(alpha, TwoQuantifiers.EXISTS_FORALL) && (alphaSubsumesBeta || alphaSubsumesMirrorBeta)) // ExEy is swappable so we don't have to make more complicate conditions
                    || hasQuantifier(beta, TwoQuantifiers.EXISTS_FORALL) && (betaSubsumesAlpha || betaSubsumesMirrorAlpha)) {
                return true;
            }
        }

        // Ey Vx phi(x, y) |= Vx Ey phi(x, y)    stack
        return mirrorEquals && quantifiersConfiguration(alpha, beta, TwoQuantifiers.EXISTS_FORALL, TwoQuantifiers.FORALL_EXISTS);
    }

    private boolean hasQuantifier(Clause alpha, TwoQuantifiers quantifier) {
        return alpha.getQuantifier().getQuantifiers() == quantifier;
    }

    private boolean isRedundant(Clause alpha, Clause beta) {
        if (!alpha.getPredicates().containsAll(beta.getPredicates()) && !beta.getPredicates().containsAll(alpha.getPredicates())) {
            return false; // alpha and beta have completely different predicate sets => no subsumption is possible, prune the rest of the method :)
            // actually it is redundant because of different pruning -- clause predicate-decomposibility
        }

        if (beta.hasSameQuantifier(alpha)) { // IJCAI'23 paper calls this Subsumption
            return subsumesWithIdentitySubsumption(alpha, beta)
                    || (beta.getQuantifier().isSwappable() && subsumesWithIdentitySubsumption(alpha, beta.getMirror()));
            // we don't have to test other alternatives, because we do not cover them in the rest of the methods (otherwise change this!)
        } else if (2 == alpha.getQuantifier().numberOfUsedVariables && 2 == beta.getQuantifier().numberOfUsedVariables
                && beta.getQuantifier().getMirror().equals(alpha.getQuantifier())
                && ((alpha.isDecomposable() || beta.isDecomposable()))) { //  || (alpha.getQuantifier().isSwappable() && beta.getQuantifier().isSwappable())
//             the same case just for swappable quantifiers, i.e. Qx Jy phi(x) | rho(y) vs Jx Qy  phi(y) | rho(x)
            if (subsumesWithIdentitySubsumption(alpha, beta.getMirror())) {
                return true;
            }
        }

        if (alpha.hasCountingQuantifier()) { // alpha \in C^2
            if (beta.hasCountingQuantifier()) { // beta \in C^2
                return decideC2C2(alpha, beta);
            } else { // beta \in FO^2
                return decideFo2C2(beta, alpha);
            }
        } else { // alpha \in FO^2
            if (beta.hasCountingQuantifier()) { // beta \in C^2
                return decideFo2C2(alpha, beta);
            } else { // beta \in FO^2
                return decideFo2Fo2(alpha, beta);
            }
        }
    }

    // TODO this is actually called SUBSUMPTION in the IJCAI'23 paper
    // TODO prove this
    private boolean subsumesWithIdentitySubsumption(Clause alpha, Clause beta) {
        // alpha.quantifier == beta.quantifier
        // \theta = {x -> x, y -> y}
        return alpha.literals().containsAll(beta.literals()) || beta.literals().containsAll(alpha.literals());
    }


    public JoiningFilter quantifiersReducibility() {
        return new JoiningFilter("QuantifiersReducibility", (alpha, beta) -> {
            boolean isReduceable = false;

            // TODO some of these tuple may be thereafter shift to cached n-tuples of forbidden
            for (Clause gamma : alpha.clauses) {
                if (isRedundant(beta, gamma)) {
                    isReduceable = true;
                    break;
                }
            }
            boolean val = !isReduceable;
            if (useLogger && !val) {
                log(alpha, beta, "QuantifiersReducibility");
            }
            return val;
        });
    }

    public JoiningFilter trivialConstraints() {
        return new JoiningFilter("TrivialConstraints", (alpha, beta) -> {
            boolean val = !beta.isCliffhanger() && alpha.clauses.stream().noneMatch(Clause::isCliffhanger);
            if (useLogger && !val) {
                log(alpha, beta, "TrivialConstraints");
            }
            return val;
        });
    }

    public JoiningFilter maxClauses(int maxClauses) {
        return new JoiningFilter("MaxClauses", (alpha, beta) -> {
            boolean val = alpha.clauses.size() + 1 <= maxClauses;
            if (useLogger && !val) {
                log(alpha, beta, "MaxClauses");
            }
            return val;
        });
    }

    public JoiningFilter creationLogging(String name) {
        return new JoiningFilter(name, (alpha, beta) -> {
            if (useLogger) {
                log(alpha, beta, name);
            }
            return true;
        });
    }


    public void log(SentenceState alpha, Clause beta, String reason) {
        log(alpha, beta, reason, null);
    }

    public void log(SentenceState alpha, Clause beta, String reason, SentenceState witness) {
        if (null == beta) {
            logger.add(new Triple<>(System.nanoTime() + " ; " + reason + " ; " + alpha.toFol() + " ; ", alpha, witness));
        } else if (null == alpha) {
            logger.add(new Triple<>(System.nanoTime() + " ; " + reason + " ;  ; " + beta.toFOL(), null, null));
        } else {
            logger.add(new Triple<>(System.nanoTime() + " ; " + reason + " ; " + alpha.toFol() + " ; " + beta.toFOL(), alpha.extend(beta), witness));
        }
    }


    public void flushLogger() {
        System.err.println("# logger starts\t" + logger.size());
        logger.stream().map(t -> "# " + t.getR() + " ; " +
                        (null == t.getS() ? "" : t.getS().getUltraCannonic()) + " ; " +
                        (null == t.getT() ? "" : t.getT().toFol() + " ; " + t.getT().getUltraCannonic()))
                .sorted()
                .forEach(System.err::println);
        System.err.println("# logger ends");
        logger.clear();
    }

    public long precomputeQuantifiersReducibility(List<Clause> clauses, int maxClauses, int maxLiteralsPerClause, int maxOverallLiterals, SentenceSetup setup) {
        forbiddens = ConcurrentHashMap.newKeySet(); // TODO let's work with longs for now and add support for bitsets when we need them :)

        this.bitsPerClause = (int) Math.ceil((Math.log(clauses.size()) / Math.log(2)));
        int maxBits = 64;
        if (3 * bitsPerClause > maxBits) {
            throw new UnsupportedOperationException("Ask the author for a better implementation since now we are working with only long encoding of forbidden n-tuples (change it to bitsets instead). IMHO you won't be able to compute anything with 2^21 of clauses.");
        }

        // all tuples // TODO make this parallel
        for (int innerIdx = 0; innerIdx < clauses.size(); innerIdx++) {
            Clause innerClause = clauses.get(innerIdx);
            for (int outerIdx = innerIdx + 1; outerIdx < clauses.size(); outerIdx++) {
                Clause outerClause = clauses.get(outerIdx);
                if (isRedundant(innerClause, outerClause)) {
                    forbiddens.add(encode(innerClause, outerClause));
                }
            }
        }


        // decomposability of formula to subformulae
        if (maxClauses > 2 && maxLiteralsPerClause > 1) { // otherwise there's nothing to prune by this technique
            ClausesCache cache = ClausesCache.getInstance();
            clauses.stream().filter(clause -> clause.countLiterals() > 1 && clause.getQuantifier().numberOfUsedVariables > 1)
                    .map(clause -> {
                        Pair<List<Literal>, List<Literal>> decomposition = split(clause);
                        if (decomposition.r.isEmpty() || decomposition.s.isEmpty()) {
                            return null;
                        }
                        return new Triple<>(clause, decomposition.getR(), decomposition.getS());
                    })
                    .filter(Objects::nonNull)
                    .forEach(triple -> {
                        Clause clause = triple.getR();
                        List<Literal> phiLiterals = triple.getS();
                        List<Literal> rhoLiterals = triple.getT();

                        Quantifier originalQuantifier = clause.getQuantifier();
                        List<Quantifier> phiQuatifiers = redundantQuantifiers(TwoQuantifiers.startsWithForall(originalQuantifier.getQuantifiers()) ? TwoQuantifiers.FORALL : TwoQuantifiers.EXISTS, originalQuantifier.firstVariableCardinality, originalQuantifier.getVariables(), setup.maxK);
                        List<Quantifier> rhoQuatifiers = redundantQuantifiers((TwoQuantifiers.FORALL_FORALL == originalQuantifier.getQuantifiers() || TwoQuantifiers.EXISTS_FORALL == originalQuantifier.getQuantifiers()) ? TwoQuantifiers.FORALL : TwoQuantifiers.EXISTS, originalQuantifier.secondVariableCardinality, originalQuantifier.getVariables(), setup.maxK);
                        for (List<Literal> phiPrime : Combinatorics.allSubsets(phiLiterals, 1)) {
                            for (List<Literal> rhoPrime : Combinatorics.allSubsets(rhoLiterals, 1)) {
                                for (Quantifier phiQuatifier : phiQuatifiers) {
                                    Clause phi = cache.get(new Clause(phiQuatifier, phiPrime));
                                    for (Quantifier rhoQuatifier : rhoQuatifiers) {
                                        Clause rho = cache.get(new Clause(rhoQuatifier, rhoPrime));
                                        forbiddens.add(encode(Sugar.list(clause.getId(), phi.getId(), rho.getId())));

//                                        SentenceState s = new SentenceState(Sugar.list(phi, rho, clause), setup);
//                                        System.out.println("new forbidden is\t" + s.getUltraCannonic() + "\t;\t" + s.toFol());
                                    }
                                }
                            }
                        }
                    });
        }
        return forbiddens.size();
    }

    private List<Quantifier> redundantQuantifiers(TwoQuantifiers original, int cardinality, List<Variable> variables, int maxK) {
        List<Quantifier> retVal = Sugar.list();
        Quantifier quantifier = Quantifier.create(original, variables, cardinality, -1);
        retVal.add(quantifier);
        if (TwoQuantifiers.EXISTS == original && cardinality < 0) {
            retVal.add(Quantifier.create(TwoQuantifiers.FORALL, variables, -1, -1));
            if (maxK >= 1) {
                retVal.add(Quantifier.create(TwoQuantifiers.EXISTS, variables, 1, -1));
            }
        }
        return retVal;
    }

    private Pair<List<Literal>, List<Literal>> split(Clause clause) {
        List<Literal> firstVariableLiterals = Sugar.list();
        List<Literal> secondVariableLiterals = Sugar.list();
        Variable firstVariable = clause.getQuantifier().getFirstVariable();
        for (Literal literal : clause.literals()) {
            if (literal.getVariableSet().size() > 1) {
                continue;
            }
            if (literal.getVariableSet().contains(firstVariable)) {
                firstVariableLiterals.add(literal);
            } else {
                secondVariableLiterals.add(literal.getMirror());
            }
        }
        return new Pair<>(firstVariableLiterals, secondVariableLiterals);
    }

    private Long connectEncoding(int smallerId, int biggerId) {
        long result = smallerId;
        result = result | ((long) biggerId << this.bitsPerClause);
        return result;
    }

    private Long encode(int alphaId, int betaId) {
        if (alphaId < betaId) {
            return connectEncoding(alphaId, betaId);
        }
        return connectEncoding(betaId, alphaId);
    }

    private Long encode(Clause alpha, Clause beta) {
        return encode(alpha.getId(), beta.getId());
    }

    private Long encode(List<Integer> indices) {
        Collections.sort(indices);
        long result = 0L;
        for (int idx = 0; idx < indices.size(); idx++) {
            result = result | ((long) indices.get(idx) << (idx * this.bitsPerClause));
        }
        return result;
    }

    private boolean isForbidden(int alphaId, int betaId) {
        return forbiddens.contains(encode(alphaId, betaId));
    }

    private boolean isForbidden(List<Integer> indices) {
        return forbiddens.contains(encode(indices));
    }

    public JoiningFilter twoFormulaeFilter() {
        return new JoiningFilter("QuantifiersReducibilityTwoFormulae", (alpha, beta) -> {
            boolean val = true;
            for (Clause clause : alpha.clauses) {
                if (isForbidden(clause.getId(), beta.getId())) {
                    val = false;
                    break;
                }
            }
            if (useLogger && !val) {
                log(alpha, beta, "QuantifiersReducibilityTwoFormulae");
            }
            return val;
        });
    }


    public JoiningFilter decomposableFilter() {
        return new JoiningFilter("QuantifiersReducibilityNTuple", (alpha, beta) -> {
            boolean val = true;
            if (beta.countLiterals() < 2) {
                val = true;
            } else {
                Pair<List<Clause>, List<Clause>> smallerAndBigger = shorterAndLonger(alpha, beta.countLiterals());
                if (beta.countLiterals() > 1) {
                    for (List<Integer> composition : twoWithAtMostLiteralsTogether(smallerAndBigger.getR(), beta.countLiterals())) {
                        composition.add(beta.getId());
                        if (isForbidden(composition)) {
                            val = false;
                            break;
                        }
                    }
                }

                if (val) {
                    for (Clause longer : smallerAndBigger.getS()) {
                        for (Clause clause : alpha.clauses) {
                            if (clause.countLiterals() <= longer.countLiterals() - beta.countLiterals()) {
                                List<Integer> composition = Sugar.list(clause.getId(), beta.getId(), longer.getId());
                                if (isForbidden(composition)) {
                                    val = false;
                                    break;
                                }
                            }
                        }
                        if (!val) {
                            break;
                        }
                    }
                }
            }
            if (useLogger && !val) {
                log(alpha, beta, "QuantifiersReducibilityNTuple");
            }
            return val;
        });
    }


    private List<List<Integer>> twoWithAtMostLiteralsTogether(List<Clause> clauses, int length) {
        List<List<Integer>> accumulator = Sugar.list();
        // we could sort the clauses but we're most likely playing with at most 5 clauses at all
        findDecompositions(clauses, length, accumulator, Sugar.list());
        return accumulator;
    }

    private void findDecompositions(List<Clause> clauses, int length, List<List<Integer>> accumulator, List<Integer> currentState) {
        if (length == 0) {
            return;
            //accumulator.add(Sugar.listFromCollections(currentState));
        } else if (length < 0 || clauses.isEmpty()) {
            return;
        } else {
            Clause first = clauses.get(0);
            List<Clause> rest = clauses.subList(1, clauses.size());
            if (first.countLiterals() <= length) {
                currentState.add(first.getId());
                if (currentState.size() > 1) {
                    accumulator.add(Sugar.listFromCollections(currentState));
                } else {
                    findDecompositions(rest, length - first.countLiterals(), accumulator, currentState);
                }
                currentState.remove(currentState.size() - 1); // remove last
            }
            findDecompositions(rest, length, accumulator, currentState);
        }
    }

    private Pair<List<Clause>, List<Clause>> shorterAndLonger(SentenceState alpha, int threshold) {
        List<Clause> shorter = Sugar.list();
        List<Clause> longer = Sugar.list();
        for (Clause clause : alpha.clauses) {
            if (clause.countLiterals() < threshold) {
                shorter.add(clause);
            } else if (clause.countLiterals() > threshold) {
                longer.add(clause);
            }
        }
        return new Pair<>(shorter, longer);
    }
}
