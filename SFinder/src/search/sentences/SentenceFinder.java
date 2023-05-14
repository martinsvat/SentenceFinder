package search.sentences;


import search.ilp.logic.*;
import search.ilp.logic.subsumption.Matching;

import search.ilp.logic.*;
import search.ilp.logic.special.IsoClauseWrapper;
import search.utils.Combinatorics;
import search.utils.Sugar;
import search.utils.collections.MultiList;
import search.utils.tuples.Pair;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.time.LocalDateTime;
import java.util.*;
import java.util.stream.Collectors;

public class SentenceFinder {

    public final Map<String, Literal> literalCache;
    private final HashMap<Quantifier, Integer> quantifierToOrder;
    private final HashMap<Literal, Integer> literalToOrder;
    private boolean debug;
    private final SentenceSetup setup;
    private List<Clause> uniqueSingleLiteralClauses;
    private List<Literal> singleLiterals;
    private Set<Literal> identityLiterals;
    private final Matching isomorphisMatching = new Matching();
    private final List<Quantifier> quantifiers;
    private String endingMessage = "the search has ended!";
    private String outOfTimeMessage = "the search has ended because of the time limit!";
    private Set<Clause> cliffHangers;
    private Map<TwoQuantifiers, Set<TwoQuantifiers>> mirrorQuantifiersForCountingContradictionPruning;
    private Map<Pair<String, Integer>, Pair<String, Integer>> ancestors;

    public SentenceFinder(SentenceSetup setup) {
        this.setup = setup;
        this.debug = setup.debug;

        if (2 != setup.variablesSet.size() || 2 != setup.variables.size()) {
            throw new UnsupportedOperationException("Only 2-variables are supported by this implementation.");
        }

        if (this.setup.quantifiers) {
            this.quantifiers = Sugar.list(
                    Quantifier.create(TwoQuantifiers.FORALL_FORALL, setup.variables),
                    Quantifier.create(TwoQuantifiers.FORALL_EXISTS, setup.variables),
                    Quantifier.create(TwoQuantifiers.EXISTS_FORALL, setup.variables),
                    Quantifier.create(TwoQuantifiers.EXISTS_EXISTS, setup.variables));

            if (setup.maxLiteralsPerCountingClause > 0 && setup.maxCountingClauses > 0) { // don't generate these if they are not gonna be used
                List<Pair<TwoQuantifiers, Integer>> counting = Sugar.list(
                        new Pair<>(TwoQuantifiers.FORALL_EXISTS, 1),
                        new Pair<>(TwoQuantifiers.EXISTS_FORALL, 0)// the case when we allow only E^{=k} x with no other y will be covered by Exists-k-forall
                );

                if (setup.doubleCountingExist) {
                    counting.add(new Pair<>(TwoQuantifiers.EXISTS_EXISTS, 0));
                    counting.add(new Pair<>(TwoQuantifiers.EXISTS_EXISTS, 1));
                }
                for (Pair<TwoQuantifiers, Integer> pair : counting) {
                    for (int k = 1; k <= setup.maxK; k++) {
                        Quantifier countingQuantifier = 0 == pair.getS() ? Quantifier.create(pair.getR(), setup.variables, k, -1) : Quantifier.create(pair.getR(), setup.variables, -1, k);
                        this.quantifiers.add(countingQuantifier);
                    }
                }
                if (setup.doubleCountingExist) {
                    for (int k = 1; k <= setup.maxK; k++) {
                        for (int j = 1; j <= setup.maxK; j++) {
                            this.quantifiers.add(Quantifier.create(TwoQuantifiers.EXISTS_EXISTS, setup.variables, k, j));
                        }
                    }
                }
            }
        } else {
            this.quantifiers = Sugar.list(Quantifier.create(TwoQuantifiers.FORALL_FORALL, setup.variables));
        }

        this.mirrorQuantifiersForCountingContradictionPruning = new HashMap<>();
        mirrorQuantifiersForCountingContradictionPruning.put(TwoQuantifiers.EXISTS_FORALL, Sugar.set(TwoQuantifiers.FORALL_EXISTS, TwoQuantifiers.FORALL_FORALL));
        mirrorQuantifiersForCountingContradictionPruning.put(TwoQuantifiers.FORALL_EXISTS, Sugar.set(TwoQuantifiers.EXISTS_FORALL, TwoQuantifiers.FORALL_FORALL));

        // the other are easy, but this one is a cumberstone, it is not so easy strip counting quantifiers and let match the other,
        // e.g. for (E=1 x E=1 y phi(x,y)) && (E=1 x E=1 y ~phi(x,y))   we can't conclude as easily as for
        // (E=1 x E=1 y phi(x,y)) && (V x V y ~phi(x,y))
        //mirrorQuantifiersForCountingContradictionPruning.put(TwoQuantifiers.EXISTS_EXISTS, Sugar.set(TwoQuantifiers.EXISTS_FORALL, TwoQuantifiers.FORALL_EXISTS, TwoQuantifiers.FORALL_FORALL - this case is intentionally left blank since we would need more information

        // generate all literals at the start
        this.singleLiterals = generateSingleLiterals();
        this.literalCache = literalsToCache(this.singleLiterals);
        this.identityLiterals = sameArgumentsLiterals(singleLiterals);
        this.cliffHangers = generateCliffHangers(singleLiterals);
        this.uniqueSingleLiteralClauses = generateUniqueSingleLiteralClauses();

        // sorting things
        this.quantifierToOrder = new HashMap<>();
        for (int idx = 0; idx < this.quantifiers.size(); idx++) {
            this.quantifierToOrder.put(quantifiers.get(idx), idx);
        }
        this.literalToOrder = new HashMap<>();
        for (int idx = 0; idx < this.singleLiterals.size(); idx++) {
            this.literalToOrder.put(singleLiterals.get(idx), idx);
        }

        this.ancestors = new HashMap<>();
        List<Predicate> nullary = setup.predicates.stream().filter(p -> p.getArity() == 0).sorted(Comparator.comparing(Predicate::toString)).collect(Collectors.toList());
        List<Predicate> unary = setup.predicates.stream().filter(p -> p.getArity() == 1).sorted(Comparator.comparing(Predicate::toString)).collect(Collectors.toList());
        List<Predicate> binary = setup.predicates.stream().filter(p -> p.getArity() == 2).sorted(Comparator.comparing(Predicate::toString)).collect(Collectors.toList());

        for (List<Predicate> preds : Sugar.list(nullary, unary, binary)) {
            for (int idx = 0; idx < preds.size(); idx++) {
                this.ancestors.put(preds.get(idx).getPair(), 0 == idx ? null : preds.get(idx - 1).getPair());
            }
        }
    }

    private Map<String, Literal> literalsToCache(List<Literal> literals) {
        HashMap<String, Literal> result = new HashMap<>();
        for (Literal literal : literals) {
            result.put(literal.toString(), literal);
        }
        return result;
    }


    public void search() {
        SentenceState emptyState = SentenceState.create(setup);
        List<SentenceState> layer = Sugar.list(emptyState);
        search(0, layer, Sugar.list());
    }

    public void search(int layerIdx, List<SentenceState> layer, List<Clause> cellGraphs) {
        long overallStart = System.nanoTime();
        if (setup.cliffhangerFilter) {
            makeSentencesConsistent(layer);
        }
        MultiList<IsoClauseWrapper, Clause> cellIsomorphic = cacheToMultiList(cellGraphs);
        StringBuilder sizes = new StringBuilder();
        for (; layerIdx < setup.maxLayers; layerIdx++) {
            long start = System.nanoTime();
            long displayed = 0;
            String layerMessage = "starting layer " + layerIdx + " with " + layer.size() + " candidates\t" + sizes;
            printComment(layerMessage);

            if (layer.isEmpty()) {
                break;
            }

            if (setup.statesStoring) {
                System.err.println("# " + layerMessage);
                for (SentenceState sentence : layer) {
                    System.err.println(sentence.toFol(true, true, true));
                }
                System.err.println("# end of candidates");
                System.err.println("# writing down all cell-graphs\t" + cellGraphs.size());
                for (Clause cellGraph : cellGraphs) {
                    System.err.println(cellGraph);
                }
                System.err.println("# end cells");
            }

            if (debug) {
                printDebug("within layer " + layerIdx + " there are " + layer.size() + " candidates");
                layer.forEach(c -> printDebug("\t" + c.toFol() + c.debugOutput(debug)));
            }

            MultiList<IsoClauseWrapper, Clause> fullQuantifiersIsomorphic = new MultiList<>();
            MultiList<IsoClauseWrapper, Clause> partialQuantifiersIsomorphic = new MultiList<>();

            Set<String> lexicoFullyQuantified = Sugar.set();
            Set<String> lexicoPartiallyQuantified = Sugar.set();

            List<SentenceState> nextLayer = Sugar.list();
            List<Pair<SentenceState, CandidateProperties>> cellGraphQueue = Sugar.list();
            for (SentenceState candidate : layer) {
                if (shouldEnd(overallStart)) {
                    break;
                }
                if (debug) {
                    printDebug("generating refinements of " + candidate.toFol(true, true));
                }
                for (SentenceState refinement : refinements(candidate)) {
                    if (shouldEnd(overallStart)) {
                        break;
                    }
                    if (debug) {
                        printDebug("evaluating refinement " + refinement.toFol(true, true));
                    }

                    // cellGraphs is extended if the candidate does not have an isomorphic graph in there
                    CandidateProperties properties = checkCandidate(refinement, fullQuantifiersIsomorphic, partialQuantifiersIsomorphic, cellIsomorphic, lexicoFullyQuantified, lexicoPartiallyQuantified);
                    if (properties.addToNextLayer) {
                        cellGraphQueue.add(new Pair<>(refinement, properties));
                        if (setup.lexicographicalComparatorOnly) {
                            lexicoFullyQuantified.add(refinement.getFullyQuantifiedLexicographicallyMinimal());
                            lexicoPartiallyQuantified.add(refinement.getPartiallyQuantifiedLexicographicallyMinimal());
                        } else {
                            incorporateForIsomorphism(refinement, fullQuantifiersIsomorphic, partialQuantifiersIsomorphic);
                        }
                    }
                }
            }

            if (shouldEnd(overallStart)) {
                break;
            }
            if (debug) {
                printDebug("checking cell-graph isomorphism");
            }
            fillInCellGraph(cellGraphQueue);
            // shouldEnd should be here as well, but let's forget it for now
            for (Pair<SentenceState, CandidateProperties> pair : cellGraphQueue) {
                SentenceState refinement = pair.getR();
                if (debug) {
                    printDebug(" " + refinement.toFol() + " -> " + refinement.getCellGraph() + " <- " + refinement.toFol(true, true));
                }
                if ((!setup.computeCellGraph || wasCellGraphUniqueStateful(refinement, cellGraphs, cellIsomorphic))
                        && pair.getS().printOut) {
                    displayed++;
                    printCandidate(refinement);
                }
                nextLayer.add(refinement);
            }

            layer = nextLayer;
            long layerTimeInSec = (System.nanoTime() - start) / 1000000000;
            sizes.append(" ").append(displayed).append(" (").append(layerTimeInSec).append(")");
            String layerEnds = "ending " + layerIdx + " with " + layer.size() + " candidates\t" + sizes;
            printComment(layerEnds);
            if (setup.statesStoring) {
                System.err.println("# " + layerEnds);
            }
        }

        String message = shouldEnd(overallStart) ? outOfTimeMessage : endingMessage;
        printComment(message);
        if (setup.statesStoring) {
            System.err.println("# " + message);
        }
    }

    private boolean shouldEnd(long start) {
        return null != this.setup.timeLimit && this.setup.timeLimit <= (System.nanoTime() - start) / 60_000_000_000L; // 1min = 60*10^9 milliseconds
    }

    private void makeSentencesConsistent(List<SentenceState> layer) {
        for (SentenceState sentence : layer) {
            for (Clause clause : sentence.clauses) {
                if (this.cliffHangers.contains(clause)) {
                    clause.setCliffhanger(true);
                }
            }
        }
    }

    private MultiList<IsoClauseWrapper, Clause> cacheToMultiList(List<Clause> cellGraphs) {
        MultiList<IsoClauseWrapper, Clause> result = new MultiList<>();
        for (Clause cellGraph : cellGraphs) {
            IsoClauseWrapper icw = IsoClauseWrapper.create(cellGraph);
            boolean matches = false;
            for (Clause clause : result.get(icw)) {
                if (isomorphisMatching.isomorphism(clause, cellGraph)) {
                    matches = true;
                    break;
                }
            }
            if (!matches) {
                result.put(icw, cellGraph);
            }
        }
        return result;
    }

    public void fillInCellGraph(List<Pair<SentenceState, CandidateProperties>> cellGraphQueue) {
        if (null == setup.cellGraphPath || !setup.computeCellGraph || cellGraphQueue.isEmpty()) {
            return;
        }
        try {
            File file = File.createTempFile("sentences", ".in");
            StringBuilder sb = new StringBuilder();
            cellGraphQueue.forEach(pair -> sb.append(sb.isEmpty() ? "" : "\n").append(pair.getR().toFol(true, false)));
            Files.write(file.toPath(), Sugar.list(sb.toString()));

            ProcessBuilder processBuilder = new ProcessBuilder();
            if (setup.juliaSoVersion != null) {
                processBuilder.command("julia", "--sysimage", setup.juliaSoVersion, "--threads", "" + setup.juliaThreads, setup.cellGraphPath, file.getAbsolutePath());//, "" + setup.cellTimeLimit);
            } else {
                processBuilder.command("julia", "--threads", "" + setup.juliaThreads, "--project=" + Paths.get(setup.cellGraphPath).getParent().getParent(), setup.cellGraphPath, file.getAbsolutePath());//, "" + setup.cellTimeLimit);
            }

            Process process = processBuilder.start();

            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            int addedCellGraphs = 0;
            while ((line = reader.readLine()) != null) {
                if (line.startsWith("[")) {
                    String wholeLine = line;
                    // parsing a cell-graph
                    line = line.substring(1, line.length() - 1);
                    if (line.trim().isEmpty()) {
                        // now, there are only [] meaning the sentence was a contradiction, thus scratching it completely
                        printComment(" HX removing contradiction since it has no cell-graph\t" + cellGraphQueue.get(addedCellGraphs).getR().toFol(true, true));
                        cellGraphQueue.remove(addedCellGraphs);
                        continue;
                    }
                    VariableSupplier sumSupplier = VariableSupplier.create("m");
                    VariableSupplier productSupplier = VariableSupplier.create("p");
                    VariableSupplier weightVariableSupplier = VariableSupplier.create("x");
                    Map<String, Term> expressionCache = new HashMap<>();

                    List<Literal> literals = Sugar.list();
                    VariableSupplier variableSupplier = VariableSupplier.create("n");
                    int idx = 0;
                    for (String graph : line.split(";")) {
                        literals.addAll(parseSingleCellGraph(graph, idx, variableSupplier, sumSupplier, productSupplier, weightVariableSupplier, expressionCache, addedCellGraphs, cellGraphQueue, processBuilder, wholeLine));
                        idx++;
                    }
                    if (addedCellGraphs >= cellGraphQueue.size()) {
                        throw new IllegalStateException("Julia's FastWFOMC returned more cell-graphs than we asked for.");
                    }

                    cellGraphQueue.get(addedCellGraphs).getR().setCellGraph(new Clause(literals));
                    addedCellGraphs++;
                } else {
                    printComment("there is an unparseable line from FastWFOMC\t" + line + " ; after parsing " + addedCellGraphs + " cell-graphs");
                }
            }
            if (cellGraphQueue.size() != addedCellGraphs) {
                System.err.println("Not every single cell-graph was returned from the query!");
                System.err.println(processBuilder.command());
                System.err.println(file.getAbsolutePath());
                System.err.println(sb);

                BufferedReader errorReader = new BufferedReader(new InputStreamReader(process.getErrorStream()));
                System.err.println("error from WFOMC");
                while ((line = errorReader.readLine()) != null) {
                    System.err.println(line);
                }
                throw new IllegalStateException();
            }
            int exitCode = process.waitFor();
            Files.deleteIfExists(file.toPath());
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private Collection<? extends Literal> parseSingleCellGraph(String graph, int graphIdx, VariableSupplier variableSupplier, VariableSupplier sumSupplier, VariableSupplier productSupplier, VariableSupplier weightVariableSupplier, Map<String, Term> expressionCache, int addedCellGraphs, List<Pair<SentenceState, CandidateProperties>> cellGraphQueue, ProcessBuilder processBuilder, String wholeLine) {
        List<Literal> literals = Sugar.list();
        Variable graphVar = Variable.construct("g" + graphIdx);
        for (Literal literal : Clause.parse(graph, ',', null).literals()) {
            if (literal.predicate().startsWith("L")) { // L(x3, 4, 1)
                literals.add(new Literal(literal.predicate(),
                        variableSupplier.get(literal.get(0) + "-" + graphIdx),
                        parseSymbolicWeightStateful(literal.get(1), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        parseSymbolicWeightStateful(literal.get(2), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar));
            } else if (literal.predicate().startsWith("E")) { //  E(x1, x2, 2)
                literals.add(new Literal(literal.predicate(),
                        variableSupplier.get(literal.get(0) + "-" + graphIdx),
                        variableSupplier.get(literal.get(1) + "-" + graphIdx),
                        parseSymbolicWeightStateful(literal.get(2), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar));
            } else if (literal.predicate().startsWith("W")) { //  W(1)
                literals.add(new Literal(literal.predicate(),
                        parseSymbolicWeightStateful(literal.get(0), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar));
            } else {
                System.err.println("error while computing cell-graph at " + addedCellGraphs + " out of " + cellGraphQueue.size());
                System.err.println(cellGraphQueue.get(addedCellGraphs).getR().toFol(true, true));
                System.err.println(processBuilder.command());
                System.err.println(wholeLine);
                System.err.println(graph);
                System.err.println(literal);
                throw new IllegalStateException();
            }
        }
        literals.add(new Literal("G", graphVar));
        return literals;
    }

    private Term parseSymbolicWeightStateful(Term constant, VariableSupplier sumSupplier, VariableSupplier productSupplier, VariableSupplier weightVariableSupplier, List<Literal> parseTree, Map<String, Term> expressionCache) {
        String expression = constant.name();
        if (!expression.startsWith("'")) { // -1, 1,... scalar weight
            return constant;
        }

        if (expressionCache.containsKey(expression)) {
            return expressionCache.get(expression);
        }

        Term finalTerm = sumSupplier.getNext();
        expression = expression.substring(1, expression.length() - 1); // removing first and last '...'

        List<Pair<Term, Boolean>> sums = Sugar.list(); // sum is either a constant (e.g. 10) or a product (e.g. p1)
        while (!expression.isEmpty()) {
            boolean startsWithMinus = expression.startsWith("-");
            int nextPlus = expression.indexOf("+");
            int nextMinus = startsWithMinus ? expression.indexOf("-", 1) : expression.indexOf("-");
            int end = 0;
            if (-1 == nextPlus && -1 == nextMinus) {
                end = expression.length();
            } else if (-1 == nextPlus) {
                end = nextMinus;
            } else if (-1 == nextMinus) {
                end = nextPlus;
            } else {
                end = Math.min(nextPlus, nextMinus);
            }

            String part = expression.substring(startsWithMinus ? 1 : 0, end);
            expression = expression.substring(end);

            if (part.contains("x")) { // we're gonna do some product
                Variable productVariable = productSupplier.getNext();
                sums.add(new Pair<>(productVariable, startsWithMinus));

                for (String expr : part.split("\\*")) {
                    if (expr.contains("x")) {
                        List<Term> arguments = Sugar.list(productVariable);
                        String[] split = expr.split("\\^");
                        arguments.add(weightVariableSupplier.get(split[0]));
                        arguments.add(new Constant(2 == split.length ? split[1] : "1")); // ^1 might be redundant but better be safe than sorry
                        parseTree.add(new Literal("P", arguments));
                    } else { // scalar
                        parseTree.add(new Literal("P", productVariable, new Constant(expr)));
                    }
                }
            } else {// just a scalar
                sums.add(new Pair<>(new Constant(part), startsWithMinus));
            }

            if (expression.startsWith("+")) {
                expression = expression.substring(1);
            }
        }
        for (Pair<Term, Boolean> sum : sums) {
            parseTree.add(new Literal(sum.getS() ? "Md" : "M", finalTerm, sum.getR())); // M stands for addition, Md for distraction
        }

        expressionCache.put(constant.name(), finalTerm);
        return finalTerm;
    }

    // returns true iff refinement is not cell-graph isomorphic to anything in the collection
    private boolean wasCellGraphUniqueStateful(SentenceState refinement, List<Clause> cellGraphs, MultiList<IsoClauseWrapper, Clause> cellIsomorphic) {
        if (setup.computeCellGraph) {
            Clause cellGraph = refinement.getCellGraph();
            IsoClauseWrapper icw = IsoClauseWrapper.create(cellGraph);
            boolean innerHide = false;
            for (Clause otherCellGraph : cellIsomorphic.get(icw)) {
                innerHide = isomorphisMatching.isomorphism(cellGraph, otherCellGraph); // TODO this might be optimized, right?
                if (innerHide && debug) {
                    printDebug("H4 " + refinement + " since it's cell-isomorphic to " + otherCellGraph + " (this one produces " + cellGraph + " )");
                }
                if (innerHide) {
                    return false;
                }
            }
            cellIsomorphic.put(icw, cellGraph);
            cellGraphs.add(cellGraph);
        }
        return true;
    }

    private void incorporateForIsomorphism(SentenceState sentence, MultiList<IsoClauseWrapper, Clause> fullQuantifiersIsomorphic, MultiList<IsoClauseWrapper, Clause> partialQuantifiersIsomorphic) {
        Pair<List<Clause>, List<Clause>> pair = sentence.getPredicateIsomorphicRepresentation();
        for (Clause clause : pair.getS()) {
            add(clause, fullQuantifiersIsomorphic);
        }
        if (sentence.containsSecondUnusedVariable()) {
            for (Clause clause : pair.getR()) {
                add(clause, partialQuantifiersIsomorphic);
            }
        }
    }

    private void add(Clause clause, MultiList<IsoClauseWrapper, Clause> multilist) {
        IsoClauseWrapper icw = IsoClauseWrapper.create(clause);
        for (Clause another : multilist.get(clause)) {
            if (isomorphisMatching.isomorphism(clause, another)) {
                return;
            }
        }
        multilist.put(icw, clause);
    }

    private void printDebug(String message) {
        System.out.println("# " + LocalDateTime.now().getHour() + ":" + LocalDateTime.now().getMinute() + ":" + LocalDateTime.now().getSecond() + "\t" + message);
    }

    private List<SentenceState> refinements(SentenceState candidate) {
        // this method is intended to return...
        List<SentenceState> result = Sugar.list();

        if (debug) {
            printDebug(" adding new clauses");
        }
        // adding a new clause; we don't have to test these, they are brand new a unique
        if (candidate.getNumberOfClauses() < setup.maxClauses) {
            appendRefinedBySingleLiteralsClause(candidate, result);
        }

        if (debug) {
            printDebug(" extending an existing clause");
        }
        // extending an existing clause
        for (Clause clause : candidate.clauses) {
            if (clause.literals().size() < setup.maxLiteralsPerClause
                    && (!clause.hasCountingQuantifier() || clause.literals().size() < setup.maxLiteralsPerCountingClause)
                    && !clause.isFrozen()) {
                appendRefinementsByExtendingClauses(candidate, result, clause);
            }
        }

        if (debug) {
            printDebug(" there are " + result.size() + " refinements: " + result.stream().map(sentence -> sentence.toFol(true, true)).collect(Collectors.joining(" ; ")));
        }

        return result;
    }

    private void appendRefinementsByExtendingClauses(SentenceState candidate, List<SentenceState> result, Clause clause) {
        for (Literal singleLiteral : this.singleLiterals) {
            if (setup.languageBias) {
                Pair<String, Integer> ancestor = ancestors.get(singleLiteral.getPredicate());
                if (null != ancestor && !candidate.containsPredicate(ancestor)) { // because {} sentence contains every predicate
                    continue;
                }
            }
            if (clause.containsLiteral(singleLiteral)) {
                continue;
            }
            if (setup.identityFilter) {
                if (!candidate.containsPredicate(singleLiteral.getPredicate()) && identityLiterals.contains(singleLiteral)) {
                    if (debug) {
                        printDebug("  X2 skipping identity filter \t" + candidate + " with refinement " + singleLiteral);
                    }
                    continue; // there is no other literal with the same predicate in the sentence and this predicate is an identity one
                }
            }
            if (setup.naiveTautology && clause.containsLiteral(singleLiteral.negation())) {
                if (debug) {
                    printDebug("  X3 skipping tautology\t" + candidate.toFol(true, true) + " with clause " + clause + " should not contain " + singleLiteral);
                }
                continue;
            }
            if (!clause.hasCountingQuantifier() && setup.tautologyFilter && setup.prover9Path != null
                    && candidate.containsPredicate(singleLiteral.getPredicate()) && isTautology(clause, singleLiteral)) {
                if (debug) {
                    printDebug("   X4 skipping proved tautology \t" + candidate.toFol(true, true) + " with clause " + clause + " should not contain " + singleLiteral);
                }
                continue;
            }

            SentenceState refinement = candidate.refineByExtendingClause(clause, singleLiteral);
            if (canBeAdded(refinement, result)) { // i.e. add only those "unique" from this refinement
                result.add(refinement);
            }
        }
    }

    public boolean isTautology(Clause clause, Literal literal) {
        StringBuilder sos = new StringBuilder();
        Clause joined = new Clause(clause.getQuantifier(), Sugar.listFromCollections(clause.literals(), Sugar.list(literal)));
        sos.append("-(");
        sos.append(joined.getProver9Format());
        sos.deleteCharAt(sos.length() - 1);
        sos.append(").");
        if (debug) {
            printDebug("  invoking isTautology with " + clause.toFOL(true, true) + " with " + literal);
        }
        return isProveable(sos.toString());
    }

    // returns true iff newSentence \not\in sentences
    private boolean canBeAdded(SentenceState newSentence, List<SentenceState> sentences) {
        if (null == newSentence) {
            return false;
        }
        if (debug) {
            printDebug("  checking addition of " + newSentence);
        }
        for (SentenceState existingOne : sentences) {
//            IsomorphismType isomorphic = newSentence.isIsomorphicTo(existingOne);
            //IsomorphismType isomorphic = ;
            boolean prune = setup.lexicographicalComparatorOnly
                    ? existingOne.areLexicographicallySame(newSentence)
                    : IsomorphismType.YES == newSentence.isPredicateIsomorphic(existingOne);
            if (prune) {
                if (debug) {
                    printDebug("   X5 " + newSentence.toFol(true, true) + " since it is isomorphic to " + existingOne.toFol(true, true));
                }
                return false;
            }
        }
        return true;
    }

    private void appendRefinedBySingleLiteralsClause(SentenceState candidate, List<SentenceState> result) {
        long quantifiedClauses = candidate.clauses.stream().filter(Clause::hasCountingQuantifier).count();
        for (Clause clause : this.uniqueSingleLiteralClauses) {
            Pair<String, Integer> predicate = Sugar.chooseOne(clause.literals()).getPredicate();
            if (setup.languageBias) {
                Pair<String, Integer> ancestor = ancestors.get(predicate);
                if (null != ancestor && (candidate.clauses.isEmpty() || !candidate.containsPredicate(ancestor))) { // because empty sentence contains every single predicate
                    continue;
                }
            }

            if (setup.maxCountingClauses <= quantifiedClauses && clause.hasCountingQuantifier()) {
                if (debug) {
                    printDebug("  X-1 " + candidate.toFol(true, true) + " \\cup " + clause.toFOL(true, true) + " since " + clause.toFOL(true, true));
                }
                continue;
            }
            if (setup.identityFilter && candidate.clauses.isEmpty()) {
                if (identityLiterals.contains(Sugar.chooseOne(clause.literals()))) {
                    if (debug) {
                        printDebug("  X0 " + candidate.containsPredicate(Sugar.chooseOne(clause.literals()).getPredicate()) + "\t" + candidate.toFol(true, true) + " \\cup " + clause.toFOL(true, true) + " since " + clause.toFOL(true, true));
                    }
                    continue;
                }
            }

            if ((!setup.connectedComponents || candidate.containsPredicate(predicate))
                    && !candidate.containsIsomorphicClause(clause, false)) { // this is maybe too big hammer and plain contains would do as well
                result.add(candidate.extend(clause));
            } else {
                if (debug) {
                    printDebug("  X1 " + candidate.containsPredicate(Sugar.chooseOne(clause.literals()).getPredicate()) + "\t" + candidate.toFol(true, true) + " \\cup " + clause.toFOL(true, true) + " since " + clause.toFOL(true, true));
                }
            }

        }
    }


    private List<Clause> generateUniqueSingleLiteralClauses() {
        if (null == this.singleLiterals) {
            this.singleLiterals = generateSingleLiterals();
            this.identityLiterals = sameArgumentsLiterals(singleLiterals);
            this.cliffHangers = generateCliffHangers(singleLiterals);
        }
        List<Clause> singleLiteralClauses = Sugar.list();
        this.quantifiers.forEach(quantifier -> singleLiterals.stream()
                .filter(literal -> literal.containsTerm(quantifier.getFirstVariable()))
                .map(literal -> {
                    Clause clause = Clause.create(quantifier, literal);
                    if (setup.cliffhangerFilter && this.cliffHangers.contains(clause)) {
                        clause.setCliffhanger(true);
                    }
                    if (quantifier.isCountingQuantifier()) {
                        // we prune here Vx E=k y U(x) since it's effectively Vx U(x) which is generated by Vx Vy U(x) and Vx Ey U(x) anyway
                        // i.e. at least one variable in the literal must be counting
                        boolean atLeastOneCountingVariable = false;
                        for (Term term : literal.terms()) {
                            if (term instanceof Variable) {
                                Variable variable = (Variable) term;
                                if (quantifier.isVariableCounting(variable)) {
                                    atLeastOneCountingVariable = true;
                                    break;
                                }
                            }
                        }
                        if (!atLeastOneCountingVariable) {
                            return null;
                        }
                    }
                    return clause;
                })
                .filter(Objects::nonNull)
                .forEach(singleLiteralClauses::add));

        List<Clause> result = Sugar.list();
        for (Clause candidate : singleLiteralClauses) {
            boolean contained = false;
            for (Clause alreadyIn : result) {
                if (setup.lexicographicalComparatorOnly
                        ? alreadyIn.isLexicographicallySame(candidate, false)
                        : areIsomorphic(candidate, alreadyIn, false)) {
                    contained = true;
                    break;
                }
            }
            if (!contained) {
                result.add(candidate);
            }
        }
        return result;
    }

    private Set<Clause> generateCliffHangers(List<Literal> literals) {
        // Vx U(x) , Vx ~U(x), Vx Vy ~B(x,y) , Vx Vy B(y,x)
        Set<Clause> retVal = Sugar.set();
        for (Literal literal : literals) {
            Set<Variable> variables = LogicUtils.variables(literal);
            for (Quantifier quantifier : this.quantifiers) {
                if (quantifier.isCountingQuantifier()) {
                    continue;
                }
                // quantifier here is just counting-free
                if (literal.arity() == 1) {
                    if (literal.containsTerm(quantifier.getVariable(0)) && TwoQuantifiers.startsWithForall(quantifier.getQuantifiers())) {
                        retVal.add(Clause.create(quantifier, literal));
                    }
                } else if (literal.arity() == 2) {
                    if (TwoQuantifiers.FORALL_FORALL == quantifier.getQuantifiers() && 2 == variables.size()) {
                        retVal.add(Clause.create(quantifier, literal));
                    }
                } else {
                    throw new IllegalStateException("Literal arity is " + literal.arity() + " of literal " + literal);
                }
            }
        }
        return retVal;
    }

    private Set<Literal> sameArgumentsLiterals(List<Literal> literals) {
        // returns only those literals with arity higher than 1 and same arguments
        return literals.stream()
                .filter(literal -> literal.arity() > 1 && 1 == literal.argumentsStream().collect(Collectors.toSet()).size())
                .collect(Collectors.toSet());
    }

    private boolean areIsomorphic(Clause first, Clause second, boolean ignoreSecondVariableIfNotPresent) { // unify this with the SentenceState::areIsomorphic!
        // ignoreSecondVariableIfNotPresents stands for hiding things from output (it is used for VxEy & ExVy which are decomposable
        boolean firstContainsSecondVariable = first.isSecondVariableUsed();
        boolean secondContainsSecondVariable = second.isSecondVariableUsed();
        if (!firstContainsSecondVariable && !secondContainsSecondVariable && ignoreSecondVariableIfNotPresent) {
            // this branch represent the case where we have, for example,
            // Vx Ey U(x)  vs  Vx Vy U(x)
            // and we don't care about the second unused variable, so we call these two isomorphic
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
        } else if (ignoreSecondVariableIfNotPresent && first.isDecomposable() && second.isDecomposable()
                && (TwoQuantifiers.EXISTS_FORALL == first.getQuantifier().getQuantifiers() || TwoQuantifiers.FORALL_EXISTS == first.getQuantifier().getQuantifiers())
                && (TwoQuantifiers.EXISTS_FORALL == second.getQuantifier().getQuantifiers() || TwoQuantifiers.FORALL_EXISTS == second.getQuantifier().getQuantifiers())) {
            return isomorphisMatching.isomorphism(first.getQuantifierExtendedClauseWithoutOrder(), second.getQuantifierExtendedClauseWithoutOrder());
        } else {
            return false;
        }
    }

    private List<Literal> generateSingleLiterals() {
        List<Literal> result = Sugar.list();
        for (Predicate predicate : this.setup.predicates) {
            for (List<Variable> arguments : Combinatorics.variationsWithRepetition(setup.variablesSet, predicate.getArity())) {
                Literal posLiteral = new Literal(predicate.getName(), false, arguments);
                Literal negLiteral = new Literal(predicate.getName(), true, arguments);
                result.add(posLiteral);
                result.add(negLiteral);
            }
        }
        result.sort(Comparator.comparing(Literal::arity));
        return result;
    }

    private CandidateProperties checkCandidate(SentenceState refinement, MultiList<IsoClauseWrapper, Clause> fullQuantifiersIsomorphic, MultiList<IsoClauseWrapper, Clause> partialQuantifiersIsomorphic, MultiList<IsoClauseWrapper, Clause> cellIsomorphic, Set<String> lexicoFullyQuantified, Set<String> lexicoPartiallyQuantified) {
        if (setup.contradictionFilter && setup.prover9Path != null && isContradiction(refinement)) {
            if (debug) {
                printDebug("  scratching contradiction " + refinement.toFol(true, true));
            }
            return CandidateProperties.create(false, false);
        }

        if (debug) {
            printDebug(" checking isomorphism within layer");
        }

        if (setup.lexicographicalComparatorOnly) {
            if (lexicoFullyQuantified.contains(refinement.getFullyQuantifiedLexicographicallyMinimal())) {
                if (debug) { // this has higher priority!
                    printDebug("  X6' " + refinement.toFol(true, true) + " since it is lexicographically identical to some else");
                }
                return CandidateProperties.create(false, false);
            }
            if (lexicoPartiallyQuantified.contains(refinement.getPartiallyQuantifiedLexicographicallyMinimal())) {
                if (debug) {
                    printDebug("  H0 " + refinement.toFol(true, true) + " since it is lexicographically identical to some else");
                }
                return CandidateProperties.create(false, true);
            }
        } else {
            Clause isoRepresentation = refinement.getPredicateIsomorphicRepresentation().getS().get(0);
            for (Clause clause : fullQuantifiersIsomorphic.get(IsoClauseWrapper.create(isoRepresentation))) {
                if (isomorphisMatching.isomorphism(isoRepresentation, clause)) {
                    if (debug) { // this has higher priority!
                        printDebug("  X6 " + refinement.toFol(true, true) + " since it is isomorphic to some else\t" + clause);
                    }
                    return CandidateProperties.create(false, false);
                }
            }

            if (refinement.containsSecondUnusedVariable()  // this will be repeated many times since E=k x Vy U(x) will lead to second unused variable in case double existentials are forbidden
                    || refinement.hasDecomposableForallExists()
            ) {
                // TODO remove this sanity check in future
                Pair<List<Clause>, List<Clause>> pair = refinement.getPredicateIsomorphicRepresentation();
                if (pair.getS().get(0) == pair.getR().get(0)) {
                    System.out.println(pair.getS().get(0));
                    System.out.println(pair.getR().get(0));
                    throw new IllegalStateException(); // just a sanity check
                }
                isoRepresentation = refinement.getPredicateIsomorphicRepresentation().getR().get(0);
                for (Clause clause : partialQuantifiersIsomorphic.get(IsoClauseWrapper.create(isoRepresentation))) {
                    if (isomorphisMatching.isomorphism(isoRepresentation, clause)) {
                        if (debug) {
                            printDebug("  H0 " + refinement.toFol(true, true) + " since it is isomorphic to some else\t" + clause);
                        }
                        return CandidateProperties.create(false, true);
                    }
                }
            }
        }

        boolean hide = setup.cliffhangerFilter && refinement.isCliffhanger();
        if (hide && debug) {
            printDebug("  H1 " + refinement + " since it is a cliffhanger");
        }

        if (!hide && setup.thetaReducibility) {
            if (debug) {
                printDebug(" checking reducibility 1");
            }
            hide = canBeReduced(refinement);
            if (hide && debug) {
                printDebug("  H2 " + refinement + " since it can be reduced (or is second-variable-free isomorphic to something), thus not printing out, but leaving in the next layer");
            }
        }

        if (!hide && setup.quantifiersReducibility) {
            if (debug) {
                printDebug(" checking reducibility 2");
            }
            hide = shouldStayHidden(refinement);
            if (hide && debug) {
                printDebug("  H3 " + refinement + " since " + refinement.toFol(true, true));
            }
        }

        return CandidateProperties.create(!hide, true);
    }

    public boolean isContradiction(SentenceState refinement) {
        StringBuilder sos = new StringBuilder();
        refinement.clauses.stream().filter(clause -> !clause.hasCountingQuantifier())
                .forEach(clause -> sos.append(clause.getProver9Format()).append("\n"));
        if (sos.isEmpty()) {
            return false;
        }
        if (debug) {
            printDebug(" invoking contradiction test");
        }
        if (isProveable(sos.toString())) {
            return true; // counting quantifiers-free contradiction
        }

        // counting quantifiers
        if (setup.countingContradictionFilter) {
            for (Clause countingClause : refinement.clauses) {
                if (countingClause.hasCountingQuantifier() && countingClause.countLiterals() == 1 && TwoQuantifiers.EXISTS_EXISTS != countingClause.getQuantifier().getQuantifiers()) {
                    Literal literal = Sugar.chooseOne(countingClause.literals());
                    Pair<String, Integer> predicate = literal.getPredicate();
                    boolean target = !literal.isNegated();
                    Set<TwoQuantifiers> mirrorQuantifiers = mirrorQuantifiersForCountingContradictionPruning.get(countingClause.getQuantifier().getQuantifiers());
                    StringBuilder partialSOS = new StringBuilder();
                    refinement.clauses.stream()
                            .filter(clause -> countingClause != clause
                                    && clause.countLiterals() == 1
                                    && mirrorQuantifiers.contains(clause.getQuantifier().getQuantifiers())
                                    && Sugar.chooseOne(clause.literals()).getPredicate().equals(predicate)
                                    && Sugar.chooseOne(clause.literals()).isNegated() == target
                                    && (TwoQuantifiers.FORALL_FORALL == clause.getQuantifier().getQuantifiers() || literal.equalsWithoutNegation(Sugar.chooseOne(clause.literals())))
                            ).forEach(clause -> partialSOS.append(clause.getProver9Format()).append("\n"));
                    if (partialSOS.isEmpty()) {
                        continue;
                    }
                    partialSOS.append(countingClause.getProver9Format()).append("\n");
                    if (isProveable(partialSOS.toString())) {
                        return true; // is contradiction because of counting quantifiers
                    }
                }
            }
        }
        return false;
    }

    private boolean isProveable(String setOfSentences) {
        try {
            File file = File.createTempFile("problem", ".in");
            StringBuilder sb = new StringBuilder();
            sb.append("set(quiet).\n");
            sb.append("assign(max_seconds, ").append(setup.maxProver9Seconds).append(").\n");
            sb.append("assign(max_proofs, 0).\n");
            sb.append("formulas(sos).\n");
            sb.append(setOfSentences);
            sb.append("end_of_list.\n");
            Files.write(file.toPath(), Sugar.list(sb.toString()));

            ProcessBuilder processBuilder = new ProcessBuilder();
            processBuilder.command(setup.prover9Path, "-f", file.getAbsolutePath());
            Process process = processBuilder.start();

            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            boolean isContradiction = false;
            String line;
            while ((line = reader.readLine()) != null) {
                isContradiction |= line.contains("THEOREM PROVED");
            }

            int exitCode = process.waitFor();
            Files.deleteIfExists(file.toPath());
            return isContradiction;
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    private boolean shouldStayHidden(SentenceState refinement) {
        for (int outer = 0; outer < refinement.clauses.size(); outer++) {
            Clause outerClause = refinement.clauses.get(outer);
            for (int inner = outer + 1; inner < refinement.clauses.size(); inner++) {
                Clause innerClause = refinement.clauses.get(inner);
                if (areIsomorphic(outerClause, innerClause, true)
                        || thetaSubsumes(innerClause, outerClause)
                        || thetaSubsumes(outerClause, innerClause)
                ) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean thetaSubsumes(Clause first, Clause second) {
        if (first.hasCountingQuantifier() || second.hasCountingQuantifier()) {
            if (first.hasCountingQuantifier() && first.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL
                    && 1 == first.getQuantifier().firstVariableCardinality
                    && !first.isSecondVariableUsed() && first.countLiterals() == 1
                    && !second.hasCountingQuantifier() && TwoQuantifiers.startsWithExists(second.getQuantifier().getQuantifiers())
                    && !second.isFirstVariableUsed() && second.countLiterals() == 1) {
                // resolving the case (E=1 x Vy Phi(x)) implies (E x V/Ey Phi(x))
                return isomorphisMatching.subsumption(first, second); // this may be too big hammer !
            }
            // the vast majority of this field, however, is left for future development
            return false;
        }
        if (!first.isSecondVariableUsed() && !second.isSecondVariableUsed()) {
            if (first.startsWithTheSameQuantifier(second)) {
                // resolving Vx (V/Ey), Ex (V/Ey)
                return isomorphisMatching.subsumption(first, second);
            } else if (TwoQuantifiers.startsWithForall(first.getQuantifier().getQuantifiers())) {
                // by dropping domainsize=0, this resolve Vx phi(x) \implies Ex phi(x)
                return isomorphisMatching.subsumption(first, second);
            }
        } else if (first.hasSameQuantifier(second)) {
            // Vx Vy ; Vx Ey ; Ex Vy ; Ex Ey
            return isomorphisMatching.subsumption(first.getQuantifiedClause(), second.getQuantifiedClause());
        } else if (TwoQuantifiers.FORALL_FORALL == first.getQuantifier().getQuantifiers()) {
            // if it holds for VxVy there it will hold for VxEy, etc...
            return isomorphisMatching.subsumption(first, second);
        } else if (first.isDecomposable() && second.isDecomposable() &&
                ((TwoQuantifiers.FORALL_EXISTS == first.getQuantifier().getQuantifiers() && TwoQuantifiers.EXISTS_FORALL == second.getQuantifier().getQuantifiers())
                        || (TwoQuantifiers.EXISTS_FORALL == first.getQuantifier().getQuantifiers() && TwoQuantifiers.FORALL_EXISTS == second.getQuantifier().getQuantifiers()))) {
            return isomorphisMatching.subsumption(first.getQuantifierExtendedClauseWithoutOrder(), second.getQuantifierExtendedClauseWithoutOrder());
        } else if (TwoQuantifiers.EXISTS_FORALL == first.getQuantifier().getQuantifiers() && TwoQuantifiers.FORALL_EXISTS == second.getQuantifier().getQuantifiers()) {
            // if it holds for VxVy there it will hold for VxEy, etc...
            return isomorphisMatching.subsumption(first.getQuantifiedClause(), second.getQuantifiedClause());
        }
        return false;
    }

    public boolean canBeReduced(SentenceState sentence) {
        boolean reduceable;
        for (Clause clause : sentence.clauses) {
            if (clause.hasCountingQuantifier()) {
                continue; // place for extensions in future
            }
            boolean secondVariableUnused = !clause.isSecondVariableUsed();
            if (secondVariableUnused) {
                if (TwoQuantifiers.startsWithForall(clause.getQuantifier().getQuantifiers())) {
                    reduceable = isReducibleDisjunction(clause);
                } else {
                    reduceable = isReducibleConjunction(clause);
                }
            } else {
                if (clause.getQuantifier().getQuantifiers() == TwoQuantifiers.FORALL_FORALL
                        || clause.getQuantifier().getQuantifiers() == TwoQuantifiers.EXISTS_FORALL) {
                    reduceable = isReducibleDisjunction(clause); // proceed as with forall-forall since it is the same case even when fol-skolemized
                } else {
                    // proceed with a reduction on conjunction of literals
                    reduceable = isReducibleConjunction(clause);
                }
            }
            if (reduceable) {
                return true;
            }
        }
        return false;
    }

    private boolean isReducibleDisjunction(Clause clause) {
        for (Literal literal : clause.literals()) {
            Clause shorther = makeShortherClause(clause, literal);
            if (isomorphisMatching.subsumption(clause, shorther)) {
                return true;
            }
        }
        return false;
    }

    private boolean isReducibleConjunction(Clause clause) {
        for (Literal literal : clause.literals()) {
            Clause shorther = makeShortherClause(clause, literal);
            if (isomorphisMatching.subsumption(new Clause(literal), shorther)) {
                return true;
            }
        }
        return false;
    }


    private Clause makeShortherClause(Clause clause, Literal literal) {
        List<Literal> lits = Sugar.list();
        for (Literal innerLiteral : clause.literals()) {
            if (literal != innerLiteral) {
                lits.add(innerLiteral);
            }
        }
        return new Clause(lits);
    }

    private void printCandidate(SentenceState refinement) {
        printMessage(refinement.toFol(), false);
    }

    private void printComment(String message) {
        printMessage(message, true);
    }

    private void printMessage(String message, boolean isComment) {
        if (isComment) {
            System.out.println("# " + message);
        } else {
            System.out.println(message);
        }
    }

    public void loadAndContinueSearch() {
        HashMap<String, Quantifier> cache = quantifiersToCache();
        int layerIdx = 0;
        List<SentenceState> layer = Sugar.list();
        List<Clause> cells = Sugar.list();
        boolean searchHasEnded = false;
        try {
            int currentIdx = 0;
            List<SentenceState> currentLayer = Sugar.list();
            List<Clause> currentCells = Sugar.list();
            for (String line : Files.lines(setup.errOut).collect(Collectors.toList())) {
                if (line.startsWith("# starting layer")) { //  # starting layer 1 with 18 candidates
                    int idx = Integer.parseInt(line.split("layer")[1].split("with")[0].trim());
                    currentIdx = idx;
                    currentLayer = Sugar.list();
                } else if (line.startsWith("# end of candidates")) {
                    layerIdx = currentIdx;
                    layer = currentLayer;
                } else if (line.startsWith("# end cells")) {
                    cells = currentCells;
                    currentCells = Sugar.list();
                } else if (line.startsWith("# " + endingMessage)) {
                    searchHasEnded = true;
                } else if (line.startsWith("#")) {
                    continue;
                } else {
                    if (!line.trim().equals("") && !line.startsWith("(")) {
                        currentCells.add(Clause.parse(line, ',', null));
                    } else if (line.startsWith("(")) { // because we know each sentence starts with (
                        currentLayer.add(SentenceState.parse(line, cache, setup, literalCache));
                    }
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        if (searchHasEnded) {
            String continuing = "the search won't restart from this place";
            printComment(endingMessage);
            printComment(continuing);
            if (setup.statesStoring) {
                System.err.println("# " + endingMessage);
                System.err.println("# " + continuing);
            }
            return;
        }
        System.out.println("# restoring search from " + layerIdx + " layer");
        search(layerIdx, layer, cells);
    }

    public HashMap<String, Quantifier> quantifiersToCache() {
        HashMap<String, Quantifier> result = new HashMap<>();
        for (Quantifier quantifier : this.quantifiers) {
            result.put(quantifier.quantifierToString(0) + quantifier.quantifierToString(1), quantifier);
        }
        return result;
    }

    public void startFromSeed(String seed) {
        List<SentenceState> layer = parseSeed(seed, this.setup);
//        if (setup.manualSeed) { // tzn kdyz to poskladal uzivatel v ruce, tak by se melo jeste napocitat minimalita vzhledem ke generovani
//            layer = layer.stream().map(this::toSmallestOrderedSentence).collect(Collectors.toList());
//        }
        Collections.sort(layer, this::sentenceComparator); // zvladne ten komparator binary-to-unary ??? asi ne
        Set<Integer> levels = layer.stream().map(s -> s.clauses.stream().mapToInt(Clause::countLiterals).sum()).collect(Collectors.toSet());
        if (levels.size() != 1) {
            throw new IllegalStateException("All seeds have to have the same number of literals.");
        }
        fillInCellGraph(layer.stream().map(sentence -> new Pair<>(sentence, CandidateProperties.create(true, true))).collect(Collectors.toList()));
        List<Clause> cellGraphs = layer.stream().map(SentenceState::getCellGraph).filter(Objects::nonNull).collect(Collectors.toList());
        search(0, layer, cellGraphs);
    }

    private int sentenceComparator(SentenceState s1, SentenceState s2) {
        // Returns a negative integer, zero, or a positive integer as the first argument is less than, equal to, or greater than the second.
        if (s1.clauses.size() > s2.clauses.size()) { // longer clauses are preferred
            return -1;
        } else if (s1.clauses.size() < s2.clauses.size()) {
            return 1;
        }

        // s1.clauses.size() == s2.clauses.size()
        // comparing clause by clause
        for (int idx = 0; idx < s1.clauses.size(); idx++) {
            int compared = clauseComparator(s1.clauses.get(idx), s2.clauses.get(idx));
            if (0 != compared) {
                return compared;
            }
        }
        return 0;
    }

    private int clauseComparator(Clause clause1, Clause clause2) {
        if (clause1.countLiterals() != clause2.countLiterals()) {
            throw new IllegalStateException();
        }
        int quantifier1 = quantifierToOrder.get(clause1.getQuantifier());
        int quantifier2 = quantifierToOrder.get(clause2.getQuantifier());

        if (quantifier1 < quantifier2) { // the first possible quantifier is preferred
            return -1;
        } else if (quantifier1 > quantifier2) {
            return 1;
        }
        // same quantifier
        Iterator<Literal> iter1 = clause1.literals().iterator();
        Iterator<Literal> iter2 = clause2.literals().iterator();
        while (iter1.hasNext()) {
            int order1 = literalToOrder.get(iter1.next());
            int order2 = literalToOrder.get(iter2.next());
            if (order1 < order2) {
                return -1;
            } else if (order1 > order2) {
                return 1;
            }
        }
        return 0;
    }

    private List<SentenceState> parseSeed(String seed, SentenceSetup setup) {
        printComment("starting with seed\t" + seed);

        List<SentenceState> layer = Sugar.list();
        HashMap<String, Quantifier> quantifierCache = quantifiersToCache();
        seed = seed.trim();
        if (seed.startsWith("[")) {
            if (!seed.endsWith("]")) {
                throw new IllegalStateException("Unparseable seed:\t" + seed);
            }
            seed = seed.substring(1, seed.length() - 1);
            for (String sentence : seed.split(";")) {
                layer.addAll(SentenceState.parseMultiplePossibleQuantifiers(sentence, quantifierCache, literalCache, setup));
            }
        } else {
            layer.addAll(SentenceState.parseMultiplePossibleQuantifiers(seed, quantifierCache, literalCache, setup));
        }
        if (setup.fixedSeed) {
            layer.forEach(SentenceState::freezeAllClauses);
        }
        return layer;
    }
}
