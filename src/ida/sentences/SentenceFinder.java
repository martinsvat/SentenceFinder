package ida.sentences;

import ida.ilp.logic.*;
import ida.ilp.logic.quantifiers.Quantifier;
import ida.ilp.logic.quantifiers.QuantifiersGenerator;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.caches.ClausesCache;
import ida.sentences.caches.LiteralsCache;
import ida.sentences.filters.SingleFilter;
import ida.sentences.filters.JoiningFilter;
import ida.sentences.generators.ClausesGenerator;
import ida.sentences.generators.LiteralsGenerator;
import ida.sentences.generators.PredicateGenerator;
import ida.utils.Sugar;
import ida.utils.collections.Counters;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class SentenceFinder {

    private final String BASIC_CLAUSES = "basic clauses";
    private final String BASIC_CLAUSES_ENDS = "end of basic clauses";

    private final String ENDING_MESSAGE = "the search has ended!";
    private final String OUT_OF_TIME_MESSAGE = "the search has ended because of the time limit!";
    private final String SEEDS_START = "seeds follow";
    private final String SEEDS_END = "end of seeds";
    private final SentenceSetup setup;
    private final boolean debug;
    private final List<Quantifier> quantifiers;
    private final MultiList<Quantifier, Quantifier> quantifierSuccessors;
    private final Map<Quantifier, Quantifier> quantifiersMirrors;
    public final List<Literal> literals;
    private final Matching matching = new Matching();
    private final SentenceState emptySentence;

    private final MultiList<Clause, SentenceState> cellGraphs = new MultiList<>(); // this is just a dev tool

    public SentenceFinder(SentenceSetup setup) {
        this.setup = setup;
        this.debug = setup.debug;

        if (2 != setup.variablesSet.size() || 2 != setup.variables.size()) {
            throw new UnsupportedOperationException("Only 2-variables are supported by this implementation.");
        }

        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> quanty = QuantifiersGenerator.generateQuantifiers(setup.quantifiers, setup.maxK, setup.maxK > 0 && setup.maxCountingClauses > 0 && setup.maxLiteralsPerCountingClause > 0, setup.doubleCountingExist, setup.variables);
        this.quantifiers = quanty.getR();
        this.quantifierSuccessors = quanty.getS();
        this.quantifiersMirrors = quanty.getT(); // to deal with extension when we break from decomposable to non-decomposable
        this.literals = LiteralsGenerator.generate(setup.variables, setup.predicates); // this important so we have intertwined literals before any other parsing take places!
        this.literals.sort(Comparator.comparing(Literal::toString));
        this.emptySentence = new SentenceState(Sugar.list(), setup);
    }


    public void loadAndContinueSearch() {
        SentenceState seed = null;
        List<Clause> baseClause = Sugar.list();
        MultiList<Integer, SentenceState> sentences = new MultiList<>();
        MultiList<IsoClauseWrapper, Clause> cellGraphs = new MultiList<>();

        boolean generatedAll = false;
        boolean outOfTime = false;
        final int NOTHING = -1;
        final int SEED = 0;
        final int BASE_CLAUSES = 1;

        int seedLiterals = 0;
        boolean lastLineComment = false;
        int state = NOTHING;
        try {
            for (String line : Files.lines(setup.errOut).toList()) {
                if (line.isBlank()) {
                    continue;
                } else if (line.startsWith("#")) {
                    line = line.substring(1).trim();
                    if (line.startsWith(BASIC_CLAUSES)) {
                        state = BASE_CLAUSES;
                    } else if (line.startsWith(BASIC_CLAUSES_ENDS)) {
                        state = NOTHING;
                    } else if (line.startsWith(SEEDS_START)) {
                        state = SEED;
                    } else if (line.startsWith(SEEDS_END)) {
                        state = NOTHING;
                    } else if (line.equals(ENDING_MESSAGE)) {
                        generatedAll = true;
                    } else if (line.equals(OUT_OF_TIME_MESSAGE)) {
                        outOfTime = true;
                    }
                    lastLineComment = true;
                } else {
                    switch (state) {
                        case SEED -> {
                            seed = SentenceState.parse(line, this.setup);
                            seedLiterals = seed.countLiterals();
                            if (!sentences.isEmpty()) {
                                throw new IllegalStateException("Cannot parse seed after some sentences have been loaded.");
                            }
                        }
                        case BASE_CLAUSES -> baseClause.add(Clause.parseWithQuantifier(line));
                        default -> {
                            String[] split = line.split(";");
                            SentenceState sentence = SentenceState.parse(split[0], this.setup);
                            sentences.put(sentence.countLiterals() - seedLiterals, sentence);

                            Clause cellGraph = Clause.parse(split[split.length - 1], ',', null);
                            IsoClauseWrapper icw = IsoClauseWrapper.create(cellGraph);
                            boolean found = false;
                            for (Clause clause : cellGraphs.get(icw)) {
                                if (matching.isomorphism(clause, icw.getOriginalClause())) {
                                    found = true;
                                    break;
                                }
                            }
                            if (!found) {
                                cellGraphs.put(icw, icw.getOriginalClause());
                            }

                            sentence.setCellGraph(cellGraph);
                            lastLineComment = false;
                        }
                    }
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        if (generatedAll) {
            printComment("the previous search has ended, thus the search cannot continue from that place!");
            printComment(ENDING_MESSAGE);
            return;
        }
        if (!lastLineComment) {
            printComment("the previous search has ended in an incompatible state, thus the search cannot continue from this place");
            return;
        }

        if (null != seed) {
            checkSeed(seed, setup.predicates, setup.variables);
            printComment(SEEDS_START);
            printCandidate(seed.toFol());
            if (setup.statesStoring) {
                printMessage(seed.toFol(), false, System.err);
            }
            printComment(SEEDS_END);
        }
        if (setup.statesStoring) {
            printSerialization("throwing out all sentences with their cell graphs", true);
        }

        if (setup.statesStoring) {
            printSerialization("printing out previous layers", true);
            sentences.values().stream().flatMap(List::stream)
                    .forEach(sentence -> printSerialization(sentenceToSerialization(sentence), false));
        }
        int maxLevel = sentences.keySet().stream().mapToInt(i -> i).max().orElse(0);
        generate(seed, baseClause, sentences, cellGraphs, maxLevel + 1);
    }

    public void startFromSeed(String seed) {
        SentenceState sentence = parseSeed(seed);
        checkSeed(sentence, setup.predicates, setup.variables);
        printComment(SEEDS_START);
        printCandidate(sentence.toFol());
        if (setup.statesStoring) {
            printMessage(sentence.toFol(), false, System.err);
        }
        printComment(SEEDS_END);
        generate(sentence, null, new MultiList<>(), new MultiList<>(), 1);
    }

    private void checkSeed(SentenceState sentence, List<Predicate> predicates, List<Variable> variables) {
        for (Clause clause : sentence.clauses) {
            if (!Sugar.setFromCollections(clause.getQuantifier().getUsedVariables()).equals(clause.variables())) {
                setup.closeRedis();
                throw new IllegalStateException("Every variable in the seed has to be used in the formula! See\t" + clause.toFOL());
            }
            List<Variable> prefixVariables = clause.getQuantifier().getVariables();
            List<Variable> setupVariables = variables;
            if (1 == clause.getQuantifier().numberOfUsedVariables) {
                prefixVariables = prefixVariables.subList(0, 1);
                setupVariables = setupVariables.subList(0, 1);
            }
            if (!prefixVariables.equals(setupVariables)) {
                setup.closeRedis();
                throw new IllegalStateException("The variables should be named\t" + setupVariables + "\tinstead of\t" + prefixVariables);
            }

        }
        Set<Predicate> predicatesInside = sentence.getPredicates().stream().map(p -> PredicateFactory.getInstance().create(p.r, p.s)).collect(Collectors.toSet());
        if (!Sugar.setFromCollections(predicates).containsAll(predicatesInside)) {
            setup.closeRedis();
            throw new IllegalStateException("The following sentence contains literals which are not in the language:\t" + sentence.toFol());
        }
    }

    private SentenceState parseSeed(String seed) {
        printComment("parsing seed\t" + seed);
        seed = seed.trim();
        if (seed.startsWith("[")) {
            if (!seed.endsWith("]")) {
                throw new IllegalStateException();
            }
        }

        SentenceState result = SentenceState.parse(seed, setup);
        List<Clause> cached = result.clauses.stream().map(clause -> {
            if (clause.getId() < 0) {
                Clause isThere = ClausesCache.getInstance().get(clause.getCannonic());
                if (null == isThere) {
                    clause = ClausesCache.getInstance().get(clause);
                } else {
                    clause = isThere;
                }
            }
            return clause;
        }).toList();
        return new SentenceState(cached, setup);
    }

    public void generate() {
        generate(null, null, new MultiList<>(), new MultiList<>(), 1);
    }

    public void generate(SentenceState seed, List<Clause> allClauses, MultiList<Integer, SentenceState> sentences, MultiList<IsoClauseWrapper, Clause> cellGraphs, int startLevel) {
        long startTime = System.nanoTime();
        printComment("there are " + this.quantifiers.size() + " quantifiers and " + this.literals.size() + " literals");
        ClausesGenerator clausesGen = new ClausesGenerator(this.literals, this.quantifiers, this.quantifierSuccessors, this.quantifiersMirrors, PredicateGenerator.generateFollowers(setup.predicates), setup.debug);
        if (null == allClauses) {
            allClauses = generateClauses(clausesGen);
        }

        List<Clause> clausesToCheck = allClauses;
        if (null != seed && !allClauses.containsAll(seed.clauses)) {
            clausesToCheck = Sugar.listFromCollections(Sugar.setFromCollections(allClauses, seed.clauses));
        }
        indexClausesIfNeeded(clausesToCheck);
        if (setup.quantifiersReducibility) {
            long startQuantifiersReducibility = System.nanoTime();
            printComment("starting to precompute quantifiers reducibility " + allClauses.size());
            long forbiddens = clausesGen.precomputeQuantifiersReducibility(allClauses, setup.maxClauses, setup.maxLiteralsPerClause, setup.maxOverallLiterals, setup);
            printComment("quantifiers reducibility done within " + timeToNowInSeconds(startQuantifiersReducibility) +
                    " resulting in " + forbiddens + " forbiddens n-tuples");
        }

        printComment("initialization time " + timeToNowInSeconds(startTime));

        if (setup.statesStoring) {
            flushBaseClauses(allClauses);
        }

        Thread.setDefaultUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
            @Override
            public void uncaughtException(Thread t, Throwable e) {
                printComment("ending because there is a exception thrown by some thread");
                printComment("exception\t" + t.getName() + " " + e.getMessage());
                setup.closeRedis();
                e.printStackTrace();
                System.exit(-111);
            }
        });

        MultiList<Integer, Clause> clausesByLength = new MultiList<>();
        allClauses.forEach(clause -> clausesByLength.put(clause.countLiterals(), clause));
        runConnection(sentences, cellGraphs, clausesByLength, getSentenceFilters(clausesGen, this.setup),
                getJoiningFilters(clausesGen, this.setup), getHideOnlyFilters(clausesGen, this.setup), startLevel, seed,
                clausesGen);

        printComment("ending with " + sentences.entrySet().stream().mapToInt(e -> e.getValue().size()).sum() + " in " + timeToNowInSeconds(startTime));
        printComment(shouldEnd(startTime) ? OUT_OF_TIME_MESSAGE : ENDING_MESSAGE);
    }

    public Pair<List<Clause>, ClausesGenerator> initForQueries() {
        long startTime = System.nanoTime();
        printComment("there are " + this.quantifiers.size() + " quantifiers and " + this.literals.size() + " literals");
        ClausesGenerator clausesGen = new ClausesGenerator(this.literals, this.quantifiers, this.quantifierSuccessors, this.quantifiersMirrors, PredicateGenerator.generateFollowers(setup.predicates), setup.debug);
        List<Clause> allClauses = generateClauses(clausesGen);
        indexClausesIfNeeded(allClauses);
        if (setup.quantifiersReducibility) {
            long startQuantifiersReducibility = System.nanoTime();
            printComment("starting to precompute quantifiers reducibility " + allClauses.size());
            long forbiddens = clausesGen.precomputeQuantifiersReducibility(allClauses, setup.maxClauses, setup.maxLiteralsPerClause, setup.maxOverallLiterals, setup);
            printComment("quantifiers reducibility done within " + timeToNowInSeconds(startQuantifiersReducibility) +
                    " resulting in " + forbiddens + " forbiddens n-tuples");
        }
        printComment("initialization time " + timeToNowInSeconds(startTime));
        return new Pair<>(allClauses, clausesGen);
    }

    private void indexClausesIfNeeded(List<Clause> clauses) {
        Set<Integer> indexes = clauses.stream().map(Clause::getId).filter(idx -> idx >= 0).collect(Collectors.toSet());
        if (indexes.size() != clauses.size() || !indexes.equals(IntStream.range(0, clauses.size()).boxed().collect(Collectors.toSet()))) {
            List<Clause> sorted = clauses.stream().sorted(Comparator.comparing(Clause::getCannonic)).collect(Collectors.toList());
            for (int idx = 0; idx < sorted.size(); idx++) {
                sorted.get(idx).setId(idx);
            }
        }
    }

    public List<SingleFilter<SentenceState>> getHideOnlyFilters(ClausesGenerator generator, SentenceSetup setup) {
        List<SingleFilter<SentenceState>> retVal = Sugar.list();
        if (setup.reflexiveAtoms) {
            retVal.add(generator.reflexiveAtoms());
        }
        return retVal;
    }

    public List<JoiningFilter> getJoiningFilters(ClausesGenerator clausesGen, SentenceSetup setup) {
        List<JoiningFilter> connectionFilters = Sugar.list();
        if (setup.debug) {
            connectionFilters.add(clausesGen.creationLogging("JoiningFilters"));
        }
        connectionFilters.add(clausesGen.disjunctiveClauses());
        if (setup.languageBias) {
            connectionFilters.add(clausesGen.languageBias());
        }
        if (setup.maxClauses > 0) {
            connectionFilters.add(clausesGen.maxClauses(setup.maxClauses));
        }
        if (setup.decomposableComponents) {
            connectionFilters.add(clausesGen.connectedComponents());
        }
        if (setup.trivialConstraints) {
            connectionFilters.add(clausesGen.trivialConstraints());
        }
        if (setup.quantifiersReducibility) {
            connectionFilters.add(clausesGen.twoFormulaeFilter());
            if (setup.maxClauses > 2) {
                connectionFilters.add(clausesGen.decomposableFilter());
            }
        }
        if (setup.debug) {
            connectionFilters.add(clausesGen.creationLogging("CreationLogging1"));
        }
        return connectionFilters;
    }

    public List<SingleFilter<SentenceState>> getSentenceFilters(ClausesGenerator clausesGen, SentenceSetup setup) {
        List<SingleFilter<SentenceState>> sentenceFilters = Sugar.list();
        if (setup.contradictionFilter) {
            sentenceFilters.add(clausesGen.contradictionFilter(null == setup.prover9Path ? null : Paths.get(setup.prover9Path), setup.maxProver9Seconds));
        }
        return sentenceFilters;
    }

    private void runConnection(MultiList<Integer, SentenceState> sentences, MultiList<IsoClauseWrapper, Clause> cellGraphs,
                               MultiList<Integer, Clause> clausesByLength, List<SingleFilter<SentenceState>> sentenceFilters,
                               List<JoiningFilter> connectionFilters, List<SingleFilter<SentenceState>> hideOnlyFilters,
                               int startLevel, SentenceState seed, ClausesGenerator clausesGenerator) {
        printComment("going to connect clauses with connection filters: " + makeString(connectionFilters));
        printComment("going to connect clauses with sentence filters: " + makeString(sentenceFilters));
        printComment("going to connect clauses with hide filters: " + makeString(hideOnlyFilters));
        StringBuilder info = new StringBuilder("info: ");
        StringBuilder isoDistribution = new StringBuilder("iso: ");
        StringBuilder cellDistribution = new StringBuilder("cells: ");
        StringBuilder hashDistributions = new StringBuilder("hashes: ");
        long start = System.nanoTime();

        for (int layerToFree = 1; layerToFree < startLevel - setup.maxLiteralsPerClause; layerToFree++) { // free memory from search continuing
            sentences.get(layerToFree).clear();
        }
        Triple<List<SentenceState>, String, Counters<Integer>> isoTriple = new Triple<>(null, "", new Counters<>());

        for (int numberOfLiterals = startLevel; numberOfLiterals <= setup.maxOverallLiterals; numberOfLiterals++) {
            // dev
            List<Clause> cls = Sugar.list();
            clausesByLength.values().forEach(cls::addAll);
            List<SentenceState> s = Sugar.list();
            sentences.values().forEach(s::addAll);
            List<Clause> cg = Sugar.list();
            cellGraphs.values().forEach(cg::addAll);
            printComment("stats " + numberOfLiterals
                    + "\tc " + clausesToHistogram(cls)
                    + "\ts " + sentencesToHistogram(s)
                    + "\tg" + clausesToHistogram(cg));
            /// end dev

            // generating
            long layerStart = System.nanoTime();
            printComment("starting to generate all clauses of length exactly " + numberOfLiterals + " literals");
            //List<SentenceState> layerSentences = connectToSize(numberOfLiterals, sentences, clausesByLength, connectionFilters);
            List<SentenceState> layerSentences = connectToSizeParallel(numberOfLiterals, sentences, clausesByLength, connectionFilters, seed, clausesGenerator);
            Long generation = timeToNowInSeconds(layerStart);
            printComment("there are " + layerSentences.size() + " sentences generated within " + generation);
            int rawSize = layerSentences.size();
            if (shouldEnd(start)) {
                break;
            }

            if (debug) {
                debugOutput("raw", layerSentences);
            }

            // pruning (iso, contradictions,...)
            long pruningStart = System.nanoTime();
            layerSentences = layerSentences.stream()
                    .parallel()
                    .filter(sentence -> sentenceFilters.stream().allMatch(filter -> filter.test(sentence))).toList();
            if (setup.negations && setup.isomorphicSentences && setup.permutingArguments && setup.lexicographicalMatching) {
                ConcurrentHashMap.KeySetView<String, Boolean> iso = ConcurrentHashMap.newKeySet();
                List<SentenceState> prunedSentences = layerSentences.parallelStream()
                        .filter(sentence -> iso.add(sentence.getUltraCannonic()))
                        .collect(Collectors.toList());
                isoTriple = new Triple<>(prunedSentences, "", new Counters<>());
            } else {
                isoTriple = isoPruneParallel(layerSentences, clausesGenerator);
            }
            layerSentences = isoTriple.getR();

            Long pruning = timeToNowInSeconds(pruningStart);
            int afterPruneCount = layerSentences.size();
            printComment("there are " + layerSentences.size() + " sentence after pruning done within " + pruning);
            sentences.putAll(numberOfLiterals, layerSentences);
            if (shouldEnd(start)) {
                break;
            }

            if (debug) {
                debugOutput("after-pruning", layerSentences);
            }


            // hiding (e.g. reflexive atoms), cell-graph,...
            long filteringStart = System.nanoTime();
            Set<SentenceState> hide = ConcurrentHashMap.newKeySet();
            layerSentences.parallelStream()
                    .filter(sentence -> !hideOnlyFilters.stream().allMatch(f -> f.test(sentence)))
                    .forEach(hide::add);

            int hideBeforeCallGraph = hide.size();

            resolveCellGraphHiding(layerSentences, hide, cellGraphs, clausesGenerator);
            if (setup.collectCellGraphs) { // this is just a dev tool
                showSameCellGraphs();
            }
            Long filtering = timeToNowInSeconds(filteringStart);
            int displaySize = layerSentences.size() - hide.size();
            printComment("there are " + (displaySize) + " sentence after filtering within " + filtering);
            printComment("there were " + afterPruneCount + " after pruning from which " + hideBeforeCallGraph + " were hidden by hiding filters and exactly " + (hide.size() - hideBeforeCallGraph) + " were hidden using cell graph pruning and so " + displaySize + " left");
            if (shouldEnd(start)) {
                break;
            }

            if (debug) {
                debugOutput("after-filtering", layerSentences.stream().filter(sentence -> !hide.contains(sentence)).toList());
            }


            // printing
            long printingStart = System.nanoTime();
            layerSentences.stream()
                    .filter(sentence -> !hide.contains(sentence))
                    .map(SentenceState::getUltraCannonic)
                    .sorted().forEach(this::printCandidate);
            Long printing = timeToNowInSeconds(printingStart);
            if (this.setup.statesStoring) {
                layerSentences.stream().sorted(Comparator.comparing(SentenceState::getUltraCannonic))
                        .forEach(sentence -> printSerialization(sentenceToSerialization(sentence), false));
            }

            if (debug) {
                clausesGenerator.flushLogger();
            }

            // free memory
            for (SentenceState sentence : layerSentences) {
                sentence.freeMemory();
            }
            int layerToFree = numberOfLiterals - setup.maxLiteralsPerClause;
            if (layerToFree > 0 && sentences.containsKey(layerToFree)) {
                sentences.get(layerToFree).clear();
            }


            long layerTime = generation + pruning + filtering + printing;
            printComment("finished layer with exactly " + numberOfLiterals + " literals, overall time was " + (layerTime));
            info.append(numberOfLiterals).append(": ").append(displaySize)
                    .append(" (").append(afterPruneCount).append(", ").append(rawSize).append(")")
                    .append(" in ").append(layerTime)
                    .append(" [ ").append(generation).append(", ").append(pruning).append(", ")
                    .append(filtering).append(", ").append(printing).append("]; ");
            printComment(info.toString());

            isoDistribution.append(" ").append(numberOfLiterals).append(": [").append(isoTriple.getS()).append("]");
            printComment(isoDistribution.toString());
            cellDistribution.append(" ").append(numberOfLiterals).append(": [").append(toDistribution(cellGraphs)).append("]");
            printComment(cellDistribution.toString());
            hashDistributions.append(" ").append(numberOfLiterals)
                    .append(": [").append(histogramToString(isoTriple.getT())).append("]")
                    .append(" [").append(histogramToString(toCounter(cellGraphs.entrySet()))).append("]");
            printComment(hashDistributions.toString());
            if (shouldEnd(start)) {
                break;
            }
        }
    }

    // dev & debug
    private void showSameCellGraphs() {
        cellGraphs.entrySet().stream()
                .filter(entry -> entry.getValue().size() > 1)
                .sorted(Comparator.comparing(entry -> entry.getValue().size()))
                .forEach(entry -> {
                    StringBuilder connected = new StringBuilder("#-----------");
                    entry.getValue().stream().sorted(Comparator.comparing(SentenceState::getUltraCannonic))
                            .forEach(s -> connected.append("\n#\t" + s.getUltraCannonic() + "\t;\t" + s));
                    System.err.println(connected);
                });
    }

    // RL-related
    public List<Clause> allRefinements(SentenceState sentence, List<Clause> clauses, List<SingleFilter<SentenceState>> sentenceFilters,
                                       List<JoiningFilter> connectionFilters, ClausesGenerator clausesGenerator) {
        // generating
        long layerStart = System.nanoTime();
        List<Pair<SentenceState, Clause>> refinements = clauses.stream().filter(clause -> connectionFilters.stream().allMatch(filter -> filter.test(sentence, clause)))
                .map(clause -> new Pair<>(sentence.extend(clause), clause))
                .filter(pair -> sentenceFilters.stream().allMatch(filter -> filter.test(pair.getR())))
                .toList();
        // pruning (iso-pruning)
        long pruningStart = System.nanoTime();
        if (!setup.negations || !setup.isomorphicSentences || !setup.permutingArguments || !setup.lexicographicalMatching) {
            throw new IllegalStateException();
        }
        int beforePruneCount = refinements.size();
        Map<String, Clause> isoPrune = new HashMap<>();
        for (Pair<SentenceState, Clause> pair : refinements) {
            String canonic = pair.getR().getUltraCannonic();
            if (!isoPrune.containsKey(canonic) || pair.getS().getCannonic().compareTo(isoPrune.get(canonic).getCannonic()) < 0) {
                isoPrune.put(canonic, pair.getS());
            }
        }
        Long pruning = timeToNowInSeconds(pruningStart);
        int afterPruneCount = isoPrune.size();
        System.out.println("there are " + beforePruneCount + " (out of " + clauses.size() + ") which resulted in " + afterPruneCount);
//        return isoPrune.values();
        return Sugar.listFromCollections(isoPrune.values());
    }

    private void debugOutput(String token, List<SentenceState> list) {
        printComment(token + " start");
        list.stream().map(sentence -> new Pair<>(sentence.getUltraCannonic(), sentence.toFol()))
                .sorted(Comparator.comparing(Pair::getR))
                .forEach(pair -> printComment(pair.getR() + " ; " + pair.getS()));
        printComment(token + " end");
    }


    private String sentenceToSerialization(SentenceState sentence) {
        return sentence.getUltraCannonic() + " ; " + sentence.toFol(true) + " ; " + sentence.getCellGraph();
    }

    private <S, T> String toDistribution(MultiList<S, T> multiList) {
        Counters<Integer> counter = new Counters<>();
        for (Map.Entry<S, List<T>> entry : multiList.entrySet()) {
            counter.increment(entry.getValue().size());
        }
        return histogramToString(counter);
    }

    private String toDistribution(ConcurrentIsoHandler multiList) {
        Counters<Integer> counter = new Counters<>();
        for (Map.Entry<IsoClauseWrapper, List<Clause>> entry : multiList.entrySet()) {
            counter.increment(entry.getValue().size());
        }
        return histogramToString(counter);
    }

    private void printCandidate(String candidate) {
        printMessage(candidate, false, System.out);
    }

    private void resolveCellGraphHiding(List<SentenceState> layerSentences, Set<SentenceState> hide, MultiList<IsoClauseWrapper, Clause> cellGraphs, ClausesGenerator clausesGenerator) {
        if (null == setup.cellGraph || !setup.computeCellGraph || layerSentences.isEmpty()) {
            return;
        }
        fillInCellGraphs(dropComputed(layerSentences));

        // proceed hide as first! then do the same with layerSentence
        // firstly hide what should be hidden
        forcedInput(hide, cellGraphs);
        // this most likely doesn't need parallelization because the bottleneck is cell-graph computation
        MultiList<Clause, SentenceState> parents = new MultiList<>();
        for (SentenceState sentence : layerSentences) {
            if (hide.contains(sentence)) {
                continue;
            }
            boolean found = false;
            IsoClauseWrapper icw = IsoClauseWrapper.create(sentence.getCellGraph());
            for (Clause clause : cellGraphs.get(icw)) {
                if (matching.isomorphism(clause, icw.getOriginalClause())) {
                    if (parents.containsKey(clause)) {
                        if (parents.containsKey(clause)) {
                            parents.put(clause, sentence);
                        } else {
                            if (clausesGenerator.useLogger) {
                                clausesGenerator.log(sentence, null, "CellGraph-Inter");
                            }
                            hide.add(sentence); // this sentence is cell-isomorphic to something with less literals
                        }
                        if (setup.collectCellGraphs) { // this is just a dev tool
                            this.cellGraphs.put(clause, sentence);
                        }
                    }
                    found = true;
                    break;
                }
            }
            if (!found) {
                cellGraphs.put(icw, icw.getOriginalClause());
                parents.put(icw.getOriginalClause(), sentence);
                if (setup.collectCellGraphs) { // this is just a dev tool
                    this.cellGraphs.put(sentence.getCellGraph(), sentence);
                }
            }
        }

        // hide non-minimals!
        parents.values().parallelStream()
                .filter(values -> values.size() > 1)
                .forEach(list -> list.stream().sorted(Comparator.comparing(SentenceState::getUltraCannonic))
                        .skip(1)
                        .forEach(sentence -> {
                            if (clausesGenerator.useLogger) {
                                clausesGenerator.log(sentence, null, "CellGraph-Intra");
                            }
                            hide.add(sentence);
                        }));
    }

    // TODO parallelize this???
    private void forcedInput(Set<SentenceState> sentences, MultiList<IsoClauseWrapper, Clause> cellGraphs) {
        for (SentenceState sentence : sentences) {
            boolean found = false;
            IsoClauseWrapper icw = IsoClauseWrapper.create(sentence.getCellGraph());
            for (Clause clause : cellGraphs.get(icw)) {
                if (matching.isomorphism(clause, icw.getOriginalClause())) {
                    found = true;
                    if (setup.collectCellGraphs) { // this is just a dev tool
                        this.cellGraphs.put(clause, sentence);
                    }
                    break;
                }
            }
            if (!found) {
                cellGraphs.put(icw, icw.getOriginalClause());
                if (setup.collectCellGraphs) { // this is just a dev tool
                    this.cellGraphs.put(sentence.getCellGraph(), sentence);
                }
            }
        }
    }

    private List<SentenceState> dropComputed(List<SentenceState> layerSentences) {
        if (null == setup.redisConnection) {
            System.out.println("E2");
            return layerSentences;
        }
        return layerSentences.stream().filter(sentence -> {
            String cellGraph = setup.redisConnection.get(sentence.getUltraCannonic());
            if (null == cellGraph) {
                return true;
            }
            sentence.setCellGraph(Clause.parse(cellGraph, ',', null));
            return false;
        }).collect(Collectors.toList());
    }

    private void fillInCellGraphs(List<SentenceState> cellGraphQueue) {
        if (cellGraphQueue.isEmpty()) {
            return;
        }
        try {
            File file = File.createTempFile("sentences", ".in");
            StringBuilder sb = new StringBuilder();
            cellGraphQueue.forEach(sentence -> sb.append(sb.isEmpty() ? "" : "\n").append(sentence.getUltraCannonic()));
            Files.write(file.toPath(), Sugar.list(sb.toString()));

            ProcessBuilder processBuilder = new ProcessBuilder();
//            if (setup.juliaSoVersion != null) { // TODO throw this unused version out :))
//                processBuilder.command("julia", "--sysimage", setup.juliaSoVersion, "--threads", "" + setup.juliaThreads, setup.cellGraphPath, file.getAbsolutePath(), "" + setup.cellTimeLimit);
//            } else {
            processBuilder.command("julia", "--threads", "" + setup.juliaThreads, setup.cellGraph, file.getAbsolutePath(), "" + setup.cellTimeLimit);

//            System.out.println("the input is in\t" + file.getAbsolutePath());
            Process process = processBuilder.start();

            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            int addedCellGraphs = 0;
            while ((line = reader.readLine()) != null) {
                if (line.startsWith("[")) {
                    String wholeLine = line;
                    // parsing a cell-graph
                    line = line.substring(1, line.length() - 1);
                    Clause cellGraph = parseCellGraph(cellGraphQueue, processBuilder, line, addedCellGraphs, wholeLine);
                    SentenceState sentence = cellGraphQueue.get(addedCellGraphs);
                    sentence.setCellGraph(cellGraph);
                    if (null != setup.redisConnection) {
                        setup.redisConnection.set(sentence.getUltraCannonic(), cellGraph.toString());
                    }
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

    private Clause parseCellGraph(List<SentenceState> cellGraphQueue, ProcessBuilder processBuilder, String line, int addedCellGraphs, String wholeLine) {
        Clause cellGraph = null;
        if (line.trim().isEmpty()) {
            // now, there are only [] meaning the sentence was a contradiction, thus scratching it completely... or it took too much time to compute its cell graph, so prune it from the search anyway
            cellGraph = Clause.parse("");
        } else {
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

            cellGraph = new Clause(literals);
        }
        return cellGraph;
    }

    private Collection<? extends Literal> parseSingleCellGraph(String graph, int graphIdx, VariableSupplier
            variableSupplier, VariableSupplier sumSupplier, VariableSupplier productSupplier,
                                                               VariableSupplier weightVariableSupplier,
                                                               Map<String, Term> expressionCache,
                                                               int addedCellGraphs, List<SentenceState> cellGraphQueue,
                                                               ProcessBuilder processBuilder, String wholeLine) {
        List<Literal> literals = Sugar.list();
        Variable graphVar = Variable.construct("g" + graphIdx);
        for (Literal literal : Clause.parse(graph, ',', null).literals()) {
            Literal transofmed = null;
            if (literal.predicate().startsWith("L")) { // L(x3, 4, 1)
                transofmed = new Literal(literal.predicate(),
                        variableSupplier.get(literal.get(0) + "-" + graphIdx),
                        parseSymbolicWeightStateful(literal.get(1), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        parseSymbolicWeightStateful(literal.get(2), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar);
            } else if (literal.predicate().startsWith("E")) { //  E(x1, x2, 2)
                transofmed = new Literal(literal.predicate(),
                        variableSupplier.get(literal.get(0) + "-" + graphIdx),
                        variableSupplier.get(literal.get(1) + "-" + graphIdx),
                        parseSymbolicWeightStateful(literal.get(2), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar);
            } else if (literal.predicate().startsWith("W")) { //  W(1)
                transofmed = new Literal(literal.predicate(),
                        parseSymbolicWeightStateful(literal.get(0), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar);
            } else if (literal.predicate().startsWith("C")) { //  C(name_i, w_i, r_ii, k, inner_ri) k is a scalar (size of the clique)
                transofmed = new Literal(literal.predicate(),
                        variableSupplier.get(literal.get(0) + "-" + graphIdx),
                        parseSymbolicWeightStateful(literal.get(1), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        parseSymbolicWeightStateful(literal.get(2), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        parseSymbolicWeightStateful(literal.get(3), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        parseSymbolicWeightStateful(literal.get(4), sumSupplier, productSupplier, weightVariableSupplier, literals, expressionCache),
                        graphVar);
            } else {
                System.err.println("error while computing cell-graph at " + addedCellGraphs + " out of " + cellGraphQueue.size());
                System.err.println(cellGraphQueue.get(addedCellGraphs).toFol());
                System.err.println(processBuilder.command());
                System.err.println(wholeLine);
                System.err.println(graph);
                System.err.println(literal);
                throw new IllegalStateException();
            }
            literals.add(LiteralsCache.getInstance().get(transofmed));
        }
        literals.add(LiteralsCache.getInstance().get(new Literal("G", graphVar)));
        return literals;
    }

    private Term parseSymbolicWeightStateful(Term constant, VariableSupplier sumSupplier, VariableSupplier productSupplier,
                                             VariableSupplier weightVariableSupplier, List<Literal> parseTree, Map<String, Term> expressionCache) {
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
                        parseTree.add(LiteralsCache.getInstance().get(new Literal("P", arguments)));
                    } else { // scalar
                        parseTree.add(LiteralsCache.getInstance().get(new Literal("P", productVariable, new Constant(expr))));
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
            parseTree.add(LiteralsCache.getInstance().get(new Literal(sum.getS() ? "Md" : "M", finalTerm, sum.getR()))); // M stands for addition, Md for distraction
        }

        expressionCache.put(constant.name(), finalTerm);
        return finalTerm;
    }

    private Triple<List<SentenceState>, String, Counters<Integer>> isoPruneParallel(List<SentenceState> sentences, ClausesGenerator clausesGenerator) {
//        System.out.println("isoPruneParallel");
        LiteralsCache cache = LiteralsCache.getLayer();
        ConcurrentIsoHandler iso = new ConcurrentIsoHandler();
        List<SentenceState> retVal = sentences
                .parallelStream()
                .filter(sentence -> {
//                    boolean val = !iso.contains(sentence.getICW());
                    SentenceState witness = iso.contains(sentence.getICW(cache));
                    boolean val = null == witness;
                    if (clausesGenerator.useLogger && !val) {
                        clausesGenerator.log(sentence, null, "IsoPruneParallel", witness);
                    }
                    return val;
                }).collect(Collectors.toList());
        cache.forget();
        return new Triple<>(retVal, toDistribution(iso), toCounter(iso.entrySet()));
    }

    // TODO these two methods are not nice, they are recopy but do the same thing :(
    private Counters<Integer> toCounter(Collection<Map.Entry<IsoClauseWrapper, List<Clause>>> entries) {
        Counters<Integer> hashToCommon = new Counters<>();
        for (Map.Entry<IsoClauseWrapper, List<Clause>> entry : entries) {
            hashToCommon.add(entry.getKey().hashCode(), entry.getValue().size());
        }
        Counters<Integer> retVal = new Counters<>();
        for (Map.Entry<Integer, Integer> entry : hashToCommon.toMap().entrySet()) {
            retVal.increment(entry.getValue());
        }
        return retVal;
    }

    private void flushBaseClauses(List<Clause> allClauses) {
        printSerialization(BASIC_CLAUSES, true);
        allClauses.stream().sorted(Comparator.comparing(Clause::getCannonic))
                .forEach(c -> printSerialization(c.getCannonic(true), false));
//        allClauses.stream()
//                .map(c -> new Pair<>(c, c.getCannonic()))
//                .sorted(Comparator.comparing(Pair::getS))
//                .forEach(p -> printSerialization(p.getS() + " ; " + p.getR().toFOL(), false));
        printSerialization(BASIC_CLAUSES_ENDS, true);

    }

    private List<Clause> generateClauses(ClausesGenerator generator) {
        long startTime = System.nanoTime();
        List<SingleFilter<Clause>> filters = Sugar.list(
                generator.maxLiterals(setup.maxLiteralsPerClause),
                generator.maxLiteralsPerCountingClause(setup.maxLiteralsPerCountingClause)
        );
        if (setup.naiveTautology) {
            filters.add(generator.naiveTautologyFilter());
        }
        if (setup.tautologyFilter) {
            filters.add(generator.tautologyFilter(null == setup.prover9Path ? null : Paths.get(setup.prover9Path), setup.maxProver9Seconds));
        }

        printComment("starting to generate clauses with filters: " + makeString(filters));
        List<Clause> allClauses = generator.generateClauses(filters, setup.maxLiteralsPerClause);
        Counters<Integer> clausesLengthHistogram = clausesToHistogram(allClauses);
        printComment("clauses generated within " + timeToNowInSeconds(startTime) + " overall " + allClauses.size() +
                " with distribution " + histogramToString(clausesLengthHistogram));

        if (setup.subsumption) {
            long startThetaReductionFilter = System.nanoTime();
            printComment("starting to do theta-reduction with " + allClauses.size() + " with distribution " + histogramToString(clausesLengthHistogram));
            SingleFilter<Clause> thetaSubsumptionFilter = generator.thetaSubsumptionFilter();
            allClauses = allClauses.stream().filter(thetaSubsumptionFilter).toList(); // TODO to parallel
            clausesLengthHistogram = clausesToHistogram(allClauses);
            printComment("theta-reduction done within " + timeToNowInSeconds(startThetaReductionFilter) + " resulting in " +
                    allClauses.size() + " with distribution " + histogramToString(clausesLengthHistogram));
        }

        allClauses = allClauses.stream().map(c -> ClausesCache.getInstance().get(c)).collect(Collectors.toList());
        return allClauses;
    }

    private List<SentenceState> connectToSizeParallel(int numberOfLiterals, MultiList<Integer, SentenceState> sentences,
                                                      MultiList<Integer, Clause> clausesByLength, List<JoiningFilter> connectionFilters,
                                                      SentenceState seed, ClausesGenerator clausesGenerator) {
        List<SentenceState> retVal = IntStream.range(1, numberOfLiterals).parallel()
                .boxed()
                .flatMap(startLength -> connect(sentences.get(startLength),
                        clausesByLength.get(numberOfLiterals - startLength),
                        connectionFilters))
                .collect(Collectors.toList());
        if (clausesByLength.containsKey(numberOfLiterals)) {
            if (null == seed) {
                Stream<Clause> clausesStream = clausesByLength.get(numberOfLiterals).stream();
                if (setup.languageBias) {
                    JoiningFilter languageBiasFilter = clausesGenerator.languageBias();
                    clausesStream = clausesStream.filter(clause -> languageBiasFilter.test(emptySentence, clause));
                }
                Stream<SentenceState> stream = clausesStream.map(clause -> new SentenceState(Sugar.list(clause), this.setup));
                if (setup.debug) {
                    JoiningFilter logging = clausesGenerator.creationLogging("CreationLogging2");
                    stream = stream.filter(sentence -> logging.test(sentence, null));
                }
                stream.forEach(retVal::add);
            } else {
                clausesByLength.get(numberOfLiterals).stream()
                        .filter(clause -> connectionFilters.stream().allMatch(filter -> filter.test(seed, clause)))
                        .forEach(clause -> retVal.add(seed.extend(clause)));
            }
        }
        return retVal;
    }

    private List<SentenceState> connectToSize(int numberOfLiterals, MultiList<
            Integer, SentenceState> sentences, MultiList<Integer, Clause> clausesByLength, List<JoiningFilter> connectionFilters) {
        List<SentenceState> retVal = Sugar.list();
        if (clausesByLength.containsKey(numberOfLiterals)) {
            clausesByLength.get(numberOfLiterals).stream()
                    .map(clause -> new SentenceState(Sugar.list(clause), this.setup))
                    .forEach(retVal::add);
        }
        for (int startLength = 1; startLength < numberOfLiterals; startLength++) {
            int secondLength = numberOfLiterals - startLength;
            retVal.addAll(connect(sentences.get(startLength), clausesByLength.get(secondLength), connectionFilters).toList());
        }
        return retVal;
    }

    private Stream<SentenceState> connect(List<SentenceState> sentences, List<Clause> clauses, List<JoiningFilter> connectionFilters) {
        if (sentences.isEmpty() || clauses.isEmpty()) {
            return Stream.empty();
        }
        return sentences.parallelStream()
                .flatMap(sentence -> clauses.stream()
                        .filter(clause -> connectionFilters.stream().allMatch(filter -> filter.test(sentence, clause)))
                        .map(sentence::extend)
                );
    }


    private boolean shouldEnd(long start) {
        return null != this.setup.timeLimit && this.setup.timeLimit > 0 && this.setup.timeLimit <= (System.nanoTime() - start) / 60_000_000_000L; // 1min = 60*10^9 milliseconds
    }

    private Long timeToNowInSeconds(long start) {
        return timeToSeconds(start, System.nanoTime());
    }

    private Long timeToSeconds(long start, long end) {
        return (end - start) / 1_000_000_000;
    }

    private String histogramToString(Counters<Integer> counter) {
        return counter.keySet().stream().sorted().map(key -> key + ":" + counter.get(key)).collect(Collectors.joining(", "));
    }

    private Counters<Integer> clausesToHistogram(List<Clause> clauses) {
        Counters<Integer> counter = new Counters<>();
        clauses.forEach(clause -> counter.increment(clause.countLiterals()));
        return counter;
    }

    private Counters<Integer> sentencesToHistogram(List<SentenceState> sentences) {
        Counters<Integer> counter = new Counters<>();
        sentences.forEach(sentence -> counter.increment(sentence.countLiterals()));
        return counter;
    }

    private String makeString(List<? extends Object> filters) {
        return filters.stream().map(Object::toString).collect(Collectors.joining(", "));
    }


    private void printComment(String message) {
        printMessage(message, true, System.out);
        if (this.setup.statesStoring) {
            printSerialization(message, true);
        }
    }

    private void printSerialization(String message, boolean isComment) {
        printMessage(message, isComment, System.err);
    }

    private void printMessage(String message, boolean isComment, PrintStream out) {
        if (isComment) {
            out.println("# " + message);
        } else {
            out.println(message);
        }
    }

}
