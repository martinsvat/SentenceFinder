package ida.sentences;

import ida.ilp.logic.Predicate;
import ida.ilp.logic.PredicateFactory;
import ida.ilp.logic.Variable;
import ida.utils.Sugar;
import io.lettuce.core.RedisClient;
import io.lettuce.core.api.StatefulRedisConnection;
import io.lettuce.core.api.sync.RedisCommands;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

// just a wrapper for search's hyperparameters
public class SentenceSetup {

    public final Set<Variable> variablesSet;
    public final List<Variable> variables;
    public final int maxOverallLiterals;
    public final int maxClauses; // TODO there is no filter based on this
    public final int maxLiteralsPerClause;
    public final List<Predicate> predicates;

    public final boolean quantifiers;
    public final boolean languageBias;
    public final boolean isomorphicSentences;
    public final boolean negations;
    public final boolean permutingArguments;
    public final boolean lexicographicalMatching;
    public final boolean reflexiveAtoms;

    public final boolean naiveTautology;
    public final String prover9Path;
    public final int maxProver9Seconds;
    public final boolean tautologyFilter;
    public final boolean contradictionFilter;
    public final boolean trivialConstraints;
    public final boolean decomposableComponents;
    public final boolean subsumption;
    public final boolean quantifiersReducibility;

    public final int maxK;
    public final int maxCountingClauses;
    public final int maxLiteralsPerCountingClause;
    public final boolean doubleCountingExist;
    public final boolean countingContradictionFilter;

    public final long cellTimeLimit;
    public final int juliaThreads;
    public final boolean computeCellGraph;
    public final String cellGraph;

    public final String seed;
    public final Long timeLimit;
    public final Path errOut;
    public final boolean statesStoring;
    public final boolean debug;
    private final String redis;
    public final boolean collectCellGraphs = false; // dev & debug
    private StatefulRedisConnection<String, String> connection;
    private RedisClient redisClient;
    public RedisCommands<String, String> redisConnection;


    public SentenceSetup(int maxOverallLiterals, int maxClauses, int maxLiteralsPerClause, List<Predicate> predicates,
                         List<Variable> variables, boolean quantifiers, boolean statesStoring, String prover9Path,
                         boolean reflexiveAtoms, Path errOut, boolean permutingArguments, String cellGraph, boolean debug,
                         boolean trivialConstraints, int juliaThreads, boolean decomposableComponents, boolean naiveTautology,
                         boolean tautologyFilter, boolean contradictionFilter, boolean subsumption,
                         boolean quantifiersReducibility, int maxK, int maxCountingClauses, int maxLiteralsPerCountingClause,
                         boolean doubleCountingExist, boolean countingContradictionFilter, int maxProver9Seconds,
                         String seed, boolean negations, boolean isomorphicSentences, Long timeLimit, long cellTimeLimit,
                         String redis, boolean languageBias, boolean lexicographicalMatching) {
        this.maxOverallLiterals = maxOverallLiterals < 0 ? maxClauses * maxLiteralsPerClause : maxOverallLiterals;
        this.maxClauses = maxClauses;
        this.maxLiteralsPerClause = maxLiteralsPerClause;
        this.predicates = predicates;
        this.variables = variables;
        this.variablesSet = Sugar.setFromCollections(variables);
        this.quantifiers = quantifiers;
        this.languageBias = languageBias;
        this.statesStoring = statesStoring;
        this.prover9Path = null == prover9Path ? null : (Files.exists(Paths.get(prover9Path)) ? prover9Path : null);
        this.maxProver9Seconds = maxProver9Seconds;
        this.reflexiveAtoms = reflexiveAtoms;
        this.errOut = errOut;
        this.permutingArguments = permutingArguments;
        this.cellGraph = null == prover9Path ? null : (Files.exists(Paths.get(cellGraph)) ? cellGraph : null);
        this.debug = debug;
        this.trivialConstraints = trivialConstraints;
        this.juliaThreads = juliaThreads;
        this.decomposableComponents = decomposableComponents;
        this.naiveTautology = naiveTautology;
        this.tautologyFilter = tautologyFilter;
        this.contradictionFilter = contradictionFilter;
        this.subsumption = subsumption;
        this.quantifiersReducibility = quantifiersReducibility;
        this.maxK = maxK;
        this.maxCountingClauses = maxCountingClauses;
        this.maxLiteralsPerCountingClause = maxLiteralsPerCountingClause;
        this.doubleCountingExist = doubleCountingExist;

        seed = seed.trim();
        if (!seed.startsWith("[") && !seed.isBlank()) {
            seed = "[" + seed + "]";
        }
        this.seed = seed;
        this.negations = negations;
        this.isomorphicSentences = isomorphicSentences;
        this.lexicographicalMatching = lexicographicalMatching;

        this.computeCellGraph = null != this.cellGraph;
//        this.juliaSoVersion = null;
//        if (null != this.cellGraphPath && this.cellGraphPath.endsWith("_so.jl")) {
//            this.juliaSoVersion = Paths.get(Paths.get(this.cellGraphPath).getParent().toString(), "FWFOMC.so").toString();
//        }
        this.cellTimeLimit = cellTimeLimit;
        this.countingContradictionFilter = countingContradictionFilter && this.maxK > 0 && this.maxCountingClauses > 0 && this.maxLiteralsPerCountingClause > 0;
        this.timeLimit = timeLimit;

        this.redis = redis;
        if (null != redis && computeCellGraph) { // if Julia's cell-graph file is not provided, do not connect to Redis at all
            try {
                this.redisClient = RedisClient.create(redis);
                this.connection = redisClient.connect();
                this.redisConnection = connection.sync();
            } catch (Exception e) {
                System.out.println("# some troubles with redis: " + e.toString());
                closeRedis();
                this.redisClient = null;
                this.connection = null;
                this.redisConnection = null;
            }
        }
    }

    public SentenceSetup(int maxOverallLiterals, int maxClauses, int maxLiteralsPerClause, int unaryPredicates, int binaryPredicates, int numberOfVariables, boolean quantifiers, boolean statesStoring, String prover9Path, boolean reflexiveAtoms, boolean permutingArguments, String cellGraph, boolean debug, boolean trivialConstraints, int juliaThreads, boolean decomposableComponents, boolean naiveTautology, boolean tautologyFilter, boolean contradictionFilter, boolean subsumption, boolean quantifiersReducibility, int maxK, int maxCountingClauses, int maxLiteralsPerCountingClause, boolean doubleCountingExist, boolean countingContradictionFilter, int maxProver9Seconds, String seed, boolean negations, boolean isomorphicSentences, Long timeLimit, long cellTimeLimit, String redis, boolean languageBias, boolean lexicographicalMatching) {
        this(maxOverallLiterals, maxClauses, maxLiteralsPerClause, unaryPredicates, binaryPredicates, numberOfVariables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, null, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, redis, languageBias, lexicographicalMatching);
    }

    public SentenceSetup(int maxOverallLiterals, int maxClauses, int maxLiteralsPerClause, int unaryPredicates, int binaryPredicates, int numberOfVariables, boolean quantifiers, boolean statesStoring, String prover9Path, boolean reflexiveAtoms, Path errOut, boolean permutingArguments, String cellGraph, boolean debug, boolean trivialConstraints, int juliaThreads, boolean decomposableComponents, boolean naiveTautology, boolean tautologyFilter, boolean contradictionFilter, boolean subsumption, boolean quantifiersReducibility, int maxK, int maxCountingClauses, int maxLiteralsPerCountingClause, boolean doubleCountingExist, boolean countingContradictionFilter, int maxProver9Seconds, String seed, boolean negations, boolean isomorphicSentences, Long timeLimit, long cellTimeLimit, String redis, boolean languageBias, boolean lexicographicalMatching) {
        this(maxOverallLiterals,
                maxClauses,
                maxLiteralsPerClause,
                Sugar.listFromCollections(
                        IntStream.range(0, unaryPredicates).mapToObj(i -> PredicateFactory.getInstance().create("U" + i, 1)).collect(Collectors.toList()),
                        IntStream.range(0, binaryPredicates).mapToObj(i -> PredicateFactory.getInstance().create("B" + i, 2)).collect(Collectors.toList())
                ),
                2 == numberOfVariables ? Sugar.list(Variable.construct("x"), Variable.construct("y")) : IntStream.range(0, numberOfVariables).mapToObj(i -> Variable.construct("x" + i)).collect(Collectors.toList()),
                quantifiers,
                statesStoring,
                prover9Path,
                reflexiveAtoms,
                errOut,
                permutingArguments,
                cellGraph,
                debug,
                trivialConstraints,
                juliaThreads,
                decomposableComponents,
                naiveTautology,
                tautologyFilter,
                contradictionFilter,
                subsumption,
                quantifiersReducibility,
                maxK,
                maxCountingClauses,
                maxLiteralsPerCountingClause,
                doubleCountingExist,
                countingContradictionFilter,
                maxProver9Seconds,
                seed,
                negations,
                isomorphicSentences,
                timeLimit,
                cellTimeLimit,
                redis,
                languageBias,
                lexicographicalMatching
        );
    }

    public SentenceSetup(int variables) {
        this(0, 0, 0, 0, 0, variables, false, false, "", false, null, false, "", false, false, 1, false, false, false, false, false, false, 0, 0, 0, false, false, 0, "", false, false, 0L, 0l, "", false, false);
    }

    public SentenceSetup setPredicates(List<Predicate> predicates) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, "", languageBias, false);
    }

    public SentenceSetup setK(int k) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, k, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, "", languageBias, false);
    }

    public SentenceSetup setDoubleExists(boolean doubleExists) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleExists, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, "", languageBias, false);
    }

    public SentenceSetup setIso(boolean isoPredicateNames, boolean isoSings, boolean symmetryFlip) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, symmetryFlip, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, isoSings, isoPredicateNames, timeLimit, cellTimeLimit, "", languageBias, false);
    }


    public SentenceSetup setQuantifiers(boolean quantifiers) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, "", languageBias, false);
    }

    public SentenceSetup setMaxCountingClauses(int maxCountingClauses) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, "", languageBias, false);
    }

    public SentenceSetup setMaxLiteralsPerCountingClause(int maxLiteralsPerCountingClause) {
        return new SentenceSetup(maxOverallLiterals, maxClauses, maxLiteralsPerClause, predicates, variables, quantifiers, statesStoring, prover9Path, reflexiveAtoms, errOut, permutingArguments, cellGraph, debug, trivialConstraints, juliaThreads, decomposableComponents, naiveTautology, tautologyFilter, contradictionFilter, subsumption, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, negations, isomorphicSentences, timeLimit, cellTimeLimit, "", languageBias, false);
    }

    public boolean continueWithSearch() {
        return null != errOut;
    }

    public static SentenceSetup createFromCmd() {
        Path errOut = Paths.get(System.getProperty("ida.sentenceSetup.loadErrOut", "null"));
        if (Files.exists(errOut)) {
            return createFromStoredState(errOut);
        }
        return createFromCmdValues();
    }

    private static SentenceSetup createFromCmdValues() {
        // general syntax-related parameters
        // FO2
        int maxOverallLiterals = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxOverallLiterals", "-1"));
        int maxClauses = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxClauses", "3"));
        int maxLiteralsPerClause = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxLiteralsPerClause", "3"));
        int unaryPredicates = Integer.parseInt(System.getProperty("ida.sentenceSetup.unaryPredicates", "1"));
        int binaryPredicates = Integer.parseInt(System.getProperty("ida.sentenceSetup.binaryPredicates", "1"));
        int numberOfVariables = Integer.parseInt(System.getProperty("ida.sentenceSetup.numberOfVariables", "2"));
        boolean quantifiers = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.quantifiers", "true"));

        // C2
        int maxK = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxK", "1"));
        int maxCountingClauses = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxCountingClauses", "1"));
        int maxLiteralsPerCountingClause = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxLiteralsPerCountingClause", "1"));
        boolean doubleCountingExist = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.doubleCountingExist", "false"));

        // pruning hacks
        boolean decomposableComponents = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.decomposableComponents", "true"));
        boolean isomorphicSentences = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.isomorphicSentences", "true"));
        boolean negations = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.negations", "true"));
        boolean lexicographicalMatching = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.lexicographicalMatching", "true"));
        boolean permutingArguments = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.permutingArguments", "true"));
        boolean subsumption = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.subsumption", "true"));
        boolean trivialConstraints = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.trivialConstraints", "true"));
        boolean quantifiersReducibility = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.quantifiersReducibility", "true"));
        boolean languageBias = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.languageBias", "true"));

        // proving related
        boolean naiveTautology = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.naiveTautology", "true"));
        boolean tautologyFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.tautologyFilter", "true"));
        boolean contradictionFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.contradictionFilter", "true"));
        String prover9Path = System.getProperty("ida.sentenceSetup.prover9Path", Paths.get("D:\\Program Files (x86)\\Prover9-Mace4\\bin-win32\\prover9.exe").toString());
        int maxProver9Seconds = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxProver9Seconds", "30"));
        boolean countingContradictionFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.countingContradictionFilter", "false"));

        // hiding hacks
        boolean reflexiveAtoms = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.reflexiveAtoms", "true"));


        // Julia (cell-graph) setup
        int juliaThreads = Integer.parseInt(System.getProperty("ida.sentenceSetup.juliaThreads", "1"));
        long cellTimeLimit = Long.parseLong(System.getProperty("ida.sentenceSetup.cellTimeLimit", "3600"));
//        String cellGraphPath = System.getProperty("ida.sentenceSetup.cellGraph", Paths.get("C:\\data\\school\\development\\sequence-db\\FastWFOMC.jl\\snippets\\sampleInstall.jl").toString());
//        String cellGraphPath = System.getProperty("ida.sentenceSetup.cellGraph", Paths.get("C:\\data\\school\\development\\sequence-db\\JuLiA\\fluffy2\\sample_so.jl").toString());
        String cellGraphPath = System.getProperty("ida.sentenceSetup.cellGraph", Paths.get("C:\\data\\school\\development\\sequence-db\\fluffy-broccoli\\SFinder\\julia\\sample_multithreaded_unskolemized.jl").toString());
//        String cellGraphPath = System.getProperty("ida.sentenceSetup.cellGraph", Paths.get("dev_null").toString());
        String redisParams = System.getProperty("ida.sentenceSetup.redis", "redis://mypass@127.0.0.1:6379/");


        String seed = System.getProperty("ida.sentenceSetup.seed", "");

        // general SFinder parameters
        String limit = System.getProperty("ida.sentenceSetup.timeLimit", "null");
        Long timeLimit = "null".equals(limit) ? null : Long.parseLong(limit);
        boolean statesStoring = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.statesStoring", "false"));
        boolean debug = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.debug", "false"));
//        boolean debug = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.debug", "true"));


        return new SentenceSetup(maxOverallLiterals,
                maxClauses,
                maxLiteralsPerClause,
                unaryPredicates,
                binaryPredicates,
                numberOfVariables,
                quantifiers,
                statesStoring,
                prover9Path,
                reflexiveAtoms,
                permutingArguments,
                cellGraphPath,
                debug,
                trivialConstraints,
                juliaThreads,
                decomposableComponents,
                naiveTautology,
                tautologyFilter,
                contradictionFilter,
                subsumption,
                quantifiersReducibility,
                maxK,
                maxCountingClauses,
                maxLiteralsPerCountingClause,
                doubleCountingExist,
                countingContradictionFilter,
                maxProver9Seconds,
                seed,
                negations,
                isomorphicSentences,
                timeLimit,
                cellTimeLimit,
                redisParams,
                languageBias,
                lexicographicalMatching
        );
    }

    private static SentenceSetup createFromStoredState(Path errOut) {
        try {
            List<String> setupLines = Files.lines(errOut).filter(line -> line.startsWith("# starting search with setup:")).toList();
            if (setupLines.isEmpty()) {
                throw new IllegalStateException("There is no setup line in the file!");
            }
            String line = setupLines.get(setupLines.size() - 1);
            System.out.println("# taking setup line\t" + line);

            Map<String, String> values = stringToValues(line);

            int unaryPredicates = values.get("predicates").split("/1").length - 1;
            int binaryPredicates = values.get("predicates").split("/2").length - 1;
            int variablesCount = values.get("variables").substring(1, values.get("variables").length() - 1).split(";").length;
            return new SentenceSetup(Integer.parseInt(values.get("maxOverallLiterals")),
                    Integer.parseInt(values.get("maxClauses")),
                    Integer.parseInt(values.get("maxLiteralsPerClause")),
                    unaryPredicates,
                    binaryPredicates,
                    variablesCount,
                    "true".equalsIgnoreCase(values.get("quantifiers")),
                    "true".equalsIgnoreCase(values.get("statesStoring")),
                    values.get("prover9Path"),
                    "true".equalsIgnoreCase(values.get("reflexiveAtoms")),
                    errOut,
                    "true".equalsIgnoreCase(values.get("permutingArguments")),
                    values.get("cellGraph"),
                    "true".equalsIgnoreCase(values.get("debug")),
                    "true".equalsIgnoreCase(values.get("trivialConstraints")),
                    Integer.parseInt(values.get("juliaThreads")),
                    "true".equalsIgnoreCase(values.get("decomposableComponents")),
                    "true".equalsIgnoreCase(values.get("naiveTautology")),
                    "true".equalsIgnoreCase(values.get("tautologyFilter")),
                    "true".equalsIgnoreCase(values.get("contradictionFilter")),
                    "true".equalsIgnoreCase(values.get("subsumption")),
                    "true".equalsIgnoreCase(values.get("quantifiersReducibility")),
                    Integer.parseInt(values.get("maxK")),
                    Integer.parseInt(values.get("maxCountingClauses")),
                    Integer.parseInt(values.get("maxLiteralsPerCountingClause")),
                    "true".equalsIgnoreCase(values.get("doubleCountingExist")),
                    "true".equalsIgnoreCase(values.get("countingContradictionFilter")),
                    Integer.parseInt(values.get("maxProver9Seconds")),
                    values.get("seed"),
                    "true".equalsIgnoreCase(values.get("negations")),
                    "true".equalsIgnoreCase(values.get("isomorphicSentences")),
                    "null".equals(values.get("timeLimit")) ? null : Long.parseLong(values.get("timeLimit")),
                    Long.parseLong(values.get("cellTimeLimit")),
                    values.get("redis"),
                    "true".equalsIgnoreCase(values.get("languageBias")),
                    "true".equalsIgnoreCase(values.get("lexicographicalMatching"))
            );
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static Map<String, String> stringToValues(String line) {
        if (!line.contains("{") || !line.contains("}")) {
            throw new IllegalStateException("Cannot parse line:\t" + line);
        }
        line = line.substring(line.indexOf('{') + 1, line.lastIndexOf('}'));

        Map<Character, Character> pair = new HashMap<>();
        pair.put('\'', '\'');
        pair.put('"', '"');
        pair.put('(', null);
        pair.put('{', null);
        pair.put('[', null);
        pair.put(')', '(');
        pair.put('}', '{');
        pair.put(']', '[');

        int lastCut = 0;
        Stack<Character> stack = new Stack<>();
        HashMap<String, String> result = new HashMap<>();
        for (int index = 0; index < line.length(); index++) {
            char element = line.charAt(index);
            if (pair.containsKey(element)) {
                Character startPoint = pair.get(element);
                if (stack.empty() || null == startPoint || stack.peek() != startPoint) {
                    stack.push(element);
                } else {
                    if (stack.peek() == startPoint) {
                        stack.pop();
                    } else {
                        throw new IllegalStateException();
                    }
                }
            }

            if ((element == ',' && stack.isEmpty()) || index == line.length() - 1) {
                String[] keyVal = line.substring(lastCut, index).split("=", 2);
                if (keyVal.length != 2) {
                    throw new IllegalStateException();
                }
                result.put(keyVal[0].trim(), keyVal[1]);
                lastCut = index + 1;
            }
        }
        return result;
    }

    @Override
    public String toString() {
        return "SentenceSetup{" +
                "maxOverallLiterals=" + maxOverallLiterals +
                ", maxClauses=" + maxClauses +
                ", maxLiteralsPerClause=" + maxLiteralsPerClause +
                ", predicates=" + "[" + predicates.stream().map(Object::toString).collect(Collectors.joining("; ")) + "]" +
                ", variables=" + "[" + variables.stream().map(Object::toString).collect(Collectors.joining("; ")) + "]" +
                ", statesStoring=" + statesStoring +
                ", quantifiers=" + quantifiers +
                ", reflexiveAtoms=" + reflexiveAtoms +
                ", prover9Path=" + prover9Path +
                ", errOut=" + errOut +
                ", permutingArguments=" + permutingArguments +
                ", cellGraph=" + cellGraph +
                ", debug=" + debug +
                ", trivialConstraints=" + trivialConstraints +
                ", juliaThreads=" + juliaThreads +
                ", decomposableComponents=" + decomposableComponents +
                ", naiveTautology=" + naiveTautology +
                ", tautologyFilter=" + tautologyFilter +
                ", contradictionFilter=" + contradictionFilter +
                ", subsumption=" + subsumption +
                ", quantifiersReducibility=" + quantifiersReducibility +
                ", maxK=" + maxK +
                ", maxCountingClauses=" + maxCountingClauses +
                ", maxLiteralsPerCountingClause=" + maxLiteralsPerCountingClause +
                ", doubleCountingExist=" + doubleCountingExist +
                ", countingContradictionFilter=" + countingContradictionFilter +
                ", maxProver9Seconds=" + maxProver9Seconds +
                ", seed=" + seed +
                ", negations=" + negations +
                ", isomorphicSentences=" + isomorphicSentences +
                ", timeLimit=" + timeLimit +
                ", cellTimeLimit=" + cellTimeLimit +
                ", redis=" + redis +
                ", forkPollSize=" + System.getProperty("java.util.concurrent.ForkJoinPool.common.parallelism", "0") +
                ", languageBias=" + languageBias +
                ", lexicographicalMatching=" + lexicographicalMatching +
                '}';
    }

    public void closeRedis() {
        if (null != connection) {
            connection.close();
        }
        if (null != redisClient) {
            redisClient.shutdown();
        }
    }
}
