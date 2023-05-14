package search.sentences;

import search.ilp.logic.PredicateFactory;
import search.ilp.logic.Predicate;
import search.ilp.logic.Variable;
import search.utils.Sugar;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

// just a wrapper for search's hyperparameters
public class SentenceSetup {


    public final int maxLayers;
    public final int maxClauses;
    public final int maxLiteralsPerClause;
    public final List<Predicate> predicates;
    public final List<Variable> variables;
    public final Set<Variable> variablesSet;
    public final boolean statesStoring;
    public final boolean quantifiers;
    public final boolean identityFilter;
    public final String prover9Path;
    public final int maxProver9Seconds;
    public final Path errOut;
    public final boolean symmetryFlip;
    public final String cellGraphPath;
    public final int juliaThreads;
    public final boolean debug;
    public final boolean computeCellGraph;
    public final boolean naiveTautology;
    public final boolean tautologyFilter;
    public final boolean contradictionFilter;
    public final boolean cliffhangerFilter;
    public final boolean connectedComponents;
    public final boolean thetaReducibility;
    public final boolean quantifiersReducibility;
    public final int maxK;
    public final int maxCountingClauses;
    public final int maxLiteralsPerCountingClause;
    public final boolean doubleCountingExist;
    public final boolean countingContradictionFilter;
    public final String seed;
    public final boolean languageBias;
    public final boolean isoSings;
    public final boolean isoPredicateNames;
    public final boolean lexicographicalComparatorOnly;
    public final Long timeLimit;
    public final boolean fixedSeed;
    public final long cellTimeLimit;
    public String juliaSoVersion;

    public SentenceSetup(int maxLayers, int maxClauses, int maxLiteralsPerClause, List<Predicate> predicates,
                         List<Variable> variables, boolean quantifiers, boolean statesStoring, String prover9Path,
                         boolean identityFilter, Path errOut, boolean symmetryFlip, String cellGraphPath, boolean debug,
                         boolean cliffhangerFilter, int juliaThreads, boolean connectedComponents, boolean naiveTautology,
                         boolean tautologyFilter, boolean contradictionFilter, boolean thetaReducibility,
                         boolean quantifiersReducibility, int maxK, int maxCountingClauses, int maxLiteralsPerCountingClause,
                         boolean doubleCountingExist, boolean countingContradictionFilter, int maxProver9Seconds,
                         String seed, boolean languageBias, boolean isoSings, boolean isoPredicateNames, boolean lexicographicalComparatorOnly,
                         Long timeLimit, boolean fixedSeed, long cellTimeLimit) {
        this.maxLayers = maxLayers;
        this.maxClauses = maxClauses;
        this.maxLiteralsPerClause = maxLiteralsPerClause;
        this.predicates = predicates;
        this.variables = variables;
        this.variablesSet = Sugar.setFromCollections(variables);
        this.quantifiers = quantifiers;
        this.statesStoring = statesStoring;
        this.prover9Path = (null != prover9Path && Files.exists(Paths.get(prover9Path))) ? prover9Path : null;
        this.maxProver9Seconds = maxProver9Seconds;
        this.identityFilter = identityFilter;
        this.errOut = errOut;
        this.symmetryFlip = symmetryFlip;
        this.cellGraphPath = (null != cellGraphPath && Files.exists(Paths.get(cellGraphPath))) ? cellGraphPath : null;
        this.debug = debug;
        this.cliffhangerFilter = cliffhangerFilter;
        this.juliaThreads = juliaThreads;
        this.connectedComponents = connectedComponents;
        this.naiveTautology = naiveTautology;
        this.tautologyFilter = tautologyFilter;
        this.contradictionFilter = contradictionFilter;
        this.thetaReducibility = thetaReducibility;
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
        this.fixedSeed = fixedSeed;
        this.languageBias = languageBias;
        this.isoSings = isoSings;
        this.isoPredicateNames = isoPredicateNames;
        this.lexicographicalComparatorOnly = lexicographicalComparatorOnly;

        if (lexicographicalComparatorOnly && (isoSings || isoPredicateNames)) {
            throw new IllegalStateException("lexicographicalComparatorOnly cannot be turned on when isoSings or isoPredicateNames are");
        }

        this.computeCellGraph = null != this.cellGraphPath;
        this.juliaSoVersion = null;
        if (null != this.cellGraphPath && this.cellGraphPath.endsWith("_so.jl")) {
            this.juliaSoVersion = Paths.get(Paths.get(this.cellGraphPath).getParent().toString(), "FWFOMC.so").toString();
        }
        this.cellTimeLimit = cellTimeLimit;
        this.countingContradictionFilter = countingContradictionFilter && this.maxK > 0 && this.maxCountingClauses > 0 && this.maxLiteralsPerCountingClause > 0;
        this.timeLimit = timeLimit;
    }

    public SentenceSetup(int maxLayers, int maxClauses, int maxLiteralsPerClause, int unaryPredicates, int binaryPredicates, int numberOfVariables, boolean quantifiers, boolean statesStoring, String prover9Path, boolean identityFilter, boolean symmetryFlip, String cellGraphPath, boolean debug, boolean cliffhangerFilter, int juliaThreads, boolean connectedComponents, boolean naiveTautology, boolean tautologyFilter, boolean contradictionFilter, boolean thetaReducibility, boolean quantifiersReducibility, int maxK, int maxCountingClauses, int maxLiteralsPerCountingClause, boolean doubleCountingExist, boolean countingContradictionFilter, int maxProver9Seconds, String seed, boolean languageBias, boolean isoSings, boolean isoPredicateNames, boolean lexicographicalComparatorOnly, Long timeLimit, boolean fixedSeed, long cellTimeLimit) {
        this(maxLayers, maxClauses, maxLiteralsPerClause, unaryPredicates, binaryPredicates, numberOfVariables, quantifiers, statesStoring, prover9Path, identityFilter, null, symmetryFlip, cellGraphPath, debug, cliffhangerFilter, juliaThreads, connectedComponents, naiveTautology, tautologyFilter, contradictionFilter, thetaReducibility, quantifiersReducibility, maxK, maxCountingClauses, maxLiteralsPerCountingClause, doubleCountingExist, countingContradictionFilter, maxProver9Seconds, seed, languageBias, isoSings, isoPredicateNames, lexicographicalComparatorOnly, timeLimit, fixedSeed, cellTimeLimit);
    }

    public SentenceSetup(int maxLayers, int maxClauses, int maxLiteralsPerClause, int unaryPredicates, int binaryPredicates, int numberOfVariables, boolean quantifiers, boolean statesStoring, String prover9Path, boolean identityFilter, Path errOut, boolean symmetryFlip, String cellGraphPath, boolean debug, boolean cliffhangerFilterManStanding, int juliaThreads, boolean connectedComponents, boolean naiveTautology, boolean tautologyFilter, boolean contradictionFilter, boolean thetaReducibility, boolean quantifiersReducibility, int maxK, int maxCountingClauses, int maxLiteralsPerCountingClause, boolean doubleCountingExist, boolean countingContradictionFilter, int maxProver9Seconds, String seed, boolean languageBias, boolean isoSings, boolean isoPredicateNames, boolean lexicographicalComparatorOnly, Long timeLimit, boolean fixedSeed, long cellTimeLimit) {
        this(maxLayers,
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
                identityFilter,
                errOut,
                symmetryFlip,
                cellGraphPath,
                debug,
                cliffhangerFilterManStanding,
                juliaThreads,
                connectedComponents,
                naiveTautology,
                tautologyFilter,
                contradictionFilter,
                thetaReducibility,
                quantifiersReducibility,
                maxK,
                maxCountingClauses,
                maxLiteralsPerCountingClause,
                doubleCountingExist,
                countingContradictionFilter,
                maxProver9Seconds,
                seed,
                languageBias,
                isoSings,
                isoPredicateNames,
                lexicographicalComparatorOnly,
                timeLimit,
                fixedSeed,
                cellTimeLimit
        );
    }

    public boolean continueWithSearch() {
        return null != errOut;
    }

    public static SentenceSetup create() {
        return new SentenceSetup(
                4,
                4,
                4,
                2,
                2,
                2,
                true,
                false,
                null,
                true,
                true,
                null,
                false,
                true,
                1,
                true,
                true,
                true,
                true,
                true,
                true,
                1,
                1,
                1,
                false,
                true,
                30,
                "",
                true,
                true,
                true,
                false,
                null,
                false,
                60 * 60l);
    }

    public static SentenceSetup createFromCmd() {
        Path errOut = Paths.get(System.getProperty("ida.sentenceSetup.loadErrOut", "null"));
        if (Files.exists(errOut)) {
            return createFromStoredState(errOut);
        }
        return createFromCmdValues();
    }

    public static SentenceSetup createFromCmdValues() {
        // general syntax-related parameters
        int maxLayers = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxLayers", "1000000000"));
        int maxClauses = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxClauses", "3"));
        int maxLiteralsPerClause = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxLiteralsPerClause", "4"));
        int unaryPredicates = Integer.parseInt(System.getProperty("ida.sentenceSetup.unaryPredicates", "1"));
        int binaryPredicates = Integer.parseInt(System.getProperty("ida.sentenceSetup.binaryPredicates", "1"));
        int numberOfVariables = Integer.parseInt(System.getProperty("ida.sentenceSetup.numberOfVariables", "2"));
        boolean quantifiers = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.quantifiers", "true"));

        int maxK = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxK", "1"));
        int maxCountingClauses = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxCountingClauses", "1"));
        int maxLiteralsPerCountingClause = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxLiteralsPerCountingClause", "1"));
        boolean doubleCountingExist = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.doubleCountingExist", "false"));

        // Julia (cell-graph) setup
        int juliaThreads = Integer.parseInt(System.getProperty("ida.sentenceSetup.juliaThreads", "1"));
        String cellGraphPath = System.getProperty("ida.sentenceSetup.cellGraph", null);
//        long cellTimeLimit = Long.parseLong(System.getProperty("ida.sentenceSetup.cellTimeLimit", "3600"));
        long cellTimeLimit = -1l;

        // pruning hacks
        boolean symmetryFlip = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.symmetryFlip", "true"));
        boolean connectedComponents = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.connectedComponents", "true"));

        String prover9Path = System.getProperty("ida.sentenceSetup.prover9Path", null);
        int maxProver9Seconds = Integer.parseInt(System.getProperty("ida.sentenceSetup.maxProver9Seconds", "30"));
        boolean contradictionFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.contradictionFilter", "true"));
        boolean naiveTautology = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.naiveTautology", "true"));
        boolean tautologyFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.tautologyFilter", "true"));
        boolean countingContradictionFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.countingContradictionFilter", "true"));

        // reducibility hacks
        boolean identityFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.identityFilter", "true"));
        boolean cliffhangerFilter = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.cliffhangerFilter", "true"));
        boolean thetaReducibility = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.thetaReducibility", "true"));
//        boolean quantifiersReducibility = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.quantifiersReducibility", "true"));
        boolean quantifiersReducibility = thetaReducibility;

        // general SFinder parameters
        boolean statesStoring = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.storeStates", "false"));
        boolean debug = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.debug", "false"));

        String seed = System.getProperty("ida.sentenceSetup.seed", "");
        boolean fixedSeed = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.fixedSeed", "true"));
        boolean languageBias = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.languageBias", "true"));
        boolean isoSings = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.isoSings", "true"));
        boolean isoPredicateNames = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.isoPredicateNames", "true"));
        boolean lexicographicalComparatorOnly = "true".equalsIgnoreCase(System.getProperty("ida.sentenceSetup.lexicographicalComparatorOnly", "false"));

        String limit = System.getProperty("ida.sentenceSetup.timeLimit", "null");
        Long timeLimit = "null".equals(limit) ? null : Long.parseLong(limit);

        return new SentenceSetup(maxLayers,
                maxClauses,
                maxLiteralsPerClause,
                unaryPredicates,
                binaryPredicates,
                numberOfVariables,
                quantifiers,
                statesStoring,
                prover9Path,
                identityFilter,
                symmetryFlip,
                cellGraphPath,
                debug,
                cliffhangerFilter,
                juliaThreads,
                connectedComponents,
                naiveTautology,
                tautologyFilter,
                contradictionFilter,
                thetaReducibility,
                quantifiersReducibility,
                maxK,
                maxCountingClauses,
                maxLiteralsPerCountingClause,
                doubleCountingExist,
                countingContradictionFilter,
                maxProver9Seconds,
                seed,
                languageBias,
                isoSings,
                isoPredicateNames,
                lexicographicalComparatorOnly,
                timeLimit,
                fixedSeed,
                cellTimeLimit
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
            return new SentenceSetup(Integer.parseInt(values.get("maxLayers")),
                    Integer.parseInt(values.get("maxClauses")),
                    Integer.parseInt(values.get("maxLiteralsPerClause")),
                    unaryPredicates,
                    binaryPredicates,
                    variablesCount,
                    "true".equalsIgnoreCase(values.get("quantifiers")),
                    "true".equalsIgnoreCase(values.get("statesStoring")),
                    values.get("prover9Path"),
                    "true".equalsIgnoreCase(values.get("identityFilter")),
                    errOut,
                    "true".equalsIgnoreCase(values.get("symmetryFlip")),
                    values.get("cellGraphPath"),
                    "true".equalsIgnoreCase(values.get("debug")),
                    "true".equalsIgnoreCase(values.get("cliffhangerFilter")),
                    Integer.parseInt(values.get("juliaThreads")),
                    "true".equalsIgnoreCase(values.get("connectedComponents")),
                    "true".equalsIgnoreCase(values.get("naiveTautology")),
                    "true".equalsIgnoreCase(values.get("tautologyFilter")),
                    "true".equalsIgnoreCase(values.get("contradictionFilter")),
                    "true".equalsIgnoreCase(values.get("thetaReducibility")),
                    "true".equalsIgnoreCase(values.get("quantifiersReducibility")),
                    Integer.parseInt(values.get("maxK")),
                    Integer.parseInt(values.get("maxCountingClauses")),
                    Integer.parseInt(values.get("maxLiteralsPerCountingClause")),
                    "true".equalsIgnoreCase(values.get("doubleCountingExist")),
                    "true".equalsIgnoreCase(values.get("countingContradictionFilter")),
                    Integer.parseInt(values.get("maxProver9Seconds")),
                    values.get("seed"),
                    "true".equalsIgnoreCase(values.get("languageBias")),
                    "true".equalsIgnoreCase(values.get("isoSings")),
                    "true".equalsIgnoreCase(values.get("isoPredicateNames")),
                    "true".equalsIgnoreCase(values.get("lexicographicalComparatorOnly")),
                    "null".equals(values.get("timeLimit")) ? null : Long.parseLong(values.get("timeLimit")),
                    "true".equalsIgnoreCase(values.get("fixedSeed")),
                    Long.parseLong(values.get("cellTimeLimit"))
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
                "maxLayers=" + maxLayers +
                ", maxClauses=" + maxClauses +
                ", maxLiteralsPerClause=" + maxLiteralsPerClause +
                ", predicates=" + "[" + predicates.stream().map(Object::toString).collect(Collectors.joining("; ")) + "]" +
                ", variables=" + "[" + variables.stream().map(Object::toString).collect(Collectors.joining("; ")) + "]" +
                ", statesStoring=" + statesStoring +
                ", quantifiers=" + quantifiers +
                ", identityFilter=" + identityFilter +
                ", prover9Path=" + prover9Path +
//                ", errOut=" + errOut +
                ", symmetryFlip=" + symmetryFlip +
                ", cellGraphPath=" + cellGraphPath +
                ", debug=" + debug +
                ", cliffhangerFilter=" + cliffhangerFilter +
                ", juliaThreads=" + juliaThreads +
                ", connectedComponents=" + connectedComponents +
                ", naiveTautology=" + naiveTautology +
                ", tautologyFilter=" + tautologyFilter +
                ", contradictionFilter=" + contradictionFilter +
                ", thetaReducibility=" + thetaReducibility +
//                ", quantifiersReducibility=" + quantifiersReducibility +
                ", maxK=" + maxK +
                ", maxCountingClauses=" + maxCountingClauses +
                ", maxLiteralsPerCountingClause=" + maxLiteralsPerCountingClause +
                ", doubleCountingExist=" + doubleCountingExist +
//                ", countingContradictionFilter=" + countingContradictionFilter +
                ", maxProver9Seconds=" + maxProver9Seconds +
//                ", seed=" + seed +
                ", languageBias=" + languageBias +
                ", isoSings=" + isoSings +
                ", isoPredicateNames=" + isoPredicateNames +
//                ", lexicographicalComparatorOnly=" + lexicographicalComparatorOnly +
                ", timeLimit=" + timeLimit +
//                ", fixedSeed=" + fixedSeed +
//                ", cellTimeLimit=" + cellTimeLimit +
                '}';
    }
}
