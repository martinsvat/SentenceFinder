package ida.cellGraphs;

import ida.hypergraphIsomorphism.VariableSupplier;
import ida.ilp.logic.*;
import ida.ilp.logic.special.IsoClauseWrapper;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.caches.LiteralsCache;
import ida.sentences.generators.ClausesGenerator;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.util.*;

public class IsomorphicFilter implements CellGraphFilter {

    private final MultiList<IsoClauseWrapper, Clause> multilist;
    private final Matching matching;
    private final String prefix;
    private final SentenceSetup setup;

    public IsomorphicFilter(SentenceSetup setup) {
        this.multilist = new MultiList<>();
        this.matching = new Matching();
        this.prefix = "IF" + setup.fastWFOMCVersion;
        this.setup = setup;
    }


    @Override
    public void incorporate(SentenceState sentence, String line) {
        Clause cellGraph = Clause.parse(line, ',', null);
        IsoClauseWrapper icw = IsoClauseWrapper.create(cellGraph);
        boolean found = false;
        for (Clause clause : multilist.get(icw)) {
            if (matching.isomorphism(clause, icw.getOriginalClause())) {
                found = true;
                break;
            }
        }
        if (!found) {
            multilist.put(icw, icw.getOriginalClause());
        }
        sentence.setCellGraph(cellGraph); // TOOO is this memory friendly????
    }

    @Override
    public Collection<List<Clause>> values() {
        return multilist.values();
    }

    @Override
    public String getPrefix() {
        return prefix;
    }

    @Override
    public void setUpRedisOutput(SentenceState sentence, String redisOutput) {
        sentence.setCellGraph(Clause.parse(redisOutput, ',', null));
    }

    @Override
    public void fillInCellGraphs(List<SentenceState> cellGraphQueue) {
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
                        setup.redisConnection.set(prefix + sentence.getUltraCannonic(), cellGraph.toString());
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

    @Override
    public void addHiddens(Collection<SentenceState> sentences) {
        for (SentenceState sentence : sentences) {
            boolean found = false;
            IsoClauseWrapper icw = IsoClauseWrapper.create(sentence.getCellGraph());
            for (Clause clause : multilist.get(icw)) {
                if (matching.isomorphism(clause, icw.getOriginalClause())) {
                    found = true;
//                if (setup.collectCellGraphs) { // this is just a dev tool
//                    this.cellGraphs.put(clause, sentence);
//                }
                    // TODO aha, a co kdyz je redundantni az pozdeji nalezena v searchi pomoci dalsich technik nez v predesle vrstve???
                    break;
                }
            }
            if (!found) {
                multilist.put(icw, icw.getOriginalClause());
//            if (setup.collectCellGraphs) { // this is just a dev tool
//                this.cellGraphs.put(sentence.getCellGraph(), sentence);
//            }
            }
        }
    }

    @Override
    public Collection<List<SentenceState>> add(List<SentenceState> sentences, Set<SentenceState> skip, ClausesGenerator clausesGenerator) {
        MultiList<Clause, SentenceState> parents = new MultiList<>(); // meaning cell graph in this layer minus the one hidden using skip-collection
        for (SentenceState sentence : sentences) {
            if (skip.contains(sentence)) {
                continue;
            }

            boolean found = false;
            IsoClauseWrapper icw = IsoClauseWrapper.create(sentence.getCellGraph());
            for (Clause clause : multilist.get(icw)) {
                if (matching.isomorphism(clause, icw.getOriginalClause())) {
//                    storeForDebug(sentence, clause);
                    if (parents.containsKey(clause)) {
                        parents.put(clause, sentence);
                    } else {
                        if (clausesGenerator.useLogger) {
                            clausesGenerator.log(sentence, null, "CellGraph-Inter");
//                            clausesGenerator.log(sentence, null, "CellGraph-Inter " + clause);
                        }
                        skip.add(sentence); // this sentence is cell-isomorphic to something with less literals
                    }
//                        if (setup.collectCellGraphs) { // this is just a dev tool
//                            this.cellGraphs.put(clause, sentence);
//                        }
                    found = true;
                    break;
                }
            }
            if (!found) {
                if (clausesGenerator.useLogger) {
                    clausesGenerator.log(sentence, null, "CGI unique ");
                    //                    clausesGenerator.log(sentence, null, "CGI unique " + icw.getOriginalClause());
                }

                multilist.put(icw, icw.getOriginalClause());
                parents.put(icw.getOriginalClause(), sentence);
//                if (setup.collectCellGraphs) { // this is just a dev tool
//                    this.cellGraphs.put(sentence.getCellGraph(), sentence);
            }
        }
        return parents.values();
    }

    private void printComment(String message) { // TODO shift this somewhere else, make it nicer!
        System.out.println("# " + message);
        System.err.println("# " + message);
    }

    private Clause parseCellGraph(List<SentenceState> cellGraphQueue, ProcessBuilder processBuilder, String line,
                                  int addedCellGraphs, String wholeLine) {
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

    private Term parseSymbolicWeightStateful(Term constant, VariableSupplier sumSupplier, VariableSupplier
            productSupplier,
                                             VariableSupplier
                                                     weightVariableSupplier, List<Literal> parseTree, Map<String, Term> expressionCache) {
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

                for (String expr : part.split("\\*")) { // 12*x^2*x2^3
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


    public static CellGraphFilter create(SentenceSetup setup) {
        return new IsomorphicFilter(setup);
    }
}
