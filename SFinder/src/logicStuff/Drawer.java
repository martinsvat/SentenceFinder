package logicStuff;

import search.ilp.logic.Clause;
import search.ilp.logic.Constant;
import search.ilp.logic.Literal;
import search.ilp.logic.Term;
import search.ilp.logic.subsumption.Matching;
import search.utils.Sugar;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;


public class Drawer {


    /**
     * Should draw shorther-to-longer hypotheses search space given the clauses, but is probably hardcoded for one specific case.
     * @param clauses
     * @return
     */
    private String drawDot(List<Clause> clauses) {
        StringBuilder sb = new StringBuilder();

        Map<Clause, String> mapping = new HashMap<>();

        String nodes = String.join("\n",
                clauses.stream().sequential()
                        .map(clause -> {
                            String label = "n" + mapping.keySet().size();
                            mapping.put(clause, label);
                            return label + " [texlbl=\"$" + clause.toString().replaceAll("\\),", ") \\\\vee ")
                                    .replaceAll("!", "\\\\lnot ")
                                    .replaceAll("#EmptyClause", "\\\\{\\\\}")
                                    + "$\"];";
                        }).collect(Collectors.toList()));

        Matching matching = new Matching();
        matching.setSubsumptionMode(Matching.THETA_SUBSUMPTION);
        String dependencies = String.join("\n",
                clauses.stream().
                        flatMap(clause ->
                                Sugar.collectionDifference(clauses, clause).stream()
                                        .filter(longer -> longer.countLiterals() == clause.countLiterals() + 1)
                                        //.filter(longer -> matching.subsumption(clause, longer))
                                        .filter(longer -> matching.subsumption(clause, longer))
                                        .map(longer -> mapping.get(clause) + " -> " + mapping.get(longer) + ";")
                        ).collect(Collectors.toList()));

        sb.append("digraph G  {\n");
        sb.append(nodes);
        sb.append("\n");
        sb.append(dependencies);
        sb.append("\n}");
        return sb.toString();
    }


    public static void main(String[] args) throws IOException {
        Drawer drawer = Drawer.create();
        //drawer.drawEquivalenceClassDiagram();
        drawer.rulesToDot(Sugar.path("..", "..", "experiments", "usclEms100sampledMol7", "hornrules.txt"),
                Sugar.path("..", "..", "experiments", "usclEms100sampledMol7", "dots"));
    }

    private void rulesToDot(String inputFilePath, String outputFolderPath) throws IOException {
        List<Clause> clauses = Files.lines(Paths.get(inputFilePath)).filter(line -> line.trim().length() > 0).map(Clause::parse).collect(Collectors.toList());
        if(clauses.stream().filter(clause -> clause.literals().stream().mapToInt(Literal::arity).max().orElse(0) > 2).count() > 0){
            throw new IllegalStateException("only literals with at most arity two are supported");
        }
        try {
            new File(outputFolderPath).mkdirs();
        } catch (Exception e) {

        }
        clauses.stream().filter(clause -> clause.literals().stream().mapToInt(Literal::arity).max().orElse(0) < 3).forEach(clause -> {
            try {
                Files.write(Paths.get(Sugar.path(outputFolderPath, clause.toString() + ".dot")), clauseToDot(clause).getBytes());
            } catch (IOException e) {
                e.printStackTrace();
            }
        });

    }

    private String clauseToDot(Clause clause) {
        // little bit of simplification, it handles only function free logic and at most binary predicates
        Map<Term, String> terms = new HashMap<>();
        clause.variables().forEach(variable -> terms.put(variable, variable.name()));
        clause.terms().stream().filter(term -> term instanceof Constant).forEach(constant -> terms.put(constant, constant.name()));
        clause.literals().stream().filter(literal -> literal.arity() == 1).forEach(literal -> {
            Term argument = Sugar.chooseOne(literal.terms());
            String extended = terms.get(argument) + ", " + literal;
            terms.put(argument, extended);
        });
        String nodes = terms.entrySet().stream().map(entry -> "n" + entry.getKey().name() + " [label=\"" + entry.getValue() + "\"];").collect(Collectors.joining("\n"));

        String dependencies = clause.literals().stream()
                .filter(literal -> literal.arity() == 2)
                .map(literal -> "n" + literal.get(0).name() + " ->  " + "n" + literal.get(1).name() + " [ label=\"" + ((literal.isNegated()) ? "!" : "") + literal.predicate() + "\"];")
                .collect(Collectors.joining("\n"));

        StringBuilder sb = new StringBuilder();
        sb.append("digraph G  {\n");
        sb.append(nodes);
        sb.append("\n");
        sb.append(dependencies);
        sb.append("\n}");
        return sb.toString();
    }

    private void drawEquivalenceClassDiagram() {
        List<Clause> clauses = Sugar.list("",
                "!b(X,Y)",
                "!b(X,X)",
                "!p(X)",
                "!b(X,Y),!p(X)",
                "!b(X,Y),!p(Y)",
                "!b(X,Y),!b(Y,X)",
                "!p(X),!p(Y)",
                "!b(X,Y),!p(X),!p(Y)",
                "!b(X,Y),!b(Y,X),!p(X)",
                "!b(X,Y),!b(Y,X),!p(X),!p(Y)"
        )
                .stream()
                .map(Clause::parse)
                .collect(Collectors.toList());

        String graph = drawDot(clauses);
        System.out.println(graph);

        List<Clause> theory = Sugar.list("!b(X,Y),b(Y,X)", "!b(X,Y),p(X)").stream()
                .map(Clause::parse)
                .collect(Collectors.toList());

        equivalencesClasses(clauses, theory).stream()
                .forEach(eqclass -> {
                    System.out.println("equivalence class");
                    eqclass.forEach(clause -> System.out.println("\t" + clause));
                });
    }

    private static Drawer create() {
        return new Drawer();
    }

    private static Collection<Set<Clause>> equivalencesClasses(List<Clause> clauses, List<Clause> theory) {
//        MultiMap<IsoClauseWrapper, Clause> map = new MultiMap<>();
//        RuleSaturator saturator = RuleSaturator.create(theory);
//        clauses.stream().forEach(clause -> map.put(IsoClauseWrapper.create(saturator.saturate(clause)), clause));
//        return map.values();
        throw new UnsupportedOperationException();
    }

}
