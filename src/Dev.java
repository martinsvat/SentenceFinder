/*
import ida.ilp.logic.*;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.*;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Dev {
    public static void main(String[] args) {
//        jep();
        //        testSkolem();
//        testSomething();
//        testIsomorhpic();
//        testIsomorhpic2();
//        checkNegatedIsomorphism();
//        devIsomorhpic();
//        checkFipping();
//        juliaTest();
//        debugVersionWise();
//        symbolicWeights();
        //decomposability();
//        decideCellGraphs();
        testPartialParsing();
    }

    private static void testPartialParsing() {
        SentenceSetup setup = SentenceSetup.create();
        SentenceFinder finder = new SentenceFinder(setup);

        List<SentenceState> s1 = SentenceState.parseMultiplePossibleQuantifiers("(E x U0(x)) & (V x U0(x))", finder.quantifiersToCache(), finder.literalCache, setup);
        for (SentenceState sentenceState : s1) {
            System.out.println(sentenceState.toFol(true,true));
        }
    }

    private static void decideCellGraphs() {
        SentenceSetup setup = SentenceSetup.create();
        SentenceFinder finder = new SentenceFinder(setup);
        HashMap<String, Quantifier> map = finder.quantifiersToCache();
//        (V x U0(x) | U1(x)) & (V x E y U0(x) | ~U1(y))
//        (V x U0(x) | U1(x)) & (E x V y ~U0(x) | U1(y))
        SentenceState s3 = SentenceState.parse("(V x V y U0(x) | U1(x)) & (V x E y U0(x) | ~U1(y))", map,setup,finder.literalCache);
        SentenceState s4 = SentenceState.parse("(V x V y U0(x) | U1(x)) & (E x V y ~U0(x) | U1(y))", map, setup,finder.literalCache);
        System.out.println(s3.isPredicateIsomorphic(s4));

        List<Pair<SentenceState, CandidateProperties>> list = Sugar.list(
                new Pair<>(s3, CandidateProperties.create(true, true)),
                new Pair<>(s4, CandidateProperties.create(true, true)));
        finder.fillInCellGraph(list);
        Clause cg1 = list.get(0).getR().getCellGraph();
        Clause cg2 = list.get(1).getR().getCellGraph();
        System.out.println(cg1);
        System.out.println(cg2);
        Matching m = new Matching();
        System.out.println(m.isomorphism(cg1, cg2));

    }


    private static void decomposability() {
        Clause c = Clause.parse("U(x) | U1(y)", '|', null);
        System.out.println(c.isDecomposable());
        Clause c2 = Clause.parse("U(x) | U1(y) | B(x,y)", '|', null);
        System.out.println(c2.isDecomposable());
    }

    private static void symbolicWeights() {
        Clause c2 = Clause.parse("p(x,N, \'-10*x1*x2^7 +x1 +10\')");
//        Clause c2 = Clause.parse("p(x,N, 10)");
//        Clause c2 = Clause.parse("p(x,N, \'-10*x1*x2^7 -x1 -10\')");
//        Clause c2 = Clause.parse("p(x,N, \'-x1 + 10*x + 11*x2^2*x1^13 - 3*x^2\')");
        System.out.println(c2);
        System.out.println("a");

        Literal l = Sugar.chooseOne(c2.literals());
        Term s = l.arguments()[2];
        Constant constant = (Constant) s;


        VariableSupplier sumSupplier = VariableSupplier.create("m");
        VariableSupplier productSupplier = VariableSupplier.create("p");
        Map<String, Term> expressionCache = new HashMap<>();


        Term finalTerm = null;
        List<Literal> parseTree = Sugar.list();
        if (constant.name().startsWith("'")) { // symbolic weight
            String expression = constant.name();
            expression = expression.substring(1, expression.length() - 1); // removing first and last '...'
            if (expressionCache.containsKey(expression)) {
                finalTerm = expressionCache.get(expression);
            } else {
                String expressionBackup = expression;
                finalTerm = sumSupplier.getNext();

                List<Pair<Term, Boolean>> sums = Sugar.list(); // sum is either a constant (e.g. 10) or a product (e.g. p1)
                int start = 0;
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
                    System.out.println("parsing element\t" + part + "\t and continuing with\t" + expression);

                    if (part.contains("x")) { // we're gonna do some product
                        Variable productVariable = productSupplier.getNext();
                        sums.add(new Pair<>(productVariable, startsWithMinus));

                        String[] subs = part.split("\\*");
                        for (int idx = 0; idx < subs.length; idx++) {
                            String expr = subs[idx];
                            System.out.println("\t" + expr);
                            if (expr.contains("x")) {
                                List<Term> arguments = Sugar.list(productVariable);
                                String[] split = expr.split("\\^");
                                arguments.add(Variable.construct(split[0]));
                                arguments.add(new Constant(2 == split.length ? split[1] : "1"));

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

                expressionCache.put(expressionBackup, finalTerm);
            }
        } else { // scalar
            finalTerm = constant;
        }

        System.out.println(finalTerm);
        System.out.println(parseTree);

    }


    private static void debugVersionWise() {
//        f1 = Paths.get("C:\\data\\school\\development\\sequence-db\\debug\\sfinder_stored_search_states\\sfinder_stored_search_states\\")
    }

    private static void jep() {

    }

    private static void juliaTest() {
        System.out.println("* Initializing tests");
//        caller = new JuliaCaller("/usr/local/bin/julia", 8000);
//        caller = new JuliaCaller("D:\\Users\\svato\\AppData\\Local\\Programs\\Julia-1.8.2\\bin\\julia.exe", 8001);
//        caller = new JuliaCaller(Utilities.TryFindingJuliaExecutable(), 8000);
        try {
            ScriptEngineManager manager = new ScriptEngineManager();
            ScriptEngine engine = manager.getEngineByName("Julia");

// Creating array in Julia
            engine.eval("a = [1,2,3]");
            engine.eval("f(x) = sum(x) / length(x)");
            engine.eval("b = f(a)");

// Handling result in Java
            Object result = engine.get("b");
            System.out.println("result!");
        } catch (ScriptException e) {
            throw new RuntimeException(e);
        }
    }

//    private static void testSkolem() {
//        HashMap map = new HashMap();
//        SentenceState s = SentenceState.parse("(V x E y B0(x, y) | U(x)) & (E x V y B0(x, y)  | U(x)) & (E x V y U0(x) | U(x)) & (E x E y B0(x, y) | U(x))", map, null, finder.);
//        System.out.println(s);
//        System.out.println(s.getOutputPrenexAndSkolemForm(" \n"));
//
//        System.out.println();
//        System.out.println(new SentenceState(Sugar.list(s.clauses.get(0)), null).getOutputPrenexAndSkolemForm("\n"));
//        System.out.println();
//        System.out.println(new SentenceState(Sugar.list(s.clauses.get(1)), null).getOutputPrenexAndSkolemForm("\n"));
//    }

//    private static void checkFipping() {
//        //???musime prohodit nebo prejmenovat kvantifikatory taky
//        SentenceSetup setup = new SentenceSetup(1, 1, 1, Sugar.list(), Sugar.list(), true, false, "", true, null, true, "", false, false, 1, true, true, true, true, true, true, 0, 0, 0, true, true, 10);
//        HashMap map = new HashMap<>();
//        SentenceState s1 = SentenceState.parse("(V x E y B0(y, x))", map, setup);
//        SentenceState s2 = SentenceState.parse("(V x E y B0(x, y))", map, setup);
//
//
//        Pair<List<Clause>, List<Clause>> d = s2.getPredicateIsomorphicRepresentation();
//        for (Clause clause : d.getS()) {
//            System.out.println(clause);
//        }
//        System.out.println(s1.isPredicateIsomorphic(s2));
//    }

//    private static void testIsomorhpic() {
//        SentenceSetup setup = SentenceSetup.create();
//        HashMap map = new HashMap<>();
//
//        SentenceState s1 = SentenceState.parse("(V x V y B0(x, y) | B0(x, x) | ~B0(y, y))", map, setup);
//        SentenceState s2 = SentenceState.parse("(V x V y B0(x, y) | B0(y, y) | ~B0(x, x))", map, setup);
//        System.out.println(s1);
//        System.out.println(s2);
////        System.out.println(s1.getPredicateIsomorphicRepresentation(true));
////        System.out.println(s2.getPredicateIsomorphicRepresentation(true));
//        System.out.println(s1.isPredicateIsomorphic(s2));
//
//        SentenceState s3 = SentenceState.parse("(V x V y B0(x, y) | B0(y, x) | ~B0(x, x))", map, setup);
//        SentenceState s4 = SentenceState.parse("(V x V y B0(x, y) | B0(y, x) | ~B0(y, y))", map, setup);
//        System.out.println(s3);
//        System.out.println(s4);
////        System.out.println(s3.getPredicateIsomorphicRepresentation(true));
////        System.out.println(s4.getPredicateIsomorphicRepresentation(true));
//        System.out.println(s3.isPredicateIsomorphic(s4));
//
//        SentenceState s5 = SentenceState.parse("(V x V y B0(x, y) | B0(x, x) | ~B0(y, x))", map, setup);
//        SentenceState s6 = SentenceState.parse("(V x V y B0(x, y) | B0(y, y) | ~B0(y, x))", map, setup);
//        System.out.println(s5);
//        System.out.println(s6);
////        System.out.println(s5.getPredicateIsomorphicRepresentation(true));
////        System.out.println(s6.getPredicateIsomorphicRepresentation(true));
//        System.out.println(s5.isPredicateIsomorphic(s6));
//    }

//    private static void testIsomorhpic2() {
//        SentenceSetup setup = SentenceSetup.create();
//        SentenceFinder finder = new SentenceFinder(setup);
//        HashMap<String, Quantifier> map = finder.quantifiersToCache();
//
//        SentenceState s0 = SentenceState.parse("(V x E y U1(x) | ~U(y))", map, setup);
//        SentenceState s1 = SentenceState.parse("(E x V y U1(x) | ~U(y))", map, setup);
//        SentenceState s2 = SentenceState.parse("(E x V y ~U1(x) | ~U(y))", map, setup);
//        SentenceState s3 = SentenceState.parse("(V x V y U0(x) | U1(x)) & (V x E y U0(x) | ~U1(y))", map, setup);
//        SentenceState s4 = SentenceState.parse("(V x V y U0(x) | U1(x)) & (E x V y ~U0(x) | U1(y))", map, setup);
////odzkouset to na jine parametrizaci sentenci
//
//        // (V x E y U0(x) | ~U1(y)) tohle by melo byt decomposable ale pry neni
//
//        System.out.println("TODO zjistit zda maji s3 a s4 izomorfni cell-grafy");
//
//        System.out.println(s0.isPredicateIsomorphic(s1));
//        System.out.println(s0.isPredicateIsomorphic(s2));
//        System.out.println(s3.isPredicateIsomorphic(s4));
//    }

*/
/*
    private static void devIsomorhpic() {
        SentenceSetup setup = SentenceSetup.create();
        HashMap map = new HashMap<>();
        SentenceFinder finder = new SentenceFinder(setup);

        SentenceState s0 = SentenceState.parse("(V x E y B0(x, x) | B0(x, y))", map, setup);
        System.out.println(s0);
        System.out.println(s0.getOutputPrenexAndSkolemForm("\n"));
        System.out.println(finder.canBeReduced(s0));

        SentenceState s1 = SentenceState.parse("(V x V y B0(x, y) | ~B0(x, x)) & (V x E y B0(x, x) | ~B0(x, y))", map, setup);
        SentenceState s2 = SentenceState.parse("(V x V y B0(x, y) | ~B0(x, x)) & (V x E y B0(x, x) | ~B0(y, x))", map, setup);
        System.out.println(s1);
        System.out.println(s2);
        System.out.println(s1.isPredicateIsomorphic(s2));
        System.out.println(s2.isPredicateIsomorphic(s1));

        SentenceState s3 = SentenceState.parse("(V x V y B0(x, y) | ~B0(x, x))", map, setup);
        SentenceState s4 = SentenceState.parse("(V x V y B0(x, y) | ~B0(x, x))", map, setup);
        System.out.println(s3);
        System.out.println(s4);
        System.out.println(s3.isPredicateIsomorphic(s4));
        System.out.println(s4.isPredicateIsomorphic(s3));

        SentenceState s5 = SentenceState.parse("(V x E y B0(x, x) | ~B0(x, y))", map, setup);
        SentenceState s6 = SentenceState.parse("(V x E y B0(x, x) | ~B0(y, x))", map, setup);
        System.out.println(s5);
        System.out.println(s6);
        System.out.println(s5.isPredicateIsomorphic(s6));
        System.out.println(s6.isPredicateIsomorphic(s5));

        System.out.println(finder.canBeReduced(s1));
        System.out.println(finder.canBeReduced(s2));

    }
*//*


*/
/*
    private static void testSomething() {
        HashMap map = new HashMap<>();
        SentenceSetup setup = SentenceSetup.createFromCmd();
//        SentenceState s = SentenceState.parse("(V x V y B0(x, y) | ~B0(y, x)) & (V x V y B0(x, x)) & (V x E y ~B0(x, y)) & (V x V y ~B0(x, x))", map, setup);
//        SentenceState s = SentenceState.parse("(V x V y B0(x, x)) & (V x V y ~B0(x, x))", map, setup);
        SentenceFinder finder = new SentenceFinder(SentenceSetup.create());
        HashMap<String, Quantifier> cache = finder.quantifiersToCache();
        SentenceState s = SentenceState.parse("(V x V y U0(x)) & (V x V y ~U0(x))", cache, setup);
        System.out.println(s);
        s.clauses.forEach(c -> System.out.println(c + "\t->\t" + c.getProver9Format()));


        boolean result = finder.isContradiction(s);
        System.out.println(result);
//        System.out.println(finder.isTautology(s));
    }
*//*


*/
/*
    private static void checkNegatedIsomorphism() {
        SentenceSetup setup = new SentenceSetup(1, 1, 1, Sugar.list(), Sugar.list(), true, false, "", true, null, true, "", false, false, 1, true, true, true, true, true, true, 0, 0, 0, true, true, 10);
        HashMap map = new HashMap<>();
        SentenceState s = SentenceState.parse("(V x V y U(x) | ~U(y))", map, setup);
        SentenceState s2 = SentenceState.parse("(V x V y U(x) | U(y))", map, setup);
        SentenceState s3 = SentenceState.parse("(V x V y ~U(x) | U(y))", map, setup);

        System.out.println("s = " + s);
        System.out.println("s2 = " + s2);
        System.out.println("s3 = " + s3);
        System.out.println("s vs s2 " + s.isPredicateIsomorphic(s2));
        System.out.println("s vs s3 " + s.isPredicateIsomorphic(s3));
        System.out.println("s2 vs s3 " + s2.isPredicateIsomorphic(s3));

        SentenceState b = SentenceState.parse("(V x V y U(x) | ~B(y))", map, setup);
        SentenceState b2 = SentenceState.parse("(V x V y U(x) | B(y))", map, setup);
        System.out.println("b = " + b);
        System.out.println("b2 = " + b2);
        System.out.println("b vs b2 " + b.isPredicateIsomorphic(b2));

        SentenceState x = SentenceState.parse("(V x V y U(x) | ~B(y) | B(x) | B(x,x)) & (E x E y ~U(x) | B(y)  | B(x,x) | ~B(x,y))", map, setup);
        System.out.println(x);
//        System.out.println(x.getPredicateIsomorphicRepresentation(true));
    }
 *//*


}
*/
