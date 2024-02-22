import ida.cellGraphs.CanonicalFilter;
import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Predicate;
import ida.ilp.logic.Variable;
import ida.ilp.logic.quantifiers.Quantifier;
import ida.ilp.logic.quantifiers.QuantifiersGenerator;
import ida.ilp.logic.subsumption.Matching;
import ida.sentences.SentenceSetup;
import ida.sentences.SentenceState;
import ida.sentences.caches.LiteralsCache;
import ida.sentences.filters.JoiningFilter;
import ida.sentences.filters.SingleFilter;
import ida.sentences.generators.ClausesGenerator;
import ida.sentences.generators.LiteralsGenerator;
import ida.sentences.generators.PredicateGenerator;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

public class Tests {

    private static List<Variable> variables = Sugar.list(Variable.construct("x"), Variable.construct("y"));

    public static void main(String[] args) {
        // TODO to bo honest, we should clear all caches before invocation of each single test

        quantifiersCountsTest();
        quantifiersSuccessorsTest(); // this is really 2-variable specific! with 1 variable it will fail
        quantifiersMirrorTest();
        literalsGeneratorTest();
        clausesGeneratorTest();

        naiveTautologyFilterTest();
        tautologyFilterTest(Paths.get("D:\\Program Files (x86)\\Prover9-Mace4\\bin-win32\\prover9.exe"));
        contradictionTest(Paths.get("D:\\Program Files (x86)\\Prover9-Mace4\\bin-win32\\prover9.exe"));
        disjunctiveClauses();
        maxClauses();
        connectedComponents();
        trivialConstraints();
        reflexiveAtoms();
        thetaReduction();
        quantifiersReduction();
        predicateFollowers();
        languageBias();

        // these should be more profound
        isoVariablesOnly();
        isoVariablesPredicates();
        isoVariablesPredicatesSigns();
        isoVariablesPredicatesSignsDirection();
        ultraCannonic();


        //cannonicCellGraph();
    }

    // TODO rewrite these test, because those are suited for CellSubGraphBasic but CellSubGraph produces a different canonical form
    private static void cannonicCellGraph() {
        SentenceSetup setup = SentenceSetup.createFromCmd();
        CanonicalFilter filter = CanonicalFilter.create(setup);
        List<Pair<String, String>> inputAndExpectedOutput = Sugar.list(
                new Pair<>("W(1, g0), L(n0, 1, 1, g0), G(g0)", "L(0,1,1), W(1)"), // base camp
                new Pair<>("W(1, g0), L(n1, 1, 1, g0), G(g0)", "L(0,1,1), W(1)"), // node invariant
                new Pair<>("W(1, g0), L(n0, 1*x1^2, 10*x2^2*x1^1, g0), G(g0)", "L(0,1*0^2,10*0^1*1^2), W(1)"), // weight invariant
                new Pair<>("W(1, g0), L(n0, 1*x1^2, 10*x2^2*x1^1, g0), G(g0) ; W(-1, g1), L(n0, x0^2, -2, g0), G(g1)", "L(0,1*0^2,-2), W(-1)>L(0,1*1^2,10*1^1*2^2), W(1)"), // weight-disconnected graphs
                new Pair<>("W(1, g0), E(n1, n2, x2*x1), E(n2, n1, x1*x2), L(n1, 1*x1^1*x2^2, x2, g0), G(g0)", "E(0,1,1*0^1*1^1), E(1,0,1*0^1*1^1), L(0,1*0^1*1^2,1*1^1), W(1)"), // rest of edges
                new Pair<>("W(1, g0), E(n1, n2, x2*x1), E(n2, n1, x1*x2), L(n1, 1*x1^2*x2^1, x2, g0), G(g0)", "E(0,1,1*0^1*1^1), E(1,0,1*0^1*1^1), L(0,1*0^1*1^2,1*0^1), W(1)"), // decision made by exponents in the L/3 literal
                new Pair<>("W(1, g0), C(n1, 1, 0, 1, x1), C(n1, 0, 1, 1, x2), G(g0)", "C(0,0,1,1,1*0^1), C(0,1,0,1,1*1^1), W(1)") // C5 test
        );
        for (Pair<String, String> test : inputAndExpectedOutput) {
            String input = test.getR();
            String expectedOutput = test.getS();
            String output = filter.toCanonical(input);
            if (!expectedOutput.equals(output)) {
                System.out.println("input\t" + input + "\nexpected\t" + expectedOutput + "\nresult\t\t" + output);
            }
            assert expectedOutput.equals(output);
        }
    }

    private static void languageBias() {
        List<Predicate> predicates = Sugar.list(Predicate.create("U0", 1),
                Predicate.create("U1", 1),
                Predicate.create("U2", 1), Predicate.create("B0", 2), Predicate.create("B1", 2), Predicate.create("B2", 2));
        LiteralsGenerator.generate(variables, predicates);
        List<Literal> literals = LiteralsGenerator.generate(variables, predicates);
        ClausesGenerator generator = new ClausesGenerator(literals, null, null, null, PredicateGenerator.generateFollowers(predicates));
        JoiningFilter filter = generator.languageBias();
        List<Triple<String, String, Boolean>> tests = Sugar.list(
                new Triple<>("(V x U0(x))", "(E x U0(x) | ~U0(x))", true),
                new Triple<>("(V x U0(x))", "(E x B0(x, x))", true),
                new Triple<>("(E x B0(x, x))", "(V x U0(x))", true),
                new Triple<>("(V x U0(x))", "(E x U2(x) | B0(x, x))", false),
                new Triple<>("(V x U0(x))", "(E x U1(x) | B0(x, x))", true),
                new Triple<>("(V x B0(x, x))", "(E x U1(x) | U2(x))", false),
                new Triple<>("(V x B0(x, x))", "(E x U0(x) | U2(x))", false),
                new Triple<>("(V x B0(x, x))", "(E x U0(x) | U1(x))", true),
                new Triple<>("(V x B0(x, x) | U0(x))", "(E x U1(x) | U2(x))", true),
                new Triple<>("", "(V x U0(x) | U1(x))", true),
                new Triple<>("", "(V x U2(x) | ~U1(x))", false)
        );
        for (Triple<String, String, Boolean> test : tests) {
            boolean result = filter.test(SentenceState.parse(test.getR()), Clause.parseWithQuantifier(test.getS()));
            Boolean expectedResult = test.getT();
            if (result != expectedResult) {
                System.out.println(SentenceState.parse(test.getR()).toFol() + "\t" + Clause.parseWithQuantifier(test.getS()).toFOL());
                System.out.println("should be\t" + expectedResult + "\tbut isn't");
            }
            assert test.getT() == result;
        }
    }

    private static void predicateFollowers() {
        Predicate u0 = Predicate.create("U0", 1);
        Predicate u1 = Predicate.create("U1", 1);
        Predicate u2 = Predicate.create("U2", 1);
        Predicate b0 = Predicate.create("B0", 2);
        Predicate b1 = Predicate.create("B1", 2);
        Predicate b2 = Predicate.create("B2", 2);
        List<Predicate> predicates = Sugar.list(u0, u1, u2, b0, b1, b2);
        Map<Predicate, Predicate> followers = PredicateGenerator.generateFollowers(predicates);

        Map<Predicate, Predicate> expectedOutput = new HashMap<>();
        expectedOutput.put(u0, u1);
        expectedOutput.put(u1, u2);
        expectedOutput.put(b0, b1);
        expectedOutput.put(b1, b2);

        assert expectedOutput.equals(followers);
    }

    private static void isoVariablesPredicatesSignsDirection() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("U1", 1),
                Predicate.create("B0", 2), Predicate.create("B1", 2)));
        SentenceSetup setup = new SentenceSetup(variables.size()).setIso(true, true, true);
        List<Triple<String, String, Boolean>> test = Sugar.list(
                new Triple<>("(V x E y ~B1(x, y))", "(V x V y B0(y, x))", false),
                new Triple<>("(V x E y ~B1(x, y))", "(E x V y B0(y, x))", false),
                new Triple<>("(V x V y ~B1(x, y) | B1(y, x))", "(V x V y B0(y, x) | ~B1(x, y))", false),
                new Triple<>("(V x V y ~B1(x, y) | B1(y, x))", "(V x V y B0(x, y) | ~B0(y, x))", true)
        );

        evaluateIsoTests(setup, test);
    }

    private static void isoVariablesPredicatesSigns() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("U1", 1),
                Predicate.create("B0", 2), Predicate.create("B1", 2)));
        SentenceSetup setup = new SentenceSetup(variables.size()).setIso(true, true, false);
        List<Triple<String, String, Boolean>> test = Sugar.list(
                new Triple<>("(V x U0(x))", "(V x B0(x, x))", false),
                new Triple<>("(V x U0(x))", "(V x ~U1(x))", true),
                new Triple<>("(V x V y U0(x) | ~U1(y))", "(V x V y U1(x) | ~U0(y))", true),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y B0(y, x))", true),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y ~B1(y, x))", true),
                new Triple<>("(V x V y ~B0(x, y) | B0(x, x) | ~B1(y, y))", "(V x V y ~B1(y, x) | B0(y, y))", false),
                new Triple<>("(V x V y ~B0(x, y) | B0(x, x) | ~B1(y, y))", "(V x V y ~B1(y, x) | B0(x, y) | B1(x, x))", false),
                new Triple<>("(V x V y ~B0(x, y) | B0(x, x) | ~B1(y, x))", "(V x V y ~B1(y, x) | ~B0(x, y) | B1(y, y))", true),
                new Triple<>("(V x U0(x) | ~U1(x)) & (E x U1(x))", "(V x ~U1(x) | U0(x)) & (E x U0(x))", false),
                new Triple<>("(V x U0(x) | ~U1(x)) & (E x U1(x))", "(V x ~U1(x) | U0(x)) & (E x ~U0(x))", true)
        );

        evaluateIsoTests(setup, test);
    }


    private static void isoVariablesOnly() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("U1", 1),
                Predicate.create("B0", 2), Predicate.create("B1", 2)));
        SentenceSetup setup = new SentenceSetup(variables.size()).setIso(false, false, false);
        List<Triple<String, String, Boolean>> test = Sugar.list(
                new Triple<>("(V x U0(x))", "(V x B0(x, x))", false),
                new Triple<>("(V x U0(x))", "(V x U1(x))", false),
                new Triple<>("(V x E y U0(x) | U1(y))", "(E x V y U0(y) | U1(x))", true),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y B0(y, x))", false),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y ~B1(y, x))", false),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y ~B1(y, x))", false)
        );

        evaluateIsoTests(setup, test);
    }

    private static void isoVariablesPredicates() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("U1", 1),
                Predicate.create("B0", 2), Predicate.create("B1", 2)));
        SentenceSetup setup = new SentenceSetup(variables.size()).setIso(true, false, false);
        List<Triple<String, String, Boolean>> test = Sugar.list(
                new Triple<>("(V x U0(x))", "(V x B0(x, x))", false),
                new Triple<>("(V x U0(x))", "(V x U1(x))", true),
                new Triple<>("(V x V y U0(x) | ~U1(y))", "(V x V y U1(x) | ~U0(y))", true),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y B0(y, x))", false),
                new Triple<>("(V x V y ~B0(x, y))", "(V x V y ~B1(y, x))", true)
        );

        evaluateIsoTests(setup, test);
    }


    private static void evaluateIsoTests(SentenceSetup setup, List<Triple<String, String, Boolean>> test) {
        for (Triple<String, String, Boolean> triple : test) {
            SentenceState input = SentenceState.parse(triple.getR(), setup);
            SentenceState output = SentenceState.parse(triple.getS(), setup);
            Matching m = new Matching();
            if (triple.getT() != m.isomorphism(input.getICW(LiteralsCache.getInstance()).getOriginalClause(), output.getICW(LiteralsCache.getInstance()).getOriginalClause())) {
                System.out.println("input is\t" + input.toFol());
                System.out.println("expected is\t" + output.toFol());
                System.out.println("should iso\t" + triple.getT() + "\t but instead\t" + m.isomorphism(input.getICW(LiteralsCache.getInstance()).getOriginalClause(), output.getICW(LiteralsCache.getInstance()).getOriginalClause()));
                System.out.println("\t-> " + input.getICW(LiteralsCache.getInstance()).getOriginalClause());
                System.out.println("\t-> " + output.getICW(LiteralsCache.getInstance()).getOriginalClause());
            }
            assert triple.getT() == m.isomorphism(input.getICW(LiteralsCache.getInstance()).getOriginalClause(), output.getICW(LiteralsCache.getInstance()).getOriginalClause());
        }
    }

    private static void quantifiersReduction() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        JoiningFilter filter = generator.quantifiersReducibility();
        List<Triple<String, String, Boolean>> tests = Sugar.list(
                new Triple<>("(E x B0(x, x))", "(V x V y B0(x, y))", false), // check this out!
                new Triple<>("(V x U0(x))", "(E x U0(x))", false),
                new Triple<>("(V x U0(x))", "(E x E y U0(x) | ~U0(x) | B0(y, y))", false),
                new Triple<>("(V x U0(x))", "(E x B0(x, x))", true),
                new Triple<>("(V x U0(x))", "(E x U0(x) | ~U0(x))", false),
                new Triple<>("(E x U0(x) | ~U0(x))", "(V x U0(x))", false),
                new Triple<>("(E x E y U0(x) | ~U0(y))", "(V x U0(x))", false),
                new Triple<>("(V x B0(x, x)) & (E x U0(x))", "(E=1 x B0(x, x))", false),
                new Triple<>("(V x E y U0(x) | B0(x, y) | ~U0(y))", "(V x E y U0(x) | B0(x, y) | ~U0(y))", false),
                new Triple<>("(V x E y U0(x) | B0(x, y) | ~U0(y))", "(E x V y U0(y) | B0(y, x) | ~U0(x))", false),
                new Triple<>("(V x E y U0(x) | B0(x, y) | ~U0(y))", "(E x V y U0(x) | B0(x, y) | ~U0(y))", true),
                new Triple<>("(V x E y U0(x) | ~B0(y, y))", "(E x V y B0(x, y) | U0(y) | ~B0(x, x) | ~B0(y, y))", false),
                new Triple<>("(E x V y B0(x, y) | U0(y) | ~B0(x, x) | ~B0(y, y))", "(V x E y U0(x) | ~B0(y, y))", false)
        );
        for (Triple<String, String, Boolean> test : tests) {
            boolean result = filter.test(SentenceState.parse(test.getR()), Clause.parseWithQuantifier(test.getS()));
            Boolean expectedResult = test.getT();
            if (result != expectedResult) {
                System.out.println(SentenceState.parse(test.getR()).toFol() + "\t" + Clause.parseWithQuantifier(test.getS()).toFOL());
                System.out.println("should be\t" + expectedResult + "\tbut isn't");
            }
            assert test.getT() == result;
        }
    }


    private static void thetaReduction() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        SingleFilter<Clause> filter = generator.thetaSubsumptionFilter();

        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, y))"));
        assert filter.test(Clause.parseWithQuantifier("(V x B0(x, x))"));
        assert filter.test(Clause.parseWithQuantifier("(V x B0(x, x) | ~B0(x, x))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x) | B0(y, y))"));
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x) | B0(y, y) | ~B0(x, y))"));
        assert filter.test(Clause.parseWithQuantifier("(E x U0(x) | ~U0(x))"));

        assert filter.test(Clause.parseWithQuantifier("(V x E y U0(x) | ~U0(y))"));
        assert filter.test(Clause.parseWithQuantifier("(V x E y B0(x, x) | ~B0(x, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x E y B0(x, x) | B0(x, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x E y ~B0(x, x) | ~B0(x, y))"));

        assert filter.test(Clause.parseWithQuantifier("(E x V y U0(x) | ~U0(y))"));
        assert filter.test(Clause.parseWithQuantifier("(E x V y B0(x, x) | ~B0(x, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x V y B0(x, x) | B0(x, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x V y ~B0(x, x) | ~B0(x, y))"));

        assert filter.test(Clause.parseWithQuantifier("(E x E y U0(x) | ~U0(y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x E y U0(x) | U0(y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x E y ~U0(x) | ~U0(y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x E y B0(x, y) | B0(y, x))"));
        assert filter.test(Clause.parseWithQuantifier("(E x E y B0(x, y) | ~B0(y, x))"));
        assert filter.test(Clause.parseWithQuantifier("(E x V y U0(x) | ~B0(y, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x V y B0(y, y) | ~U0(x) | ~U0(y))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x E y B0(x, x) | ~U0(y) | ~U0(x))"));
    }

    private static void ultraCannonic() {
//        System.out.println("ultraCannonic: tady by slo udelat jeste jedno zrychleni, proste vezmeme lookahead dopredu jake dalsi literaly to jeste ovlivni... pokud zadne tak muzeme ponechat pouze jeden jediny setup; pokud to dal ovlivni jen jeden nazev predikatu, tak se to da taky oriznout; pokud vice predikatu tak nevim");
        List<Predicate> predicates = Sugar.list(Predicate.create("U0", 1), Predicate.create("U1", 1), Predicate.create("B0", 2), Predicate.create("B1", 2));
        LiteralsGenerator.generate(variables, predicates);
        SentenceSetup setup = new SentenceSetup(2).setPredicates(predicates);

        List<Pair<String, String>> l = Sugar.list(
                new Pair<>("(V x U0(x))", "(V x U0(x))"),
                new Pair<>("(V x U1(x))", "(V x U0(x))"),
                new Pair<>("(V x ~U1(x))", "(V x U0(x))"),
                new Pair<>("(E x ~U1(x))", "(E x U0(x))"),
                new Pair<>("(E x E y ~U1(x) | U0(y))", "(E x E y U0(x) | U1(y))"),
                new Pair<>("(E x V y ~U0(x) | U1(y)) & (E x E y U0(x) | U1(y))", "(E x E y U0(x) | U1(y)) & (E x V y U0(y) | ~U1(x))"),
                new Pair<>("(V x E y ~U1(y) | U0(x)) & (E x E y U0(x) | U1(y))", "(E x E y U0(x) | U1(y)) & (E x V y U0(y) | ~U1(x))"),
                new Pair<>("(V x V y B0(x, y)) & (V x V y B0(y, x))", "(V x V y B0(x, y)) & (V x V y B0(x, y))"), // this is actually a sentence that would be filtered by quantifiers-subsumptions techniques, etc.
                new Pair<>("(V x V y B0(x, y)) & (V x V y U0(x) | ~U1(y)) & (V x V y U0(x) | ~U1(y) | ~B0(y, x))", "(V x V y B0(x, y) | U0(x) | U1(y)) & (V x V y U0(x) | U1(y)) & (V x V y ~B0(x, y))"),
                new Pair<>("(V x E=1 y B0(x, y))", "(V x E=1 y B0(x, y))"),
                new Pair<>("(V x E=1 y ~B0(y, x))", "(V x E=1 y B0(x, y))"),
                new Pair<>("(E x V y B0(y, y) | ~B0(x, x)) & (E=1 x V y B0(x, y))", "(E x V y B0(x, x) | ~B0(y, y)) & (E=1 x V y ~B0(x, y))"),
                new Pair<>("(E=1 x V y B0(x, y)) & (V x E y B0(x, x) | ~B0(y, y))", "(E x V y B0(x, x) | ~B0(y, y)) & (E=1 x V y ~B0(x, y))"),
                new Pair<>("(V x V y B0(x, x) | ~B0(y, y)) & (V x V y ~B0(x, y) | ~U0(x))", "(V x V y B0(x, x) | ~B0(y, y)) & (V x V y B0(x, y) | U0(x))")
        );
        for (Pair<String, String> pair : l) {
            String input = pair.getR();
            String expectedOutput = pair.getS();
            String output = SentenceState.parse(input, setup).getUltraCannonic();
            if (!output.equals(expectedOutput)) {
                System.out.println("!");
                System.out.println(input);
                System.out.println(expectedOutput);
                System.out.println(output);
            }
            assert output.equals(expectedOutput);
        }
    }

    private static void reflexiveAtoms() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2), Predicate.create("B1", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        SingleFilter<SentenceState> filter = generator.reflexiveAtoms();
        assert filter.test(SentenceState.parse("(V x E y B0(x, y))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x))"));
        assert !filter.test(SentenceState.parse("(V x V y B0(x, x) | ~B0(y, y))"));
        assert !filter.test(SentenceState.parse("(V x V y B0(x, x) | U0(y))"));
        assert filter.test(SentenceState.parse("(V x E y B0(x, y) | U0(x))"));
        assert !filter.test(SentenceState.parse("(V x B0(x, x) | U0(x)) & (V x B0(x, x))"));
        assert !filter.test(SentenceState.parse("(V x B0(x, x) | U0(x)) & (V x B1(x, x))"));
        assert !filter.test(SentenceState.parse("(V x B0(x, x) | U0(x)) & (E x V y B0(x, y) | B1(x, x))"));
        assert filter.test(SentenceState.parse("(V x B0 (x, x) | U0(x)) & (E x V y B0 (x, y) | ~B1(y, x))"));
    }

    private static void trivialConstraints() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        JoiningFilter filter = generator.trivialConstraints();
        assert !filter.test(SentenceState.parse("(E x B0(x, x))"), Clause.parseWithQuantifier("(V x V y B0(x, y))")); // check this out!
        assert !filter.test(SentenceState.parse("(E x U0(x))"), Clause.parseWithQuantifier("(V x U0(x))"));
        assert filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x B0(x, x))"));
        assert !filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x U0(x))"));
        assert !filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x ~U0(x))"));
        assert !filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x V y B0(x, y))"));
        assert !filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x V y B0(y, x))"));
        assert !filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x V y ~B0(x, y))"));
        assert !filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x V y ~B0(y, x))"));
        assert !filter.test(SentenceState.parse("(E x V y B0(x, y) | ~B0(y, y))"), Clause.parseWithQuantifier("(V x V y B0(x, y))"));
        assert !filter.test(SentenceState.parse("(V x V y B0(x, y))"), Clause.parseWithQuantifier("(E x V y B0(x, y) | ~B0(y, y))"));
    }

    private static void connectedComponents() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        JoiningFilter filter = generator.connectedComponents();
        assert filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x B0(x, y))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x B0(x, y))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x ~B0(x, y))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x ~B0(x, x) | U0(x))"));
        assert !filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x U0(x))"));
        assert !filter.test(SentenceState.parse("(V x ~B0(x, x))"), Clause.parseWithQuantifier("(V x E y U0(x) | ~U0(y))"));
    }

    private static void disjunctiveClauses() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("B0", 2), Predicate.create("U0", 1)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        JoiningFilter filter = generator.disjunctiveClauses();
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x B0(x, y))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x ~B0(x, y))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x ~B0(x, x))"));
        assert !filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x B0(x, x))"));
        assert !filter.test(SentenceState.parse("(V x ~B0(x, x))"), Clause.parseWithQuantifier("(V x ~B0(x, x))"));
        assert !filter.test(SentenceState.parse("(V x V y ~B0(y, x))"), Clause.parseWithQuantifier("(V x V y ~B0(y, x))"));
        assert !filter.test(SentenceState.parse("(V x V y ~B0(x, y))"), Clause.parseWithQuantifier("(V x V y ~B0(y, x))"));
        assert filter.test(SentenceState.parse("(E x E y U0(x) | ~B0(x, y))"), Clause.parseWithQuantifier("(E x E y U0(x) | ~B0(y, x))"));
    }

    private static void maxClauses() {
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        JoiningFilter filter = generator.maxClauses(2);
        assert filter.test(SentenceState.parse("(V x B0(x, x))"), Clause.parseWithQuantifier("(V x B0(x, y))"));
        assert filter.test(SentenceState.parse(""), Clause.parseWithQuantifier("(V x ~B0(x, y))"));
        assert !filter.test(SentenceState.parse("(V x B0(x, x)) & (E x U0(x))"), Clause.parseWithQuantifier("(V x ~B0(x, x))"));
    }


    private static void contradictionTest(Path prover9) {
        if (!prover9.toFile().exists()) {
            System.out.println("Cannot proceed with this test since the path does not exists\t" + prover9);
            return;
        }
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        SingleFilter<SentenceState> filter = generator.contradictionFilter(prover9, 30);
        assert filter.test(SentenceState.parse("(V x V y B0(x, x))"));
        assert filter.test(SentenceState.parse("(V x V y B0(x, x) | B0(y, y))"));
        assert filter.test(SentenceState.parse("(V x V y B0(x, x) | ~B0(y, y))"));
        assert filter.test(SentenceState.parse("(E=1 x B0(x, x) | ~B0(x, x))"));
        assert filter.test(SentenceState.parse("(V x B0(x, x) | ~B0(x, x))"));
        assert filter.test(SentenceState.parse("(V x E y B0(x, x) | ~B0(x, x) | B0(x, y))"));
        assert filter.test(SentenceState.parse("(E x E y ~B0(x, x) | B0(y, y))"));

        assert filter.test(SentenceState.parse("(E x ~B0(x, x)) & (E x B0(x, x))"));
        assert !filter.test(SentenceState.parse("(V x ~B0(x, x)) & (V x B0(x, x))"));
    }


    private static void naiveTautologyFilterTest() {
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        SingleFilter<Clause> filter = generator.naiveTautologyFilter();
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x))"));
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x) | B0(y, y))"));
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x) | ~B0(y, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x B0(x, x) | ~B0(x, x))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x E y B0(x, x) | ~B0(x, x) | B0(x, y))"));
        assert filter.test(Clause.parseWithQuantifier("(E=1 x B0(x, x) | ~B0(x, x))"));
    }

    private static void tautologyFilterTest(Path prover9) {
        if (!prover9.toFile().exists()) {
            System.out.println("Cannot proceed with this test since the path does not exists\t" + prover9);
            return;
        }
        LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        SingleFilter<Clause> filter = generator.tautologyFilter(prover9, 30);
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x))"));
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x) | B0(y, y))"));
        assert filter.test(Clause.parseWithQuantifier("(V x V y B0(x, x) | ~B0(y, y))"));
        assert filter.test(Clause.parseWithQuantifier("(E=1 x B0(x, x) | ~B0(x, x))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x B0(x, x) | ~B0(x, x))"));
        assert !filter.test(Clause.parseWithQuantifier("(V x E y B0(x, x) | ~B0(x, x) | B0(x, y))"));
        assert !filter.test(Clause.parseWithQuantifier("(E x E y ~B0(x, x) | B0(y, y))"));
    }

    private static void clausesGeneratorTest() {
        allUnaryWithPrune();
        allUnary();
        unaryWithTautology();
        refinementsConnectivity();
    }

    private static void refinementsConnectivity() {
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> triple = QuantifiersGenerator.generateQuantifiers(true, 1, true, false, variables);
        List<Literal> literals = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("B0", 2)));
        ClausesGenerator generator = new ClausesGenerator(null, null, null, null, null);
        Clause base = Clause.parseWithQuantifier("(V x E y B0(x, x) | B0(y, y))");
        List<Clause> clauses = generator.refinements(base, literals, triple.getR(), triple.getS(), triple.getT());
        List<String> expectedOutput = Sugar.list(
                "(V x E y B0(x, x) | B0(y, y) | ~B0(x, x))", "(V x E y B0(x, x) | B0(y, y) | ~B0(y, y))",

                "(V x E y B0(x, x) | B0(y, y) | B0(x, y))", "(V x E y B0(x, x) | B0(y, y) | ~B0(x, y))",
                "(E x V y B0(x, x) | B0(y, y) | B0(y, x))", "(E x V y B0(x, x) | B0(y, y) | ~B0(y, x))",

                "(V x E y B0(x, x) | B0(y, y) | B0(y, x))", "(V x E y B0(x, x) | B0(y, y) | ~B0(y, x))",
                "(E x V y B0(x, x) | B0(y, y) | B0(x, y))", "(E x V y B0(x, x) | B0(y, y) | ~B0(x, y))"
        );

        List<Clause> expectedClauses = expectedOutput.stream().map(Clause::parseWithQuantifier).toList();
        List<String> cannonOutput = clauses.stream().map(Clause::getCannonic).sorted().toList();
        List<String> cannonExpected = expectedClauses.stream().map(Clause::getCannonic).sorted().toList();
        /*
        clauses.stream().map(c -> new Pair<>(c.getCannonic(), c)).sorted(Comparator.comparing(Pair::getR)).forEach(p -> System.out.println(p.getR() + "\t" + p.getS().toFOL()));
        System.out.println("* / *");

        List<Pair<String, Clause>> a1 = clauses.stream().map(c -> new Pair<>(c.getCannonic(), c)).sorted(Comparator.comparing(Pair::getR)).toList();
        List<Pair<String, Clause>> a2 = expectedClauses.stream().map(c -> new Pair<>(c.getCannonic(), c)).sorted(Comparator.comparing(Pair::getR)).toList();
        a1.stream().map(Pair::getR).sorted().forEach(System.out::println);
        System.out.println("---");
        a2.stream().map(Pair::getR).sorted().forEach(System.out::println);

        System.out.println(clauses.size());
        System.out.println(expectedClauses.size());

        for (int idx = 0; idx < a1.size(); idx++) {
            Pair<String, Clause> a = a1.get(idx);
            Pair<String, Clause> b = a2.get(idx);
            boolean cannonEquals = a.getR().equals(b.getR());
            boolean clausesEquals = a.getS().equals(b.getS());
//            if (!clausesEquals) {
//                System.out.println("debug here!");
//            }
            System.out.println(cannonEquals + "\t" + clausesEquals
                    + "\t" + a.getS().toFOL() + " : " + b.getS().toFOL()
                    + "\t" + a.getR() + " : " + b.getR());
        }
        */

        assert cannonOutput.equals(cannonExpected);
        assert Sugar.setFromCollections(clauses).equals(Sugar.setFromCollections(expectedClauses));
    }

    private static void unaryWithTautology() {
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> triple = QuantifiersGenerator.generateQuantifiers(true, 1, true, true, variables);
        List<Literal> literals = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1)));
        ClausesGenerator generator = new ClausesGenerator(literals, triple.getR(), triple.getS(), triple.getT(), null);
        List<Clause> clauses = generator.generateClauses(Sugar.list(generator.maxLiterals(2),
                generator.maxLiteralsPerCountingClause(2),
                generator.tautologyFilter(Paths.get("D:\\Program Files (x86)\\Prover9-Mace4\\bin-win32\\prover9.exe"), 30)));
        List<String> expectedOutput = Sugar.list("(V x U0(x))", "(V x ~U0(x))", "(E x U0(x))", "(E x ~U0(x))", "(E=1 x U0(x))", "(E=1 x ~U0(x))",
                // "(V x U0(x))"
                "(V x V y U0(x) | U0(y))", "(V x V y U0(x) | ~U0(y))", "(V x V y ~U0(x) | ~U0(y))",
                "(V x E=1 y U0(x) | U0(y))", "(V x E=1 y U0(x) | ~U0(y))", "(V x E=1 y ~U0(x) | U0(y))", "(V x E=1 y ~U0(x) | ~U0(y))",
                // "(E x U0(x))"
                "(E x V y U0(x) | U0(y))", "(E x V y ~U0(x) | ~U0(y))",
                "(E x E y U0(x) | U0(y))", "(E x E y ~U0(x) | ~U0(y))", // "(E x E y ~U0(x) | U0(y))",
                "(E x E=1 y U0(x) | U0(y))", "(E x E=1 y U0(x) | ~U0(y))",
                "(E x E=1 y ~U0(x) | U0(y))", "(E x E=1 y ~U0(x) | ~U0(y))", // TODO in future, these two are redundant wrt the two previous since decomposability
                // "(E=1 x U0(x))"
                "(E=1 x U0(x) | ~U0(x))", // we do not test counting clauses for tautology now
                "(E=1 x V y U0(x) | U0(y))", "(E=1 x V y U0(x) | ~U0(y))", "(E=1 x V y ~U0(x) | U0(y))", "(E=1 x V y ~U0(x) | ~U0(y))",
                "(E=1 x E y U0(x) | U0(y))", "(E=1 x E y U0(x) | ~U0(y))", "(E=1 x E y ~U0(x) | U0(y))", "(E=1 x E y ~U0(x) | ~U0(y))",                // TODO in future, these are redundant since decomposability
                "(E=1 x E=1 y U0(x) | U0(y))", "(E=1 x E=1 y U0(x) | ~U0(y))", "(E=1 x E=1 y ~U0(x) | ~U0(y))"
                // the rest is either not canonic or non-tautology
                // e.g. tautologies "(E x E y U0(x) | ~U0(y))", "(E x V y U0(x) | ~U0(y))", "(E x V y ~U0(x) | U0(y))"
        );
        List<Clause> expectedClauses = expectedOutput.stream().map(Clause::parseWithQuantifier).toList();

        /*
        clauses.stream().map(Clause::getCannonic).sorted().forEach(System.out::println);
        System.out.println("---");
        expectedClauses.stream().map(Clause::getCannonic).sorted().forEach(System.out::println);

        List<Pair<String, Clause>> a1 = clauses.stream().map(c -> new Pair<>(c.getCannonic(), c)).sorted(Comparator.comparing(Pair::getR)).toList();
        List<Pair<String, Clause>> a2 = expectedClauses.stream().map(c -> new Pair<>(c.getCannonic(), c)).sorted(Comparator.comparing(Pair::getR)).toList();
        for (int idx = 0; idx < a1.size(); idx++) {
            Pair<String, Clause> a = a1.get(idx);
            Pair<String, Clause> b = a2.get(idx);
            boolean cannonEquals = a.getR().equals(b.getR());
            boolean clausesEquals = a.getS().equals(b.getS());
            if(!clausesEquals){
                System.out.println("debug here!");
            }
            System.out.println(cannonEquals + "\t" + clausesEquals + "\t" + a.getS() + " : " + b.getS() + "\t" + a.getR() + " : " + b.getR());
        }
        */

        List<String> cannonicClauses = clauses.stream().map(Clause::getCannonic).sorted().toList();
        List<String> cannonicExpected = expectedClauses.stream().map(Clause::getCannonic).sorted().toList();
        assert cannonicClauses.equals(cannonicExpected);
    }

    private static void allUnaryWithPrune() {
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> triple = QuantifiersGenerator.generateQuantifiers(false, 0, false, false, variables);
        List<Literal> literals = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1)));
        ClausesGenerator generator = new ClausesGenerator(literals, triple.getR(), triple.getS(), triple.getT(), null);
        List<Clause> clauses = generator.generateClauses(Sugar.list(
                        generator.maxLiterals(4),
                        generator.maxLiteralsPerCountingClause(1)),
                2);
        List<String> expectedOutput = Sugar.list("(V x U0(x))", "(V x ~U0(x))",
                "(V x U0(x) | ~U0(x))", "(V x V y U0(x) | U0(y))", "(V x V y U0(x) | ~U0(y))", "(V x V y ~U0(x) | ~U0(y))"
//                ,"(V x V y U0(x) | U0(y) | ~U0(x))", "(V x V y U0(x) | ~U0(y) | ~U0(x))",
//                "(V x V y U0(x) | U0(y) | ~U0(x) | ~U0(y))"
                // these are not canonic: "(V x V y ~U0(x) | U0(y))", "(V x V y U0(y) | ~U0(x) | ~U0(y))", "(V x V y U0(y) | U0(x) | ~U0(y))",
        );

        List<String> expectedClauses = expectedOutput.stream().map(Clause::parseWithQuantifier)
                .map(Clause::getCannonic)
                .sorted()
                .toList();

        List<String> clausesOutput = clauses.stream().map(Clause::getCannonic).sorted().toList();

        if (!clausesOutput.equals(expectedClauses)) {
            System.out.println("expecting");
            expectedClauses.forEach(c -> System.out.println(c));
            System.out.println("got");
            clausesOutput.forEach(c -> System.out.println(c));
        }

        assert clausesOutput.equals(expectedClauses);
    }


    private static void allUnary() {
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> triple = QuantifiersGenerator.generateQuantifiers(false, 0, false, false, variables);
        List<Literal> literals = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1)));
        ClausesGenerator generator = new ClausesGenerator(literals, triple.getR(), triple.getS(), triple.getT(), null);
        List<Clause> clauses = generator.generateClauses(Sugar.list(generator.maxLiterals(4), generator.maxLiteralsPerCountingClause(1)));
        List<String> expectedOutput = Sugar.list("(V x U0(x))", "(V x ~U0(x))",
                "(V x U0(x) | ~U0(x))", "(V x V y U0(x) | U0(y))", "(V x V y U0(x) | ~U0(y))", "(V x V y ~U0(x) | ~U0(y))",
                "(V x V y U0(x) | U0(y) | ~U0(x))", "(V x V y U0(x) | ~U0(y) | ~U0(x))",
                "(V x V y U0(x) | U0(y) | ~U0(x) | ~U0(y))"
                // these are not canonic: "(V x V y ~U0(x) | U0(y))", "(V x V y U0(y) | ~U0(x) | ~U0(y))", "(V x V y U0(y) | U0(x) | ~U0(y))",
        );
        List<Clause> expectedClauses = expectedOutput.stream().map(Clause::parseWithQuantifier).collect(Collectors.toList());

        assert expectedClauses.stream().map(Clause::getCannonic).sorted().toList()
                .equals(clauses.stream().map(Clause::getCannonic).sorted().toList());
        //assert clauses.equals(expectedClauses);
    }

    private static void literalsGeneratorTest() {
        List<Literal> literals0 = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1)));
        checkLiterals(literals0, 4); // 2 * (1*2)
        List<Literal> literals1 = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("B0", 2)));
        checkLiterals(literals1, 8); // 2 * (1*2^2)
        List<Literal> literals2 = LiteralsGenerator.generate(variables, Sugar.list(Predicate.create("U0", 1), Predicate.create("B0", 2)));
        checkLiterals(literals2, 12); // 2 * (1*2 + 1*2^2)

        // just a test that variable-set cache works as expected
        List<Set<Variable>> in = Sugar.list();
        for (Literal literal : literals2) {
            boolean found = false;
            Set<Variable> variableSet = literal.getVariableSet();
            for (Set<Variable> set : in) {
                if (set == variableSet) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                in.add(variableSet);
            }
        }
        assert 3 == in.size();

    }

    private static void checkLiterals(List<Literal> literals, int count) {
        assert literals.size() == Sugar.setFromCollections(literals).size();
        assert count == literals.size();
        for (Literal literal : literals) {
//            System.out.println("---");
//            System.out.println(literal + "\t" + literal.hashCode());
//            System.out.println(literal.getNegatedPair() + "\t" + literal.getNegatedPair().hashCode());
//            System.out.println(literal.getNegatedPair().getNegatedPair() + "\t" + literal.getNegatedPair().getNegatedPair().hashCode());
            assert literal == literal.getNegatedPair().getNegatedPair();
            assert literal == literal.getFlipped().getFlipped();
            assert literal == literal.getMirror().getMirror();
            assert literal == literal.getMirror().getFlipped().getNegatedPair().getMirror().getFlipped().getNegatedPair();
            assert literal == literal.getMirror().getNegatedPair().getFlipped().getNegatedPair().getMirror().getFlipped();
            assert literal == literal.getFlipped().getMirror().getFlipped().getNegatedPair().getMirror().getNegatedPair();
            assert literal == literal.getNegatedPair().getMirror().getFlipped().getMirror().getFlipped().getNegatedPair();
            assert literal == literal.getNegatedPair().getMirror().getFlipped().getNegatedPair().getMirror().getFlipped();
        }
    }

    private static void quantifiersMirrorTest() {
        Triple<List<Quantifier>, MultiList<Quantifier, Quantifier>, Map<Quantifier, Quantifier>> triple = QuantifiersGenerator.generateQuantifiers(true, 1, true, true, variables);
        Map<Quantifier, Quantifier> mirrors = triple.getT();
        Map<Quantifier, Quantifier> expectedOutput = new HashMap<>();
        expectedOutput.put(Quantifier.parse("V x E y"), Quantifier.parse("E x V y"));
        expectedOutput.put(Quantifier.parse("E x V y"), Quantifier.parse("V x E y"));

        expectedOutput.put(Quantifier.parse("V x E=1 y"), Quantifier.parse("E=1 x V y"));
        expectedOutput.put(Quantifier.parse("E=1 x V y"), Quantifier.parse("V x E=1 y"));

        expectedOutput.put(Quantifier.parse("E=1 x E y"), Quantifier.parse("E x E=1 y"));
        expectedOutput.put(Quantifier.parse("E x E=1 y"), Quantifier.parse("E=1 x E y"));

        // expectedOutput.put(Quantifier.parse("E=1 x E=1 y"), Quantifier.parse("E=1 x E=1 y")); this won't be there because we're gonna take care of this in isomorphism checking :)

        assert compareMaps(mirrors, expectedOutput);
    }

    private static boolean compareMaps(Map<Quantifier, Quantifier> output, Map<Quantifier, Quantifier> expectedOutput) {
        /*
        output.entrySet().stream().map(e -> e.getKey() + " : " + e.getValue()).sorted().forEach(System.out::println);
        System.out.println("---");
        expectedOutput.entrySet().stream().map(e -> e.getKey() + " : " + e.getValue()).sorted().forEach(System.out::println);
        */
        if (!output.keySet().equals(expectedOutput.keySet())) {
            return false;
        }
        for (Map.Entry<Quantifier, Quantifier> entry : output.entrySet()) {
            if (!expectedOutput.get(entry.getKey()).equals(entry.getValue())) {
                return false;
            }
        }
        return true;
    }

    private static void quantifiersSuccessorsTest() {
        MultiList<Quantifier, Quantifier> m0 = new MultiList<>();
        m0.putAll(Quantifier.parse("V x"), Sugar.list(Quantifier.parse("V x V y")));
        quantifiersTest(false, 0, false, variables, m0);

        MultiList<Quantifier, Quantifier> m1 = new MultiList<>();
        m1.putAll(Quantifier.parse("V x"), Sugar.list(Quantifier.parse("V x V y"), Quantifier.parse("V x E y")));
        m1.putAll(Quantifier.parse("E x"), Sugar.list(Quantifier.parse("E x V y"), Quantifier.parse("E x E y")));
        quantifiersTest(true, 0, false, variables, m1);

        MultiList<Quantifier, Quantifier> m2 = new MultiList<>();
        m2.putAll(Quantifier.parse("V x"), Sugar.list(Quantifier.parse("V x V y"), Quantifier.parse("V x E y"), Quantifier.parse("V x E=1 y")));
        m2.putAll(Quantifier.parse("E x"), Sugar.list(Quantifier.parse("E x V y"), Quantifier.parse("E x E y")));
        m2.putAll(Quantifier.parse("E=1 x"), Sugar.list(Quantifier.parse("E=1 x V y")));
        quantifiersTest(true, 1, false, variables, m2);

        MultiList<Quantifier, Quantifier> m3 = new MultiList<>();
        m3.putAll(Quantifier.parse("V x"), Sugar.list(Quantifier.parse("V x V y"), Quantifier.parse("V x E y"), Quantifier.parse("V x E=1 y")));
        m3.putAll(Quantifier.parse("E x"), Sugar.list(Quantifier.parse("E x V y"), Quantifier.parse("E x E y"), Quantifier.parse("E x E=1 y")));
        m3.putAll(Quantifier.parse("E=1 x"), Sugar.list(Quantifier.parse("E=1 x V y"), Quantifier.parse("E=1 x E y"), Quantifier.parse("E=1 x E=1 y")));
        quantifiersTest(true, 1, true, variables, m3);

        MultiList<Quantifier, Quantifier> m4 = new MultiList<>();
        m4.putAll(Quantifier.parse("V x"), Sugar.list(Quantifier.parse("V x V y"), Quantifier.parse("V x E y"), Quantifier.parse("V x E=1 y"), Quantifier.parse("V x E=2 y")));
        m4.putAll(Quantifier.parse("E x"), Sugar.list(Quantifier.parse("E x V y"), Quantifier.parse("E x E y")));
        m4.putAll(Quantifier.parse("E=1 x"), Sugar.list(Quantifier.parse("E=1 x V y")));
        m4.putAll(Quantifier.parse("E=2 x"), Sugar.list(Quantifier.parse("E=2 x V y")));
        quantifiersTest(true, 2, false, variables, m4);

        MultiList<Quantifier, Quantifier> m5 = new MultiList<>();
        m5.putAll(Quantifier.parse("V x"), Sugar.list(Quantifier.parse("V x V y"), Quantifier.parse("V x E y"), Quantifier.parse("V x E=1 y"), Quantifier.parse("V x E=2 y")));
        m5.putAll(Quantifier.parse("E x"), Sugar.list(Quantifier.parse("E x V y"), Quantifier.parse("E x E y"), Quantifier.parse("E x E=1 y"), Quantifier.parse("E x E=2 y")));
        m5.putAll(Quantifier.parse("E=1 x"), Sugar.list(Quantifier.parse("E=1 x V y"), Quantifier.parse("E=1 x E y"), Quantifier.parse("E=1 x E=1 y"), Quantifier.parse("E=1 x E=2 y")));
        m5.putAll(Quantifier.parse("E=2 x"), Sugar.list(Quantifier.parse("E=2 x V y"), Quantifier.parse("E=2 x E y"), Quantifier.parse("E=2 x E=1 y"), Quantifier.parse("E=2 x E=2 y")));
        quantifiersTest(true, 2, true, variables, m5);
    }

    private static void quantifiersTest(boolean quantifiers, int k, boolean doubleExists, List<Variable> variables, MultiList<Quantifier, Quantifier> expectedResult) {
        MultiList<Quantifier, Quantifier> tree = QuantifiersGenerator.generateQuantifiers(quantifiers, k, k > 0, doubleExists, variables).getS();
//        System.out.println("tree");
//        tree.entrySet().forEach(e -> System.out.println(e.getKey() + " -> " + e.getValue().stream().map(Quantifier::toString).collect(Collectors.joining(", "))));
//        System.out.println("expected");
//        expectedResult.entrySet().forEach(e -> System.out.println(e.getKey() + " -> " + e.getValue().stream().map(Quantifier::toString).collect(Collectors.joining(", "))));
        assert compareMultiLists(tree, expectedResult);
    }

    private static boolean compareMultiLists(MultiList<Quantifier, Quantifier> first, MultiList<Quantifier, Quantifier> second) {
        if (!first.keySet().equals(second.keySet())) {
            return false;
        }
        for (Quantifier quantifier : first.keySet()) {
            if (!first.get(quantifier).equals(second.get(quantifier))) {
                return false;
            }
        }
        return true;
    }

    private static void quantifiersCountsTest() {
        List<Variable> variables = Sugar.list(Variable.construct("x"), Variable.construct("y"));
        // there are two of them Vx, VxVy
        assert 2 == Sugar.setFromCollections(QuantifiersGenerator.generateQuantifiers(false, 0, false, false, variables).r).size();

        // there are 6 of them: Vx, Ex, VxVy, VxEx, ExVy, ExEy
        assert 6 == Sugar.setFromCollections(QuantifiersGenerator.generateQuantifiers(true, 0, false, false, variables).r).size();

        // there are 9 of them: Vx, Ex, VxVy, VxEx, ExVy, ExEy, E=1x, VxE=1y, E=1xVy
        assert 9 == Sugar.setFromCollections(QuantifiersGenerator.generateQuantifiers(true, 1, true, false, variables).r).size();

        // there are 12 of them: Vx, Ex, VxVy, VxEx, ExVy, ExEy, E=1x, VxE=1y, E=1xVy, E=1xEy, ExE=1y, E=1xE=1y
        assert 12 == Sugar.setFromCollections(QuantifiersGenerator.generateQuantifiers(true, 1, true, true, variables).r).size();

        // there are 12 of them: Vx, Ex, VxVy, VxEx, ExVy, ExEy, E=1x, VxE=1y, E=1xVy, E=2x, VxE=2y, E=2xVy
        assert 12 == Sugar.setFromCollections(QuantifiersGenerator.generateQuantifiers(true, 2, true, false, variables).r).size();

        // there are be 20 of them
        assert 20 == Sugar.setFromCollections(QuantifiersGenerator.generateQuantifiers(true, 2, true, true, variables).r).size();
    }


}
