package ida.ilp.logic.special;

import ida.ilp.logic.*;
import ida.utils.Combinatorics;
import ida.utils.Sugar;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by martin.svatos on 13. 3. 2018.
 */
public class BruteForceICW {
    private final Clause clause;
    private final String canonical;
    private final int hashCode;

    private BruteForceICW(Clause clause) {
        this.clause = clause;
        String cano = canonical(clause);
        this.hashCode = cano.hashCode();
        this.canonical = cano;
    }

    public Clause getOriginalClause() {
        return clause;
    }

    public String getCanonical() {
        return canonical;
    }

    private static String canonical(Clause c) {
        String min = null;
        Set<Variable> oldVars = LogicUtils.variables(c);
        if (oldVars.isEmpty()) {
            return canon(c.literals());
        }
//        System.out.println("input\t" + c);
        List<Variable> freshVars = IntStream.range(0, oldVars.size()).mapToObj(i -> Variable.construct("X" + i)).collect(Collectors.toList());
        for (List<Variable> variation : Combinatorics.variations(oldVars, oldVars.size())) {
            Map<Variable, Variable> substitution = IntStream.range(0, oldVars.size())
                    .boxed()
                    .collect(Collectors.toMap(variation::get, freshVars::get));
//            System.out.println(substitution);
            String canonical = canon(LogicUtils.substitute(c, substitution).literals());
//            System.out.println("\t" + canonical);
            if (null == min || min.compareTo(canonical) > 0) {
                min = canonical;
            }
        }
        return min;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        BruteForceICW that = (BruteForceICW) o;

        return canonical != null ? canonical.equals(that.canonical) : that.canonical == null;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    private static String canon(Set<Literal> literals) {
        return literals.stream().map(Literal::toString).sorted().collect(Collectors.joining(","));
    }


    public static BruteForceICW create(Clause c) {
        return new BruteForceICW(c);
    }

//    private static void tCano() {
//        SMU smu = SMU.create();
//        Clause l1 = Clause.parse("p(V2, V2, f2(V6, V5))");
//        Clause l2 = Clause.parse("p(V2, V2, f2(V1, V5))");
//        System.out.println("l1\n" + l1 + "\n" + smu.canonical(l1));
//        System.out.println("l2\n" + l2 + "\n" + smu.canonical(l2));
//
//    }


    public static void main(String[] args) {
        Clause c1 = Clause.parse("p(X,X,c(A,B))");
        Clause c2 = Clause.parse("p(A,A,c(DAD,C))");

        BruteForceICW b1 = BruteForceICW.create(c1);
        BruteForceICW b2 = BruteForceICW.create(c2);

        System.out.println(b1.getCanonical());
        System.out.println(b2.getCanonical());

        Set<BruteForceICW> s = Sugar.set();
        s.add(b1);
        s.add(b2);
        System.out.println("size s\t" + s.size());
    }
}
