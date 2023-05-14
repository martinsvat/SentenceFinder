package ida.ilp.logic;

import ida.utils.Sugar;
import ida.utils.tuples.Pair;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Supporting class for computing Herbrand base of function-free FOL.
 * <p>
 * Created by martin.svatos on 30. 10. 2017.
 */
public class HerbrandBase {

    /**
     * Generates Herbrand base of function-free theory from given theory.
     *
     * @param theory
     * @return
     */
    public static Set<Literal> herbrandBase(Collection<Clause> theory, Map<Pair<Predicate, Integer>, String> typing) {
        return herbrandBaseFromPair(LogicUtils.predicates(theory),
                LogicUtils.constants(theory), typing);
    }

    public static Set<Literal> herbrandBaseFromPair(Set<Pair<String, Integer>> predicate, Set<Constant> constants, Map<Pair<Predicate, Integer>, String> typing) {
        return herbrandBase(predicate.stream()
                        .map(Predicate::create)
                        .collect(Collectors.toSet()),
                constants, typing);
    }

    public static Set<Literal> herbrandBase(Set<Predicate> predicates, Set<Constant> constants, Map<Pair<Predicate, Integer>, String> typing) {
        return predicates.stream()
                .flatMap(predicate -> {
                    Collection<Variable> variables = (null == typing || typing.keySet().size() < 1)
                            ? LogicUtils.freshVariables(Sugar.set(), predicate.getArity())
                            : LogicUtils.freshVariables(typing, predicate);
                    Literal freshLiteral = LogicUtils.newLiteral(predicate.getName(), predicate.getArity(), variables);
                    return LogicUtils.allSubstitution(freshLiteral, constants).stream();
                })
                .collect(Collectors.toSet());
    }

    public static void main(String[] args) {
        List<Clause> theory = Sugar.list("b(X,Y)", "!b(a,Y)", "c(c)").stream().map(Clause::parse).collect(Collectors.toList());
        System.out.println("theory");
        theory.forEach(System.out::println);

        System.out.println("\nliterals");
        herbrandBase(theory, null).forEach(l -> System.out.println(l));
    }


}


