package logicStuff;

import ida.ilp.logic.*;
import ida.utils.Sugar;
import ida.utils.collections.MultiList;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by martin.svatos on 1. 3. 2018.
 */
public class Typing {


    private final Set<Literal> predicatesDefinition;
    private final List<Pair<String, Set<Constant>>> types;
    private final String UNARY_PREDICATE_PREFIX = "pred_";
    private final Map<Predicate, List<String>> predicatesWithTypes;

    // quick hack for constants only!
    public Typing(Set<Literal> predicatesDefinition, List<Pair<String, Set<Constant>>> types) {
        this.predicatesDefinition = predicatesDefinition;
        this.types = types;
        Map<Predicate, List<String>> map = new HashMap<>();
        predicatesDefinition.forEach(literal -> {
            Predicate predicate = Predicate.create(literal.predicate(), literal.arity());
            List<String> predicateType = Arrays.stream(literal.arguments())
                    .map(Term::name)
                    .collect(Collectors.toList());
            map.put(predicate, predicateType);
        });
        this.predicatesWithTypes = map;
    }

    public Set<Literal> getPredicatesDefinition() {
        return predicatesDefinition;
    }

    public Set<String> getPredicatesDefinitionAsAlchemyString() {
        return predicatesDefinition.stream()
                .map(literal -> {
                    List<Constant> terms = Arrays.stream(literal.arguments())
                            .map(constant -> Constant.construct(constant.name().substring(0, 1).toLowerCase() + constant.name().substring(1)))
                            .collect(Collectors.toList());
                    return (new Literal(literal.predicate(), terms)).toString();
                })
                .collect(Collectors.toSet());
    }

    public List<Pair<String, Set<Constant>>> getTypes() {
        return types;
    }

    public List<Pair<String, Set<String>>> getTypesAsAlchemy() {
        return types.stream().map(pair -> new Pair<>(pair.r,
                pair.s.stream().map(c -> c.name().substring(0, 1).toUpperCase() + c.name().substring(1)).collect(Collectors.toSet())))
                .collect(Collectors.toList());
    }

    public String getTypesAsAlchemyString() {
        StringBuilder sb = new StringBuilder();
        this.getTypesAsAlchemy().forEach(pair -> {
            sb.append(pair.r + " = {" + String.join(" , ", pair.s) + "}" + "\n");
        });
        return sb.toString();
    }

    // considering constants only, no variables
    public static Typing create(Clause db) {
        Map<String, Integer> predicates = new HashMap<>();
        for (Literal literal : db.literals()) {
            if (predicates.containsKey(literal.predicate()) && predicates.get(literal.predicate()) != literal.arity()) {
                System.err.println("Can't do sir. There are several predicates with the same name and different arity and this is not supported right now.");
                return null;
            }
            predicates.put(literal.predicate(), literal.arity());
        }

        Map<String, String> mapping = new HashMap<>();
        List<Pair<String, Set<Constant>>> initial = Sugar.list();
        MultiList<Pair<String, Integer>, Constant> types = typing(db);

        types.entrySet().forEach(entry -> initial.add(new Pair<String, Set<Constant>>(entry.getKey().r + "_" + entry.getKey().s, new HashSet<>(entry.getValue()))));
        List<Pair<String, Set<Constant>>> result = Sugar.list();
        Set<Integer> merged = Sugar.set();

        for (int idxFirst = 0; idxFirst < initial.size(); idxFirst++) {
            if (merged.contains(idxFirst)) {
                continue;
            }
            Pair<String, Set<Constant>> first = initial.get(idxFirst);
            for (int idxSecond = idxFirst + 1; idxSecond < initial.size(); idxSecond++) {
                Pair<String, Set<Constant>> second = initial.get(idxSecond);
                Set<Constant> intersection = new HashSet<>(first.s);
                intersection.retainAll(second.s);
                if (!intersection.isEmpty()) {
                    merged.add(idxSecond);
                    first.s.addAll(second.s);
                    mapping.put(second.r, first.r);
                }
            }
            result.add(first);
        }

        Set<Literal> definitions = Sugar.set();
        predicates.keySet().forEach(predicate -> {
            List<Variable> terms = IntStream.range(0, predicates.get(predicate))
                    .mapToObj(idx -> {
                        String key = predicate + "_" + idx;
                        if (mapping.containsKey(key)) {
                            return Variable.construct(mapping.get(key));
                        }
                        return Variable.construct(key);
                    })
                    .collect(Collectors.toList());
            definitions.add(new Literal(predicate, terms));
        });

        return new Typing(definitions, result);
    }

    public String getPredicatesAsAlchemyString() {
        return String.join("\n", getPredicatesDefinitionAsAlchemyString()) + "\n";
    }

    public String getUnaryObservedPredicateRockItDefinitions() {
        return generateUnaryPredicatesWithTypes().stream()
                .map(literal -> "*" + literal.toString())
                .collect(Collectors.joining("\n"));
    }

    public List<Literal> generateUnaryPredicatesWithTypes() {
        return getTypes().stream()
                .map(pair -> new Literal(UNARY_PREDICATE_PREFIX + pair.r, Variable.construct(pair.r)))
                .collect(Collectors.toList());
    }

    // constants starting with lower case
    public List<Literal> generateUnaryEvidence() {
        return getTypes().stream()
                .flatMap(pair -> pair.s.stream().map(constant -> new Literal(UNARY_PREDICATE_PREFIX + pair.r, Sugar.list(constant))))
                .collect(Collectors.toList());
    }

    public String generateUnaryEvidenceForRockIt() {
        return generateUnaryEvidence().stream()
                .map(literal -> new Literal(literal.predicate(), literal.isNegated(), rockItConstants(literal.arguments())))
                .map(literal -> literal.toString())
                .collect(Collectors.joining("\n"));
    }

    // also, only constant supoorted; in fact returns List<Constant>
    private List<Term> rockItConstants(Term[] arguments) {
        return Arrays.stream(arguments)
                .map(term -> Constant.construct("\"" + term.name().substring(0, 1).toUpperCase() + term.name().substring(1) + "\""))
                .collect(Collectors.toList());
    }

    /**
     * generates priors with upper letters
     *
     * @return
     */
    public List<Clause> generatePriors() {
        return generatePriors(true);
    }

    public List<Clause> generatePriors(boolean upperCase) {
        return predicatesDefinition.stream()
                .map(literal -> {
                    List<Variable> variables = IntStream.range(0, literal.arity())
                            .mapToObj(idx -> {
                                if (upperCase) {
                                    return Variable.construct("V" + idx);
                                } else {
                                    return Variable.construct("v" + idx);
                                }
                            })
                            .collect(Collectors.toList());
                    return new Clause(new Literal(literal.predicate(), variables));
                })
                .collect(Collectors.toList());
    }


    public List<Clause> filterTypeContradictions(List<Clause> rules) {
        return rules.stream()
                .filter(this::filterType)
                .collect(Collectors.toList());
    }

    /**
     * Returns true iff there is not any variable taking on multiple values.
     * <p>
     * E.g., having predicates with type (Alchemy/rockIt notation)
     * complex(protein, complex)
     * and a rule
     * complex(x,y) v complex(y,x)
     * returns false.
     *
     * @param clause
     * @return
     */
    private boolean filterType(Clause clause) {
        Map<String, String> variableToType = new HashMap<>();
        for (Literal literal : clause.literals()) {
            List<String> predicate = this.predicatesWithTypes.get(Predicate.create(literal.predicate(), literal.arity()));
            for (int argIdx = 0; argIdx < literal.arity(); argIdx++) {
                String currentType = predicate.get(argIdx);
                String currentVariable = literal.get(argIdx).name(); // this should be variable each time
                if (variableToType.containsKey(currentVariable) && !currentType.equals(variableToType.get(currentVariable))) {
                    return false;
                } else if (!variableToType.containsKey(currentVariable)) {
                    variableToType.put(currentVariable, currentType);
                }
            }
        }
        return true;
    }


    /*tady to pouzit pro typy !
        (predicate-pozice,constanta)
        exituje intesection mezi tim co muze byt v prvnim a druhym argumentu ????*/
    public static MultiList<Pair<String, Integer>, Constant> typing(Clause db) {
        MultiMap<Pair<String, Integer>, Constant> mm = new MultiMap<Pair<String, Integer>, Constant>();
        for (Literal l : db.literals()) {
            for (int i = 0; i < l.arity(); i++) {
                mm.put(new Pair<String, Integer>(l.predicate(), i), (Constant) l.get(i));
            }
        }
        MultiMap<Pair<String, Integer>, Constant> retVal = new MultiMap<Pair<String, Integer>, Constant>();
        for (Map.Entry<Pair<String, Integer>, Set<Constant>> entry1 : mm.entrySet()) {
            for (Map.Entry<Pair<String, Integer>, Set<Constant>> entry2 : mm.entrySet()) {
                if (!Sugar.intersection(entry1.getValue(), entry2.getValue()).isEmpty()) {
                    retVal.putAll(entry1.getKey(), entry1.getValue());
                    retVal.putAll(entry1.getKey(), entry2.getValue());
                    retVal.putAll(entry2.getKey(), entry1.getValue());
                    retVal.putAll(entry2.getKey(), entry2.getValue());
                }
            }
        }
        return retVal.toMultiList();
    }

}


