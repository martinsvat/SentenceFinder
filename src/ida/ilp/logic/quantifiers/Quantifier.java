package ida.ilp.logic.quantifiers;

import ida.ilp.logic.Literal;
import ida.ilp.logic.Term;
import ida.ilp.logic.Variable;
import ida.sentences.caches.VariablesCache;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Quadruple;

import java.util.*;

public class Quantifier {

    private static final String FORALL_TOKEN = "V";
    private static final String EXISTS_TOKEN = "E";

    private static final String FORALL_PREDICATE = "Fo";
    private static final String EXISTS_PREDICATE = "Ex";

    private final TwoQuantifiers quantifiers;
    private final List<Variable> variablesOrder;
    //    private final List<Literal> literals;
    public final int firstVariableCardinality;
    public final int secondVariableCardinality;
    private final boolean isCountingQuantifier;
    public final int numberOfUsedVariables;
    private final List<Literal> decomposableRepresentation;
    private final List<Literal> fixedRepresentation;
    private final Set<Variable> usedVariables;
    private String stringRepresentation;
    private Quantifier mirrored;
    private Map<Term, Term> flipSubstitution;

    private Quantifier(TwoQuantifiers quantifiers, List<Variable> variablesOrder, int firstVariableCardinality, int secondVariableCardinality) {
        // value of -1 as a cardinality means that there is no counting at all 
        if ((TwoQuantifiers.FORALL_FORALL == quantifiers && (-1 != firstVariableCardinality || -1 != secondVariableCardinality))
                || (TwoQuantifiers.FORALL == quantifiers && (-1 != firstVariableCardinality || -1 != secondVariableCardinality))
                || (TwoQuantifiers.EXISTS_FORALL == quantifiers && (-1 != secondVariableCardinality))
                || (TwoQuantifiers.FORALL_EXISTS == quantifiers && (-1 != firstVariableCardinality))) {
            throw new IllegalStateException();
        }
        this.quantifiers = quantifiers;
        this.variablesOrder = variablesOrder;
        this.firstVariableCardinality = firstVariableCardinality;
        this.secondVariableCardinality = secondVariableCardinality;

        this.isCountingQuantifier = firstVariableCardinality > -1 || secondVariableCardinality > -1;
        this.numberOfUsedVariables = (TwoQuantifiers.FORALL == quantifiers || TwoQuantifiers.EXISTS == quantifiers) ? 1 : variablesOrder.size();
        this.usedVariables = VariablesCache.getInstance().get(1 == numberOfUsedVariables ? Sugar.set(variablesOrder.get(0)) : Sugar.setFromCollections(variablesOrder));


        // TODO I don't know if these are really needed in the new version... maybe not :)
//        this.literals = Sugar.list();
//        String firstQuantifier = ((quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.FORALL_EXISTS)) ? "Forall" : ("Exists" + (-1 != this.firstVariableCardinality ? this.firstVariableCardinality : "")));
//        String secondQuantifier = ((quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.EXISTS_FORALL)) ? "Forall" : ("Exists" + (-1 != this.secondVariableCardinality ? this.secondVariableCardinality : "")));
//        literals.add(new Literal("First" + firstQuantifier, variablesOrder.get(0)));
//        literals.add(new Literal("Second" + secondQuantifier, variablesOrder.get(1)));
//
//        this.usedVariable = new HashMap<>();
//        usedVariable.put(variablesOrder.get(0), literals.get(0));
//        usedVariable.put(variablesOrder.get(1), literals.get(1));
//
//        this.usedVariablesWithoutOrder = new HashMap<>();
//        usedVariablesWithoutOrder.put(variablesOrder.get(0), new Literal("Q" + firstQuantifier, variablesOrder.get(0)));
//        usedVariablesWithoutOrder.put(variablesOrder.get(1), new Literal("Q" + secondQuantifier, variablesOrder.get(1)));

        this.decomposableRepresentation = createRepresentation();
        List<Literal> finalFixed = this.decomposableRepresentation; // VxVy, ExEy case
        if (isCountingQuantifier) { // TODO check this!!!!
            if (firstVariableCardinality != secondVariableCardinality && TwoQuantifiers.EXISTS != quantifiers) {
                finalFixed = createFixedRepresentation(this.decomposableRepresentation);
            }// else, it's E=k x E=k y and that is switchable ;)
        } else if (TwoQuantifiers.FORALL_EXISTS == this.quantifiers || TwoQuantifiers.EXISTS_FORALL == this.quantifiers) {
            finalFixed = createFixedRepresentation(this.decomposableRepresentation);
        }
        this.fixedRepresentation = finalFixed; // this.fixedRepresentation may be null, is that a problem?
    }


    private List<Literal> createFixedRepresentation(List<Literal> decomposableRepresentation) {
        String predicate = decomposableRepresentation.get(0).predicate() + decomposableRepresentation.get(1).predicate();
        return Sugar.list(new Literal(predicate, decomposableRepresentation.get(0).get(0), decomposableRepresentation.get(1).get(0)));
    }

    private List<Literal> createRepresentation() {
        List<Literal> retVal = Sugar.list();
        String firstQuantifier = TwoQuantifiers.startsWithExists(quantifiers) ? EXISTS_PREDICATE + (this.firstVariableCardinality > 0 ? this.firstVariableCardinality : "") : FORALL_PREDICATE;
        retVal.add(new Literal(firstQuantifier, this.variablesOrder.get(0)));
        if (TwoQuantifiers.FORALL != quantifiers && TwoQuantifiers.EXISTS != quantifiers) {
            String secondQuantifier = (TwoQuantifiers.FORALL_EXISTS == quantifiers || TwoQuantifiers.EXISTS_EXISTS == quantifiers)
                    ? EXISTS_PREDICATE + (this.secondVariableCardinality > 0 ? this.secondVariableCardinality : "") : FORALL_PREDICATE;
            retVal.add(new Literal(secondQuantifier, this.variablesOrder.get(1)));
        }
        return retVal;
    }

    public static Quantifier create(TwoQuantifiers quantifiers, List<Variable> variablesOrder) {
        Quantifier quantifier = new Quantifier(quantifiers, variablesOrder, -1, -1);
        return QuantifiersCache.getInstance().get(quantifier);
    }

    public static Quantifier create(TwoQuantifiers quantifiers, List<Variable> variablesOrder, int firstVariableCardinality, int secondVariableCardinality) {
        Quantifier quantifier = new Quantifier(quantifiers, variablesOrder, firstVariableCardinality, secondVariableCardinality);
        return QuantifiersCache.getInstance().get(quantifier);
    }

    public Variable getFirstVariable() {
        return variablesOrder.get(0);
    }

    public Variable getSecondVariable() {
        return variablesOrder.get(1);
    }

    public TwoQuantifiers getQuantifiers() {
        return quantifiers;
    }

    public Variable getVariable(int idx) {
        return this.variablesOrder.get(idx);
    }

    // TODO cache this!
    public String quantifierToString(int idx) {
        StringBuilder sb = new StringBuilder();
        switch (idx) {
            case 0:
                if (quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.FORALL_EXISTS)) {
                    sb.append("V");
                } else {
                    sb.append("E");
                    if (-1 != this.firstVariableCardinality) {
                        sb.append("=").append(this.firstVariableCardinality);
                    }
                }
                break;
            case 1:
                if (quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.EXISTS_FORALL)) {
                    sb.append("V");
                } else {
                    sb.append("E");
                    if (-1 != this.secondVariableCardinality) {
                        sb.append("=").append(this.secondVariableCardinality);
                    }

                }
                break;
            default:
                throw new IllegalStateException();
        }
        sb.append(" ");
        sb.append(getVariable(idx));
        sb.append(" ");
        return sb.toString();
    }

    public String getPrefix() {
        if (null == this.stringRepresentation) {
            this.stringRepresentation = makeString(this.variablesOrder);
        }
        return this.stringRepresentation;
    }

    public Quantifier getMirror() {
        if (1 == numberOfUsedVariables) {
            throw new IllegalStateException();
        }
        if (null == mirrored) {
            TwoQuantifiers mirror = quantifiers; // stand for VxVy & ExEy
            if (TwoQuantifiers.FORALL_EXISTS == quantifiers) {
                mirror = TwoQuantifiers.EXISTS_FORALL;
            } else if (TwoQuantifiers.EXISTS_FORALL == quantifiers) {
                mirror = TwoQuantifiers.FORALL_EXISTS;
            }
            mirrored = Quantifier.create(mirror, variablesOrder, secondVariableCardinality, firstVariableCardinality);
        }
        return mirrored;
    }

    private String makeString(List<Variable> variablesOrder) {
        StringBuilder sb = new StringBuilder();
        if (TwoQuantifiers.startsWithForall(quantifiers)) {
            sb.append("V");
        } else {
            sb.append("E");
            if (-1 != this.firstVariableCardinality) {
                sb.append("=").append(this.firstVariableCardinality);
            }
        }
        sb.append(" ");
        sb.append(variablesOrder.get(0));

        if (TwoQuantifiers.FORALL != this.quantifiers && TwoQuantifiers.EXISTS != this.quantifiers) {
            StringBuilder secondPart = new StringBuilder();
            if (quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.EXISTS_FORALL)) {
                secondPart.append("V");
            } else {
                secondPart.append("E");
                if (-1 != this.secondVariableCardinality) {
                    secondPart.append("=").append(this.secondVariableCardinality);
                }

            }
            secondPart.append(" ");
            secondPart.append(variablesOrder.get(1));

            if (variablesOrder.get(0).equals(this.variablesOrder.get(0))) {
                sb.append(" ");
                sb.append(secondPart);
            } else {
                sb = secondPart.append(" ").append(sb);
            }
        }
        return sb.toString();
    }


    public List<Variable> getVariables() {
        return variablesOrder;
    }

    public boolean isCountingQuantifier() {
        return isCountingQuantifier;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Quantifier that = (Quantifier) o;
        return getPrefix().equals(that.getPrefix());
    }

    @Override
    public int hashCode() {
        return getPrefix().hashCode();
    }

    public boolean isVariableCounting(Variable variable) {
        if (variable.equals(variablesOrder.get(0))) {
            return this.firstVariableCardinality > -1;
        }
        if (variable.equals(variablesOrder.get(1))) {
            return this.secondVariableCardinality > -1;
        }
        return false;
    }

    public boolean hasSameCardinalityConstraintOnVariable(Quantifier quantifier, int variableIdx) {
        switch (variableIdx) {
            case 0:
                return this.firstVariableCardinality == quantifier.firstVariableCardinality;
            case 1:
                return this.secondVariableCardinality == quantifier.secondVariableCardinality;
            default:
                throw new IllegalStateException();
        }
    }

    public Collection<? extends Literal> getRepresentation(boolean splitOrderIfPossible) {
        return splitOrderIfPossible ? this.decomposableRepresentation : this.fixedRepresentation;
    }

    public Collection<Variable> getUsedVariables() {
        return usedVariables;
    }

    @Override
    public String toString() {
        return getPrefix();
    }

    private static Quadruple<String, Integer, String, String> parseQuantifier(String line) {
        line = line.strip();
        if (line.isBlank() || (!line.startsWith(FORALL_TOKEN) && !line.startsWith(EXISTS_TOKEN))) {
            return null;
        }

        boolean exists = line.startsWith(EXISTS_TOKEN);
        int cardinality = -1;
        line = line.substring(1).trim();
        if (exists) {
            if ('=' == line.charAt(0)) {
                int firstBreak = line.indexOf(' '); // this is probably not going to work with \s+ etc.
                cardinality = Integer.parseInt(line.substring(1, firstBreak));
                line = line.substring(firstBreak);
            }
            line = line.trim();
        }
        String variable = null;
        int nextBreak = line.indexOf(' ');
        if (nextBreak < 0) {
            variable = line;
            line = "";
        } else {
            variable = line.substring(0, nextBreak);
            line = line.substring(nextBreak).trim();
        }
        return new Quadruple<>(exists ? EXISTS_TOKEN : FORALL_TOKEN, cardinality, variable, line);
    }

    public static Pair<Quantifier, String> parseAndGetRest(String line) {
        Quadruple<String, Integer, String, String> first = parseQuantifier(line);
        if (null == first) {
            throw new IllegalStateException("Cannot parse quantifier at the start of\t" + line);
        }

        Quadruple<String, Integer, String, String> second = parseQuantifier(first.u);
        if (null == second) {
            return new Pair<>(Quantifier.create("V".equals(first.r) ? TwoQuantifiers.FORALL : TwoQuantifiers.EXISTS, Sugar.list(Variable.construct(first.t)), first.s, -1), first.u);
        }

        TwoQuantifiers quantifier = null;
        if (FORALL_TOKEN.equals(first.r)) {
            if (FORALL_TOKEN.equals(second.r)) {
                quantifier = TwoQuantifiers.FORALL_FORALL;
            } else {
                quantifier = TwoQuantifiers.FORALL_EXISTS;
            }
        } else {
            if (FORALL_TOKEN.equals(second.r)) {
                quantifier = TwoQuantifiers.EXISTS_FORALL;
            } else {
                quantifier = TwoQuantifiers.EXISTS_EXISTS;
            }
        }
        List<Variable> variables = Sugar.list(Variable.construct(first.t), Variable.construct(second.t));
        Integer firstCardinality = first.s;
        Integer secondCardinality = second.s;
        return new Pair<>(Quantifier.create(quantifier, variables, firstCardinality, secondCardinality), second.u);
    }

    public static Quantifier parse(String line) {
        return parseAndGetRest(line).getR();
    }


    public boolean isSwappable() {
        return this.firstVariableCardinality == this.secondVariableCardinality
                && (TwoQuantifiers.FORALL_FORALL == this.quantifiers || TwoQuantifiers.EXISTS_EXISTS == this.quantifiers);
    }

    public Map<Term, Term> flipSubstitution() {
        synchronized (this) {
            if (null == this.flipSubstitution) {
                this.flipSubstitution = new HashMap<>();
                this.flipSubstitution.put(variablesOrder.get(0), variablesOrder.get(1));
                this.flipSubstitution.put(variablesOrder.get(1), variablesOrder.get(0));
            }
        }
        return this.flipSubstitution;
    }
}
