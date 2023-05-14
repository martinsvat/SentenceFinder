package search.ilp.logic;

import search.utils.Sugar;

import java.util.*;

public class Quantifier {

    private final TwoQuantifiers quantifiers;
    private final List<Variable> variablesOrder;
    private final List<Literal> literals;
    public final int firstVariableCardinality;
    public final int secondVariableCardinality;
    private final boolean isCountingQuantifier;
    public Map<Variable, Literal> usedVariable;
    public Map<Variable, Literal> usedVariablesWithoutOrder;

    public Quantifier(TwoQuantifiers quantifiers, List<Variable> variablesOrder, int firstVariableCardinality, int secondVariableCardinality) {
        // value of -1 as a cardinality means that there is no counting at all 
        if ((TwoQuantifiers.FORALL_FORALL == quantifiers && (-1 != firstVariableCardinality || -1 != secondVariableCardinality))
                || (TwoQuantifiers.EXISTS_FORALL == quantifiers && (-1 != secondVariableCardinality))
                || (TwoQuantifiers.FORALL_EXISTS == quantifiers && (-1 != firstVariableCardinality))) {
            throw new IllegalStateException();
        }
        this.quantifiers = quantifiers;
        this.variablesOrder = variablesOrder;
        this.firstVariableCardinality = firstVariableCardinality;
        this.secondVariableCardinality = secondVariableCardinality;

        this.isCountingQuantifier = firstVariableCardinality > -1 || secondVariableCardinality > -1;

        this.literals = Sugar.list();
        String firstQuantifier = ((quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.FORALL_EXISTS)) ? "Forall" : ("Exists" + (-1 != this.firstVariableCardinality ? this.firstVariableCardinality : "")));
        String secondQuantifier = ((quantifiers.equals(TwoQuantifiers.FORALL_FORALL) || quantifiers.equals(TwoQuantifiers.EXISTS_FORALL)) ? "Forall" : ("Exists" + (-1 != this.secondVariableCardinality ? this.secondVariableCardinality : "")));
        literals.add(new Literal("First" + firstQuantifier, variablesOrder.get(0)));
        literals.add(new Literal("Second" + secondQuantifier, variablesOrder.get(1)));

        this.usedVariable = new HashMap<>();
        usedVariable.put(variablesOrder.get(0), literals.get(0));
        usedVariable.put(variablesOrder.get(1), literals.get(1));

        this.usedVariablesWithoutOrder = new HashMap<>();
        usedVariablesWithoutOrder.put(variablesOrder.get(0), new Literal("Q" + firstQuantifier, variablesOrder.get(0)));
        usedVariablesWithoutOrder.put(variablesOrder.get(1), new Literal("Q" + secondQuantifier, variablesOrder.get(1)));
    }

    public static Quantifier create(TwoQuantifiers quantifiers, List<Variable> variablesOrder) {
        return new Quantifier(quantifiers, variablesOrder, -1, -1);
    }

    public static Quantifier create(TwoQuantifiers quantifiers, List<Variable> variablesOrder, int firstVariableCardinality, int secondVariableCardinality) {
        return new Quantifier(quantifiers, variablesOrder, firstVariableCardinality, secondVariableCardinality);
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
        return firstVariableCardinality == that.firstVariableCardinality && secondVariableCardinality == that.secondVariableCardinality && quantifiers == that.quantifiers && variablesOrder.equals(that.variablesOrder);
    }

    @Override
    public int hashCode() {
        return Objects.hash(quantifiers, variablesOrder, firstVariableCardinality, secondVariableCardinality);
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
}
