package ida.ilp.logic;

import ida.ilp.logic.subsumption.Matching;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by martin.svatos on 24. 5. 2022.
 */
public class FormulaVeryfier {


    private final List<Matching> matchings;

    public FormulaVeryfier(List<String> worlds) {
        this.matchings = worlds.stream().map(world -> Matching.create(Clause.parse(world), Matching.OI_SUBSUMPTION)).collect(Collectors.toList());
    }

    public List<Double> truthValue(Clause clause) {
        return this.matchings.stream().map(matching -> formulaHolds(clause, matching) ? 1.0 : 0.0).collect(Collectors.toList());
    }

    private boolean formulaHolds(Clause clause, Matching matching) {
        return !matching.subsumption(LogicUtils.flipSigns(clause), 0);
    }

    public static void main(String[] args){
        System.out.println("just a place holder");
    }

}