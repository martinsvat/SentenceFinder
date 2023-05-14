package ida.sentences.generators;

import ida.ilp.logic.Predicate;
import ida.utils.Sugar;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class PredicateGenerator {
    // generates followers based on sort in the list !
    public static Map<Predicate, Predicate> generateFollowers(List<Predicate> predicates) {
        List<Predicate> unary = Sugar.list();
        List<Predicate> binary = Sugar.list();
        for (Predicate predicate : predicates) {
            if (1 == predicate.getArity()) {
                unary.add(predicate);
            } else if (2 == predicate.getArity()) {
                binary.add(predicate);
            } else {
                throw new IllegalStateException();
            }
        }
        Map<Predicate, Predicate> retVal = new HashMap<>();
        for (List<Predicate> predicateList : Sugar.list(unary, binary)) {
            for (int idx = 0; idx < predicateList.size() - 1; idx++) {
                retVal.put(predicateList.get(idx), predicateList.get(idx + 1));
            }
        }
        return retVal;
    }
}
