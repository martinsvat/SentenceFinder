package search.ilp.logic.subsumption;

import search.ilp.logic.Term;

/**
 * Created by ondrejkuzelka on 12/06/16.
 */
public interface SolutionConsumer {

    public void solution(Term[] template, Term[] solution);

}
