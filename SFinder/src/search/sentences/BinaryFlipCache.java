package search.sentences;

import search.ilp.logic.Literal;

import java.util.HashMap;

public class BinaryFlipCache {
    private static BinaryFlipCache instance = new BinaryFlipCache();
    private final HashMap<Literal, Literal> map;

    private BinaryFlipCache(){
        this.map = new HashMap<>();
    }

    public Literal getFlip(Literal literal){
        if(!map.containsKey(literal)){
            Literal flipped = literal;
            if(!literal.get(0).equals(literal.get(1))){
                flipped = new Literal(literal.predicate(), literal.isNegated(), literal.get(1), literal.get(0));
            }
            map.put(literal, flipped);
        }
        return map.get(literal);
    }

    public static BinaryFlipCache getInstance() {
        return instance;
    }
}
