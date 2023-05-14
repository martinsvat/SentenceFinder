package search.sentences;

import search.ilp.logic.Constant;
import search.utils.Sugar;

import java.util.Collection;

public class SingSupplier implements Supplier<Constant>{

    Constant neg;
    Constant pos;

    public SingSupplier(){
        neg = Constant.construct("Neg");
        pos = Constant.construct("Pos");
    }

    public static SingSupplier create(){
        return new SingSupplier();
    }

    @Override
    public Constant get(String key) {
        return key.startsWith("!") ? neg : pos;
    }

    @Override
    public Collection<Constant> values() {
        return Sugar.list();
    }
}