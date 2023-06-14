package ida.hypergraphIsomorphism;

import ida.ilp.logic.Constant;
import ida.utils.Sugar;

import java.util.Collection;
import java.util.HashMap;

public class IdentitySupplier implements Supplier<Constant> {

    private final HashMap<String, Constant> map;

    public IdentitySupplier() {
        this.map = new HashMap<>();
    }

    public static IdentitySupplier create() {
        return new IdentitySupplier();
    }

    public Constant get(String key) {
        if (!map.containsKey(key)) {
            map.put(key, Constant.construct(key));
        }
        return map.get(key);
    }

    public Collection<Constant> values() {
        return Sugar.list();
    }

}