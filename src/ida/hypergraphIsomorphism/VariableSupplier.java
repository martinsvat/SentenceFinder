package ida.hypergraphIsomorphism;

import ida.ilp.logic.Variable;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class VariableSupplier implements Supplier<Variable> {

    private final Map<String, Variable> map;
    private final String prefix;

    public VariableSupplier(String prefix) {
        this.map = new HashMap<>();
        this.prefix = prefix;
    }


    public static VariableSupplier create(String prefix) {
        return new VariableSupplier(prefix);
    }

    public Variable get(String key) {
        if (!map.containsKey(key)) {
            map.put(key, Variable.construct(prefix + this.map.size()));
        }
        return map.get(key);
    }

    public Variable getNext() {
        String size = "" + this.map.size();
        Variable key = Variable.construct(prefix + size);
        map.put(size, key);
        return key;
    }

    public Collection<Variable> values() {
        return this.map.values();
    }
}
