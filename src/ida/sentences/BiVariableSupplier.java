package ida.sentences;

import ida.ilp.logic.Variable;
import ida.utils.tuples.Pair;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class BiVariableSupplier implements Supplier<Pair<Variable, Variable>> {

    private final String first;
    private final String second;
    private Map<String, Pair<Variable, Variable>> map;

    public BiVariableSupplier(String first, String second) {
        this.first = first;
        this.second = second;
        this.map = new HashMap<>();
    }


    @Override
    public Pair<Variable, Variable> get(String key) {
        if (!map.containsKey(key)) {
            map.put(key, new Pair<>(Variable.construct(first + map.size()), Variable.construct(second + map.size())));
        }
        return map.get(key);
    }

    @Override
    public Collection<Pair<Variable, Variable>> values() {
        throw new IllegalStateException();
    }

    public Map<String, Pair<Variable, Variable>> getMap() {
        return map;
    }

    public static BiVariableSupplier create(String first, String second) {
        return new BiVariableSupplier(first, second);
    }
}
