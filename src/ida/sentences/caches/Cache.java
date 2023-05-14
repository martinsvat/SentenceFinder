package ida.sentences.caches;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class Cache<T> {
    private final Map<T, T> map;

    Cache() {
        this.map = new ConcurrentHashMap<>();
    }

    public T get(T t) {
        if (!map.containsKey(t)) {
            map.put(t, t);
        }
        return map.get(t);
    }
}
