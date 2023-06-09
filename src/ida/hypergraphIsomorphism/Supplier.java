package ida.hypergraphIsomorphism;


import java.util.Collection;

public interface Supplier<T> {

    public T get(String key);

    public Collection<T> values();

}