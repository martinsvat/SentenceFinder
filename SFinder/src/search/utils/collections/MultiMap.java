/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package search.utils.collections;

import search.utils.Sugar;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
/**
 *
 * Class for datastructure which roughly corresponds to java.util.Map<R,java.util.Set<S>>.
 * 
 * @param <R> type of key-elements
 * @param <S> type of value-elements
 * @author Ondra
 */
public class MultiMap<R,S> {

    public static final int LINKED_HASH_SET = 1;
    public static final int CONCURENT_HASH_SET = 2;

    // this should be also immutable in order to get working rest of the class, e.g. putAll
    private final HashSet<S> emptySet = new HashSet<S>();
    private final int mode;

    private ConcurrentHashMap<R,Set<S>> map = new ConcurrentHashMap<R,Set<S>>();

    public MultiMap(int mode){
        this.mode = mode;
    }

    public MultiMap(){
        this(LINKED_HASH_SET);
    }

    /**
     * 
     * @return number of key-elements iterable the MultiMap
     */
    public int size() {
        return map.size();
    }

    /**
     * Checks if the MultiMap is empty.
     * @return true if the MultiMap is empty, false otherwise.
     */
    public boolean isEmpty() {
        return map.isEmpty();
    }

    /**
     * Checks if the MultiMap contains the given key.
     * @param key the key
     * @return true if the MultiMap contains the given key
     */
    public boolean containsKey(Object key) {
        return map.containsKey(key);
    }

    /**
     * Returns a set of elements associated to <em>key</em>. If there is no set associated to <em>key</em> then
     * an empty set is returned.
     * @param key the key
     * @return list of elements associated to <em>key</em>. 
     */
    public Set<S> get(Object key) {
        if (map.containsKey(key))
            return map.get(key);
        else
            return emptySet;
    }

    /**
     * Returns a set of elements associated to keys from the given set <em>keys</em>. If there is no set associated to any of the keys then
     * an empty set is returned.
     * @param keys the keys
     * @return list of elements associated to <em>key</em>. 
     */
    public Set<S> getAll(Set keys){
        Set<S> retVal = new HashSet<S>();
        for (Object key : keys){
            retVal.addAll(this.get(key));
        }
        return retVal;
    }
    
    /**
     * Adds the key-value pair to the MultiMap. It does not matter whether the MultiMap already contains
     * this key-value pair, the value will be simply added to the list associated with the given key.
     * @param key the key
     * @param value the value
     */
    public void put(R key, S value) {
        if (!map.containsKey(key)){
            if(LINKED_HASH_SET == this.mode) {
                map.put(key, new LinkedHashSet<S>());
            }else if (CONCURENT_HASH_SET == this.mode){
                map.put(key, ConcurrentHashMap.newKeySet());
            }else{
                throw new IllegalStateException("Unknown mode.");
            }
        }
        map.get(key).add(value);
    }

    /**
     * Adds all the key-value pair to the MultiMap. It does not matter whether the MultiMap already contains
     * any of the key-value pairs, the values will be simply added to the list associated with the given key.
     * @param key the key
     * @param values the collection of values
     */
    public void putAll(R key, Collection<S> values){
//        for (S s : values){
//            put(key, s);
//        }
        Set<S> set = this.get(key);
        if (set.isEmpty() || this.emptySet == set) {
            if(LINKED_HASH_SET == this.mode) {
                set = new LinkedHashSet<>();
            }else if (CONCURENT_HASH_SET == this.mode){
                set = new LinkedHashSet<>();
            }else{
                set = new HashSet<>();
            }
            set.addAll(values);
            this.map.put(key, set);
        } else {
            for (S s : values) {
                set.add(s);
            }
        }
    }


    
    /**
     * Adds all key-value pairs contained iterable the given MultiMap to this MultiMap.
     * @param multiMap the MultiMap whose key-value pairs should be added
     */
    public void putAll(MultiMap<R,S> multiMap){
        for (Entry<R,Set<S>> entry : multiMap.entrySet()){
            this.putAll(entry.getKey(), entry.getValue());
        }
    }

    /**
     * Sets the values associated with the given key.
     * @param key the key
     * @param value the new values
     */
    public void set(R key, Set<S> value){
        map.remove(key);
        map.put(key, value);
    }

    /**
     * Sets the values associated with the given key.
     * @param key the key
     * @param value the new values
     */
    public void set(R key, Collection<S> value){
        map.remove(key);
        map.put(key, Sugar.setFromCollections(value));
    }

    /**
     * Removes the first occurrence of the given value from the set associated with the given key.
     * @param key the key
     * @param value the value to be removed
     */
    public void remove(Object key, Object value) {
        Set<S> s;
        if ((s = map.get(key)) != null){
            s.remove(value);
            if (s.isEmpty()){
                map.remove(key);
            }
        }
    }
    
    /**
     * Removes all values associated with the given key.
     * @param key the key
     */
    public Set<S> remove(Object key){
        Set<S> retVal = map.remove(key);
        if (retVal == null){
            return emptySet;
        } else {
            return retVal;
        }
    }
    
    /**
     * Removes all values associated to keys from the given collection.
     * @param keys the keys for which the associated values should be removed
     * from the MultiMap
     */
    public void removeAll(Collection keys){
        for (Object o : keys){
            this.remove(o);
        }
    }
    
    /**
     * Removes everything from the MultiList.
     */
    public void clear() {
        map.clear();
    }

    /**
     * 
     * @return the set of all key-elements
     */
    public Set<R> keySet() {
        return map.keySet();
    }

    /**
     * 
     * @return a collection containing all the values
     */
    public Collection<Set<S>> values() {
        return map.values();
    }

    /**
     * 
     * @return the backing entry-set 
     */
    public Set<Entry<R, Set<S>>> entrySet() {
        return map.entrySet();
    }
    
    @Override
    public String toString(){
        return this.map.toString();
    }

    @Override
    public int hashCode(){
        return this.map.hashCode();
    }

    @Override
    public boolean equals(Object o){
        if (o instanceof MultiMap) {
            return this.map.equals(((MultiMap)o).map);
        }
        return false;
    }

    /**
     * 
     * @return string with the numbers of elements associated to particular keys
     */
    public String sizesToString(){
        StringBuilder sb = new StringBuilder();
        sb.append("MultiMap[");
        int index = 0;
        for (Entry<R,Set<S>> entry : this.map.entrySet()){
            sb.append(entry.getKey()).append(" ~ ").append(entry.getValue().size());
            if (index++ < this.map.size()-1){
                sb.append(", ");
            }
        }
        sb.append("]");
        return sb.toString();
    }

    /**
     * 
     * @return int[] array with numbers of elements associated to particular keys
     */
    public int[] sizes(){
        int[] sizes = new int[this.map.size()];
        int i = 0;
        for (Entry<R,Set<S>> entry : map.entrySet()){
            sizes[i] = entry.getValue().size();
            i++;
        }
        return sizes;
    }

    /**
     * Creates a copy of the MultiList
     * @return a copy of the MultiList
     */
    public MultiMap<R,S> copy(){
        MultiMap<R,S> retVal = new MultiMap<R,S>(this.mode);
        retVal.putAll_forCopy(this);
        return retVal;
    }
    
    private void putAll_forCopy(MultiMap<R,S> bag){
        for (Entry<R,Set<S>> entry : bag.entrySet()){
            this.putAll(entry.getKey(), Sugar.setFromCollections(entry.getValue()));
        }
    }

    public MultiList<R,S> toMultiList(){
        MultiList<R,S> retVal = new MultiList<R, S>();
        for (Entry<R,Set<S>> entry : this.entrySet()){
            retVal.putAll(entry.getKey(), entry.getValue());
        }
        return retVal;
    }

    public Set<S> fillIfNeedAndGet(R key) {
        if (!map.containsKey(key)){
            if(LINKED_HASH_SET == this.mode) {
                map.put(key, new LinkedHashSet<S>());
            }else if (CONCURENT_HASH_SET == this.mode){
                map.put(key, ConcurrentHashMap.newKeySet());
            }else{
                throw new IllegalStateException("Unknown mode.");
            }
        }
        return map.get(key);
    }
}
