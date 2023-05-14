package ida.utils;

//import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.function.Consumer;

/**
 * Created by martin.svatos on 14. 8. 2018.
 */
public class PermutationIterator<T> implements Iterator<List<T>> {

    private final int k;
    private final List<T> elements;
    private final int[] state;
    private final int[] nextIteration;
    private final boolean hasStarted;


    private PermutationIterator(List<T> elements, int k) {
        this.k = k;
        this.elements = elements;
        this.state = new int[k];
        this.nextIteration = new int[k];
        this.hasStarted = false;
    }

    @Override
    public boolean hasNext() {
        if (!hasStarted) {
            for (int idx = 0; idx < k; idx++) {
                nextIteration[idx] = idx;
                state[idx] = idx;
            }
            return true;
        } else {
            int last = findLastIncrementable(state, elements.size());
            if (last < 0) {
                return false;
            }
            int startingVal = state[last] + 1;
            for (int idx = last; idx < k; idx++) {
                state[idx] = startingVal;
                startingVal += 1;
            }
            return true;
        }
    }

    private int findLastIncrementable(int[] state, int elements) {
        // state is a array of indexes (indexed from 0)
        int idx = state.length;
        for (; idx > 0; idx--) {
            int aboveP = k - idx - 1;
            if (state[idx - 1] + aboveP <= elements) { // may here is an error and should be < instead, teste
                return idx-1;
            }
        }
        return -1;
    }

    @Override
    public List<T> next() {
        List<T> retVal = Sugar.list();
        for (int idx = 0; idx < k; idx++) {
            state[idx] = nextIteration[idx];
            retVal.add(elements.get(state[idx]));
        }
        return retVal;
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException("Not implemented.");
                //NotImplementedException();
    }

    @Override
    public void forEachRemaining(Consumer<? super List<T>> action) {
        while (hasNext()) {
            action.accept(next());
        }
    }


    public static <T> PermutationIterator<T> create(Collection<T> elements, int k) {
        System.out.println("untested version of permutation generator, write some test ;), see if (state[idx - 1] + aboveP <= elements) { // may here is an error and should be < instead, teste");
        if (k < elements.size()) {
            throw new IllegalArgumentException("k must be equal or bigger than number of elements");
        }
        return new PermutationIterator<>(Sugar.listFromCollections(elements), k);
    }
}
