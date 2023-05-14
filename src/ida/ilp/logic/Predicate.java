/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package ida.ilp.logic;

import ida.utils.tuples.Pair;

/**
 * Created by Admin on 07.03.2017.
 */
public class Predicate {
    private final String name;
    private final int arity;
    private final Pair<String, Integer> pair;

    public Predicate(String name, int arity) {
        this.name = name;
        this.arity = arity;
        this.pair = new Pair<>(name, arity);
    }

    public String getName() {
        return name;
    }

    public int getArity() {
        return arity;
    }

    public Pair<String, Integer> getPair() {
        return pair;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Predicate predicate = (Predicate) o;

        if (arity != predicate.arity) return false;
        return name.equals(predicate.name);

    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + (int) (arity ^ (arity >>> 32));
        return result;
    }

    @Override
    public String toString() {
        return name + '/' + arity;
    }

    public static Predicate construct(String prologPredicateNotation) {
        String[] splitted = prologPredicateNotation.split("/");
        assert splitted.length == 2;
        return create(splitted[0], Integer.parseInt(splitted[1]));
    }

    public static Predicate create(String predicate, int arity) {
        // TODO add cache here !!!
        // cache if need be
        return new Predicate(predicate, arity); // TODO add cache here !!!!!!!
    }

    public static Predicate create(Pair<String, Integer> predicate) {
        return create(predicate.r, predicate.s);
    }


}
