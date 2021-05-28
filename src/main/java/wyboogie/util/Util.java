package wyboogie.util;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public class Util {

    /**
     * Flattern a given list of elements where some or all elements are "compound" containing subelements to be
     * extracted.
     *
     * @param items
     * @param fn
     * @param <S>
     * @param <T>
     * @return
     */
    public static <S,T> List<T> flattern(List<S> items, Function<S, List<T>> fn) {
        ArrayList<T> result = new ArrayList<>();
        for (int i = 0; i != items.size(); ++i) {
            result.addAll(fn.apply(items.get(i)));
        }
        return result;
    }

    /**
     * Map a given list of elements from one kind to another.
     *
     * @param stmts
     * @param fn
     * @param <T>
     * @return
     */
    public static <S,T> List<T> map(List<S> stmts, Function<S,T> fn) {
        ArrayList<T> rs = new ArrayList<>();
        for(int i=0;i!=stmts.size();++i) {
            rs.add(fn.apply(stmts.get(i)));
        }
        return rs;
    }

    /**
     * Functional list append.  This creates a fresh list containing both <code>left</code> and <code>right</code> operands.
     * @param left
     * @param right
     * @param <T>
     * @return
     */
    public static <T> List<T> append(T left, List<T> right) {
        ArrayList<T> result = new ArrayList();
        result.add(left);
        result.addAll(right);
        return result;
    }

    /**
     * Functional list append.  This creates a fresh list containing both <code>left</code> and <code>right</code> operands.
     * @param left
     * @param right
     * @param <T>
     * @return
     */
    public static <T> List<T> append(List<T> left, T right) {
        ArrayList<T> result = new ArrayList();
        result.addAll(left);
        result.add(right);
        return result;
    }

    /**
     * Functional list append.  This creates a fresh list containing both <code>left</code> and <code>right</code> operands.
     * @param left
     * @param right
     * @param <T>
     * @return
     */
    public static <T> List<T> append(List<T> left, List<T> right) {
        ArrayList<T> result = new ArrayList();
        result.addAll(left);
        result.addAll(right);
        return result;
    }

    /**
     * Functional list append.  This creates a fresh list containing both <code>left</code> and <code>right</code> operands.
     * @param left
     * @param right
     * @param <T>
     * @return
     */
    public static <T> List<T> append(List<T>... lists) {
        ArrayList<T> result = new ArrayList<>();
        for(int i=0;i!=lists.length;++i) {
            result.addAll(lists[i]);
        }
        return result;
    }
}
