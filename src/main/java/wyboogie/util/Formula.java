package wyboogie.util;

import wyfs.util.ArrayUtils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

public class Formula<T extends Formula.Term<T>> {
    public static Formula TRUE = new Formula(new Disjunct[0]);
    public static final Formula FALSE = new Formula(null);

    public static <S extends Term<S>> Formula<S> AND(S... items) {
        Disjunct<S>[] disjuncts = new Disjunct[items.length];
        for(int i=0;i!=items.length;++i) {
            S[] item = Arrays.copyOf(items,1);
            item[0] = items[i];
            disjuncts[i] = new Disjunct<>(item);
        }
        return new Formula<S>(disjuncts);
    }

    private final Disjunct<T>[] disjuncts;

    private Formula(Disjunct<T>... conjuncts) {
        this.disjuncts = conjuncts;
    }

    public int size() {
        return disjuncts.length;
    }

    public T[] get(int i) {
        return disjuncts[i].clauses;
    }

    public Formula<T> implies(Formula<T> operand) {
        return not().or(operand);
    }

    public Formula<T> not() {
        throw new UnsupportedOperationException();
    }

    public Formula<T> and(Formula<T> operand) {
        if (disjuncts == null || operand == TRUE) {
            return this;
        } else if (operand.disjuncts == null || this == TRUE) {
            return operand;
        } else {
            final Disjunct<T>[] operand_disjuncts = operand.disjuncts;
            int n = disjuncts.length + operand_disjuncts.length;
            Disjunct<T>[] ndisjuncts = Arrays.copyOf(disjuncts,n);
            System.arraycopy(operand_disjuncts,0,ndisjuncts,disjuncts.length,operand_disjuncts.length);
            return new Formula<T>(ndisjuncts);
        }
    }

    public Formula<T> or(Formula<T> operand) {
        if (disjuncts == null || operand == TRUE) {
            return operand;
        } else if (operand.disjuncts == null || this == TRUE) {
            return this;
        } else {
            final Disjunct<T>[] operand_disjuncts = operand.disjuncts;
            List<Disjunct<T>> ndisjuncts = new ArrayList<>();
            for(int i=0;i!=disjuncts.length;++i) {
                Disjunct<T> ith = disjuncts[i];
                for(int j=0;j!=operand_disjuncts.length;++j) {
                    Disjunct<T> jth = operand_disjuncts[j];
                    ndisjuncts.add(ith.or(jth));
                }
            }
            return new Formula<>(ndisjuncts.toArray(new Disjunct[ndisjuncts.size()]));
        }
    }

    private static final class Disjunct<T> {
        private final T[] clauses;

        public Disjunct(T[] clauses) {
            this.clauses = clauses;
        }

        public Disjunct<T> or(Disjunct<T> disjunct) {
            return new Disjunct<>(ArrayUtils.append(clauses,disjunct.clauses));
        }
    }

    public interface Term<S> {
        public S invert();
    }
}
