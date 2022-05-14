package wyboogie.util;

import wyboogie.tasks.BoogieCompiler;
import wycc.lang.Syntactic;
import wyil.lang.WyilFile;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static wyboogie.core.BoogieFile.*;
import static wyboogie.util.Util.*;

/**
 * Construct assertions to ensure all given expression is well defined.  For example, consider the
 * following statement:
 *
 * <pre>
 *     assert xs[i] >= 0
 * </pre>
 * In this case, there is an implicit precondition that <code>i >=0 && i < |xs|</code>.  As such, we must generate a
 * boogie assertion before the above statement which ensures this is the case.  A more complex example is the
 * following:
 * <pre>
 *    if(i < |xs| && xs[i] >= 0)
 * </pre>
 * <p>This is more complex because we cannot simply create an assertion that <code>i >= 0 && i < |xs|</code> as
 * before. This is because such an assertion would exist before the conditional and, hence, must additionally take
 * into account the we know <code>i < |xs|</code> from the condition itself.  We need to generate the assertion
 * <code>(i < |xs|) ==> (i >= 0 && i < |xs|)</></code> instead.</p>
 * <p><h2>References</h2>
 * <ol>
 *     <li><b>Formalizing a hierarchical structure of practical mathematical reasoning</b>, Robison and Staples, Journal of Logical and Computation.</li>
 * </ol>
 * </p>
 *
 * @param condition
 * @return
 */
public class DefinednessExtractor extends AbstractExpressionFold<List<Stmt.Assert>> {

    private final BoogieCompiler bc;

    public DefinednessExtractor(BoogieCompiler bc) {
        this.bc = bc;
    }

    @Override
    protected List<Stmt.Assert> BOTTOM() {
        return Collections.EMPTY_LIST;
    }

    @Override
    protected List<Stmt.Assert> join(List<Stmt.Assert> lhs, List<Stmt.Assert> rhs) {
        return append(lhs,rhs);
    }

    @Override
    protected List<Stmt.Assert> join(List<List<Stmt.Assert>> operands) {
        ArrayList<Stmt.Assert> stmts = new ArrayList<>();
        for (int i = 0; i != operands.size(); ++i) {
            stmts.addAll(operands.get(i));
        }
        return stmts;
    }

    @Override
    public List<Stmt.Assert> constructLogicalAnd(Expr.LogicalAnd expr, List<List<Stmt.Assert>> operands) {
        List<Expr.Logical> window = expr.getOperands();
        List<Stmt.Assert> rs = new ArrayList<>();
        for (int i = 0; i < operands.size(); ++i) {
            List<Stmt.Assert> ith = operands.get(i);
            // Construct inference window
            Expr.Logical w = AND(window.subList(0, i),expr.getAttributes());
            // Map over existing operands
            rs.addAll(map(ith, s -> {
                Expr.Logical c = s.getCondition();
                Syntactic.Item item = s.getAttribute(Syntactic.Item.class);
                Integer errcode = s.getAttribute(Integer.class);
                return ASSERT(IMPLIES(w, c, expr.getAttributes()), ATTRIBUTE(errcode));
            }));
        }
        return rs;
    }

    @Override
    public List<Stmt.Assert> constructLogicalOr(Expr.LogicalOr expr, List<List<Stmt.Assert>> operands) {
        // Translate Whiley expressions to form the window.
        List<Expr.Logical> window = expr.getOperands();
        List<Stmt.Assert> rs = new ArrayList<>();
        for(int i=0;i<operands.size();++i) {
            List<Stmt.Assert> ith = operands.get(i);
            // Construct inference window
            Expr.Logical w = OR(window.subList(0,i),expr.getAttributes());
            // Map over existing operands
            rs.addAll(map(ith,s -> {
                Expr.Logical c = s.getCondition();
                Syntactic.Item item = s.getAttribute(Syntactic.Item.class);
                Integer errcode = s.getAttribute(Integer.class);
                return ASSERT(OR(w, c, expr.getAttributes()), ATTRIBUTE(errcode));
            }));
        }
        return rs;
    }

    @Override
    public List<Stmt.Assert> constructLogicalImplication(Expr.Implies expr, List<Stmt.Assert> left, List<Stmt.Assert> right) {
        // Map over existing operands
        List<Stmt.Assert> nright = map(right, s -> {
            Expr.Logical c = s.getCondition();
            Integer errcode = s.getAttribute(Integer.class);
            return ASSERT(IMPLIES(expr.getLeftHandSide(), c, expr.getAttributes()), ATTRIBUTE(errcode));
        });
        return append(left, nright);
    }

    @Override
    public List<Stmt.Assert> constructUniversalQuantifier(Expr.UniversalQuantifier expr, List<Stmt.Assert> body) {
        return constructQuantifier(expr, body);
    }

    @Override
    public List<Stmt.Assert> constructExistentialQuantifier(Expr.ExistentialQuantifier expr, List<Stmt.Assert> body) {
        return constructQuantifier(expr, body);
    }

    private List<Stmt.Assert> constructQuantifier(Expr.Quantifier expr, List<Stmt.Assert> body) {
        return map(body, s -> {
            Integer errcode = s.getAttribute(Integer.class);
            Expr.Logical c = s.getCondition();
            return ASSERT(FORALL(expr.getParameters(), c, expr.getAttributes()), ATTRIBUTE(errcode));
        });
    }

    @Override
    public List<Stmt.Assert> constructDictionaryAccess(Expr.DictionaryAccess expr, List<Stmt.Assert> source, List<Stmt.Assert> index) {
        Syntactic.Item wyItem = expr.getAttribute(Syntactic.Item.class);
        // Combine assertions from operands
        List<Stmt.Assert> result = append(source, index);
        // Check whether this is associated with an array access
        if (wyItem instanceof WyilFile.Expr.ArrayAccess) {
            WyilFile.Expr.ArrayAccess a = (WyilFile.Expr.ArrayAccess) wyItem;
            // Reconstruct source as expression
            Expr src = bc.reconstructExpression(a.getFirstOperand());
            // Reconstruct index as expression
            Expr idx = bc.reconstructExpression(a.getSecondOperand());
            // Add check that index is not negative
            result.add(ASSERT(LTEQ(CONST(0), idx, idx.getAttributes()), ATTRIBUTE(WyilFile.STATIC_BELOWBOUNDS_INDEX_FAILURE)));
            // Add check that index below length
            result.add(ASSERT(LT(idx, INVOKE("Array#Length", src), idx.getAttributes()), ATTRIBUTE(WyilFile.STATIC_ABOVEBOUNDS_INDEX_FAILURE)));
        }
        // Done
        return result;
    }

    @SuppressWarnings("unchecked")
	@Override
    public List<Stmt.Assert> constructDictionaryUpdate(Expr.DictionaryUpdate expr, List<Stmt.Assert> source, List<Stmt.Assert> index, List<Stmt.Assert> value) {
        Syntactic.Item wyItem = expr.getAttribute(Syntactic.Item.class);
        // Combine assertions from operands
        List<Stmt.Assert> result = append(source, index, value);
        // Check whether this is associated with an array access
        if (wyItem instanceof WyilFile.Expr.ArrayUpdate) {
            WyilFile.Expr.ArrayUpdate a = (WyilFile.Expr.ArrayUpdate) wyItem;
            // Reconstruct source as expression
            Expr src = bc.reconstructExpression(a.getFirstOperand());
            // Reconstruct index as expression
            Expr idx = bc.reconstructExpression(a.getSecondOperand());
            // Add check that index is not negative
            result.add(ASSERT(LTEQ(CONST(0), idx, idx.getAttributes()), ATTRIBUTE(WyilFile.STATIC_BELOWBOUNDS_INDEX_FAILURE)));
            // Add check that index below length
            result.add(ASSERT(LT(idx, INVOKE("Array#Length", src), idx.getAttributes()), ATTRIBUTE(WyilFile.STATIC_ABOVEBOUNDS_INDEX_FAILURE)));
        }
        // Done
        return result;
    }

    @Override
    public List<Stmt.Assert> constructIntegerDivision(Expr.IntegerDivision expr, List<Stmt.Assert> lhs, List<Stmt.Assert> rhs) {
        List<Stmt.Assert> result = append(lhs, rhs);
        Expr r = expr.getRightHandSide();
        // Add check that rhs is non-zero
        result.add(ASSERT(NEQ(r, CONST(0), r.getAttributes()), ATTRIBUTE(WyilFile.STATIC_DIVIDEBYZERO_FAILURE)));
        // Done
        return result;
    }

    @Override
    public List<Stmt.Assert> constructRemainder(Expr.Remainder expr, List<Stmt.Assert> lhs, List<Stmt.Assert> rhs) {
        List<Stmt.Assert> result = append(lhs,rhs);
        Expr r = expr.getRightHandSide();
        // Add check that rhs is non-zero
        result.add(ASSERT(NEQ(r, CONST(0), r.getAttributes()), ATTRIBUTE(WyilFile.STATIC_DIVIDEBYZERO_FAILURE)));
        // Done
        return result;
    }

    @Override
    public List<Stmt.Assert> constructInvoke(Expr.Invoke expr, List<List<Stmt.Assert>> preconditions) {
        Syntactic.Item wyItem = expr.getAttribute(Syntactic.Item.class);
        List<Stmt.Assert> rs = flattern(preconditions, l -> l);
        // Special case!
        if (expr.getName().equals("Array#Generator")) {
            Expr len = expr.getArguments().get(1);
            rs.add(ASSERT(LTEQ(CONST(0), len, len.getAttributes()), ATTRIBUTE(WyilFile.STATIC_NEGATIVE_LENGTH_FAILURE)));
        }
        else if(wyItem instanceof WyilFile.Expr.Cast) {
        	WyilFile.Expr.Cast c = (WyilFile.Expr.Cast) wyItem;
//        	Expr arg = bc.reconstructExpression(c.getOperand());
//        	Expr arg = expr.getArguments().get(1);
        	Expr.Logical test = bc.constructTypeTest(c.getType(), expr, BoogieCompiler.HEAP, wyItem);
        	rs.add(ASSERT(test, ATTRIBUTE(WyilFile.STATIC_TYPEINVARIANT_FAILURE)));
        }
        return rs;
    }
}
