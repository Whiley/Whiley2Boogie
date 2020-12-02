package wyboogie.util;

import static wyil.lang.WyilFile.DECL_lambda;
import static wyil.lang.WyilFile.EXPR_arrayaccess;
import static wyil.lang.WyilFile.EXPR_arrayborrow;
import static wyil.lang.WyilFile.EXPR_arraygenerator;
import static wyil.lang.WyilFile.EXPR_arrayinitialiser;
import static wyil.lang.WyilFile.EXPR_arraylength;
import static wyil.lang.WyilFile.EXPR_arrayrange;
import static wyil.lang.WyilFile.EXPR_arrayupdate;
import static wyil.lang.WyilFile.EXPR_bitwiseand;
import static wyil.lang.WyilFile.EXPR_bitwisenot;
import static wyil.lang.WyilFile.EXPR_bitwiseor;
import static wyil.lang.WyilFile.EXPR_bitwiseshl;
import static wyil.lang.WyilFile.EXPR_bitwiseshr;
import static wyil.lang.WyilFile.EXPR_bitwisexor;
import static wyil.lang.WyilFile.EXPR_cast;
import static wyil.lang.WyilFile.EXPR_constant;
import static wyil.lang.WyilFile.EXPR_dereference;
import static wyil.lang.WyilFile.EXPR_equal;
import static wyil.lang.WyilFile.EXPR_fielddereference;
import static wyil.lang.WyilFile.EXPR_indirectinvoke;
import static wyil.lang.WyilFile.EXPR_integeraddition;
import static wyil.lang.WyilFile.EXPR_integerdivision;
import static wyil.lang.WyilFile.EXPR_integergreaterequal;
import static wyil.lang.WyilFile.EXPR_integergreaterthan;
import static wyil.lang.WyilFile.EXPR_integerlessequal;
import static wyil.lang.WyilFile.EXPR_integerlessthan;
import static wyil.lang.WyilFile.EXPR_integermultiplication;
import static wyil.lang.WyilFile.EXPR_integernegation;
import static wyil.lang.WyilFile.EXPR_integerremainder;
import static wyil.lang.WyilFile.EXPR_integersubtraction;
import static wyil.lang.WyilFile.EXPR_invoke;
import static wyil.lang.WyilFile.EXPR_is;
import static wyil.lang.WyilFile.EXPR_lambdaaccess;
import static wyil.lang.WyilFile.EXPR_logicaland;
import static wyil.lang.WyilFile.EXPR_logicalexistential;
import static wyil.lang.WyilFile.EXPR_logicaliff;
import static wyil.lang.WyilFile.EXPR_logicalimplication;
import static wyil.lang.WyilFile.EXPR_logicalnot;
import static wyil.lang.WyilFile.EXPR_logicalor;
import static wyil.lang.WyilFile.EXPR_logicaluniversal;
import static wyil.lang.WyilFile.EXPR_new;
import static wyil.lang.WyilFile.EXPR_notequal;
import static wyil.lang.WyilFile.EXPR_recordaccess;
import static wyil.lang.WyilFile.EXPR_recordborrow;
import static wyil.lang.WyilFile.EXPR_recordinitialiser;
import static wyil.lang.WyilFile.EXPR_recordupdate;
import static wyil.lang.WyilFile.EXPR_staticvariable;
import static wyil.lang.WyilFile.EXPR_tupleinitialiser;
import static wyil.lang.WyilFile.EXPR_variablecopy;
import static wyil.lang.WyilFile.EXPR_variablemove;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wybs.lang.Build.Meter;
import wybs.util.AbstractCompilationUnit.Identifier;
import wybs.util.AbstractCompilationUnit.Tuple;
import wyfs.util.Pair;
import wyil.lang.WyilFile.Decl;
import wyil.lang.WyilFile.Expr;
import wyil.lang.WyilFile.Stmt;

/**
 * Provides a tweaked version of <code>AbstractTranslator</code> which
 * facilitates the construction of preconditions for all expressions.
 *
 * @author djp
 *
 * @param <D>
 * @param <S>
 * @param <E>
 */
public abstract class AbstractTranslator<D,S,E extends S> extends wyil.util.AbstractTranslator<D, S, E> {

	public AbstractTranslator(Meter meter, wyil.util.Subtyping.Environment subtypeOperator) {
		super(meter, subtypeOperator);
	}

	@Override
	public S visitAssert(Stmt.Assert stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getCondition());
		E operand = visitExpression(stmt.getCondition());
		return constructAssert(stmt, operand, preconditions);
	}

	@Override
	public S visitAssign(Stmt.Assign stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionsPrecondition(stmt.getRightHandSide());
		List<E> lvals = visitLVals(stmt.getLeftHandSide(), scope);
		List<E> rvals = visitExpressions(stmt.getRightHandSide());
		return constructAssign(stmt,lvals,rvals,preconditions);
	}

	@Override
	public S visitAssume(Stmt.Assume stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getCondition());
		E operand = visitExpression(stmt.getCondition());
		return constructAssume(stmt, operand, preconditions);
	}

	@Override
	public S visitDebug(Stmt.Debug stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getOperand());
		E operand = visitExpression(stmt.getOperand());
		return constructDebug(stmt,operand,preconditions);
	}

	@Override
	public S visitDoWhile(Stmt.DoWhile stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getCondition());
		S body = visitStatement(stmt.getBody(), scope);
		E condition = visitExpression(stmt.getCondition());
		List<E> invariant = visitHomogoneousExpressions(stmt.getInvariant());
		return constructDoWhile(stmt, body, condition, invariant, preconditions);
	}

	@Override
	public S visitFor(Stmt.For stmt, EnclosingScope scope) {
		Expr.ArrayRange range = (Expr.ArrayRange) stmt.getVariable().getInitialiser();
		List<E> startPreconditions = visitExpressionPrecondition(range.getFirstOperand());
		List<E> endPreconditions = visitExpressionPrecondition(range.getSecondOperand());
		E start = visitExpression(range.getFirstOperand());
		E end = visitExpression(range.getSecondOperand());
		List<E> invariant = visitHomogoneousExpressions(stmt.getInvariant());
		S body = visitStatement(stmt.getBody(), scope);
		return constructFor(stmt, new Pair<>(start, end), invariant, body,
				append(startPreconditions, endPreconditions));
	}

	@Override
	public S visitIfElse(Stmt.IfElse stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getCondition());
		E condition = visitExpression(stmt.getCondition());
		S trueBranch = visitStatement(stmt.getTrueBranch(), scope);
		S falseBranch = null;
		if (stmt.hasFalseBranch()) {
			falseBranch = visitStatement(stmt.getFalseBranch(), scope);
		}
		return constructIfElse(stmt, condition, trueBranch, falseBranch, preconditions);
	}

	@Override
	public S visitInitialiser(Stmt.Initialiser stmt) {
		if (stmt.hasInitialiser()) {
			List<E> preconditions = visitExpressionPrecondition(stmt.getInitialiser());
			E initialiser = visitExpression(stmt.getInitialiser());
			return constructInitialiser(stmt, initialiser, preconditions);
		} else {
			return constructInitialiser(stmt, null, null);
		}
	}

	@Override
	public S visitInvokeStmt(Expr.Invoke stmt) {
		List<E> preconditions = visitExpressionsPrecondition(stmt.getOperands());
		List<E> operands = visitHeterogenousExpressions(stmt.getOperands());
		return constructInvokeStmt(stmt, operands, preconditions);
	}

	@Override
	public S visitIndirectInvokeStmt(Expr.IndirectInvoke stmt) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getSource());
		preconditions.addAll(visitExpressionsPrecondition(stmt.getArguments()));
		E operand = visitExpression(stmt.getSource());
		List<E> operands = visitHeterogenousExpressions(stmt.getArguments());
		return constructIndirectInvokeStmt(stmt, operand, operands, preconditions);
	}


	@Override
	public S visitReturn(Stmt.Return stmt, EnclosingScope scope) {
		if (stmt.hasReturn()) {
			List<E> preconditions = visitExpressionPrecondition(stmt.getReturn());
			E returns = visitExpression(stmt.getReturn());
			return constructReturn(stmt, returns, preconditions);
		} else {
			return constructReturn(stmt, null, null);
		}
	}

	@Override
	public S visitSwitch(Stmt.Switch stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getCondition());
		E condition = visitExpression(stmt.getCondition());
		Tuple<Stmt.Case> cases = stmt.getCases();
		ArrayList<Pair<List<E>,S>> cs = new ArrayList<>();
		for (int i = 0; i != cases.size(); ++i) {
			cs.add(visitCase(cases.get(i), scope));
		}
		return constructSwitch(stmt, condition, cs, preconditions);
	}

	@Override
	public S visitWhile(Stmt.While stmt, EnclosingScope scope) {
		List<E> preconditions = visitExpressionPrecondition(stmt.getCondition());
		E condition = visitExpression(stmt.getCondition());
		List<E> invariant = visitHomogoneousExpressions(stmt.getInvariant());
		S body = visitStatement(stmt.getBody(), scope);
		return constructWhile(stmt, condition, invariant, body, preconditions);
	}

	public List<E> visitExpressionsPrecondition(Tuple<Expr> exprs) {
		List<E> results = Collections.EMPTY_LIST;
		for (int i = 0; i != exprs.size(); ++i) {
			results = append(results, visitExpressionPrecondition(exprs.get(i)));
		}
		return results;
	}

	public List<E> visitExpressionPrecondition(Expr expr) {
		meter.step("expression");
		//
		switch (expr.getOpcode()) {
		// Terminals
		case EXPR_constant:
			return visitConstantPrecondition((Expr.Constant) expr);
		case EXPR_indirectinvoke:
			return visitIndirectInvokePrecondition((Expr.IndirectInvoke) expr);
		case EXPR_lambdaaccess:
			return visitLambdaAccessPrecondition((Expr.LambdaAccess) expr);
		case DECL_lambda:
			throw new IllegalArgumentException("implement me");
		case EXPR_staticvariable:
			return visitStaticVariableAccessPrecondition((Expr.StaticVariableAccess) expr);
		case EXPR_variablecopy:
		case EXPR_variablemove:
			return visitVariableAccessPrecondition((Expr.VariableAccess) expr);
		// Unary Operators
		case EXPR_cast:
		case EXPR_integernegation:
		case EXPR_is:
		case EXPR_logicalnot:
		case EXPR_logicalexistential:
		case EXPR_logicaluniversal:
		case EXPR_bitwisenot:
		case EXPR_dereference:
		case EXPR_fielddereference:
		case EXPR_new:
		case EXPR_recordaccess:
		case EXPR_recordborrow:
		case EXPR_arraylength:
			return visitUnaryOperatorPrecondition((Expr.UnaryOperator) expr);
		// Binary Operators
		case EXPR_logicalimplication:
		case EXPR_logicaliff:
		case EXPR_equal:
		case EXPR_notequal:
		case EXPR_integerlessthan:
		case EXPR_integerlessequal:
		case EXPR_integergreaterthan:
		case EXPR_integergreaterequal:
		case EXPR_integeraddition:
		case EXPR_integersubtraction:
		case EXPR_integermultiplication:
		case EXPR_integerdivision:
		case EXPR_integerremainder:
		case EXPR_bitwiseshl:
		case EXPR_bitwiseshr:
		case EXPR_arrayaccess:
		case EXPR_arrayborrow:
		case EXPR_arrayrange:
		case EXPR_recordupdate:
		case EXPR_arraygenerator:
			return visitBinaryOperatorPrecondition((Expr.BinaryOperator) expr);
		// Nary Operators
		case EXPR_logicaland:
		case EXPR_logicalor:
		case EXPR_invoke:
		case EXPR_bitwiseand:
		case EXPR_bitwiseor:
		case EXPR_bitwisexor:
		case EXPR_arrayinitialiser:
		case EXPR_recordinitialiser:
		case EXPR_tupleinitialiser:
			return visitNaryOperatorPrecondition((Expr.NaryOperator) expr);
		// Ternary Operators
		case EXPR_arrayupdate:
			return visitTernaryOperatorPrecondition((Expr.TernaryOperator) expr);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<E> visitUnaryOperatorPrecondition(Expr.UnaryOperator expr) {
		switch (expr.getOpcode()) {
		// Unary Operators
		case EXPR_cast:
			return visitCastPrecondition((Expr.Cast) expr);
		case EXPR_integernegation: {
			return visitIntegerNegationPrecondition((Expr.IntegerNegation) expr);
		}
		case EXPR_is:
			return visitIsPrecondition((Expr.Is) expr);
		case EXPR_logicalnot:
			return visitLogicalNotPrecondition((Expr.LogicalNot) expr);
		case EXPR_logicalexistential:
			return visitExistentialQuantifierPrecondition((Expr.ExistentialQuantifier) expr);
		case EXPR_logicaluniversal:
			return visitUniversalQuantifierPrecondition((Expr.UniversalQuantifier) expr);
		case EXPR_bitwisenot:
			return visitBitwiseComplementPrecondition((Expr.BitwiseComplement) expr);
		case EXPR_dereference:
			return visitDereferencePrecondition((Expr.Dereference) expr);
		case EXPR_fielddereference:
			return visitFieldDereferencePrecondition((Expr.FieldDereference) expr);
		case EXPR_new: {
			return visitNewPrecondition((Expr.New) expr);
		}
		case EXPR_recordaccess:
		case EXPR_recordborrow:
			return visitRecordAccessPrecondition((Expr.RecordAccess) expr);
		case EXPR_arraylength: {
			return visitArrayLengthPrecondition((Expr.ArrayLength) expr);
		}
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<E> visitBinaryOperatorPrecondition(Expr.BinaryOperator expr) {
		switch (expr.getOpcode()) {
		// Binary Operators
		case EXPR_equal:
			return visitEqualPrecondition((Expr.Equal) expr);
		case EXPR_notequal:
			return visitNotEqualPrecondition((Expr.NotEqual) expr);
		case EXPR_logicalimplication:
			return visitLogicalImplicationPrecondition((Expr.LogicalImplication) expr);
		case EXPR_logicaliff:
			return visitLogicalIffPrecondition((Expr.LogicalIff) expr);
		case EXPR_integerlessthan:
			return visitIntegerLessThanPrecondition((Expr.IntegerLessThan) expr);
		case EXPR_integerlessequal:
			return visitIntegerLessThanOrEqualPrecondition((Expr.IntegerLessThanOrEqual) expr);
		case EXPR_integergreaterthan:
			return visitIntegerGreaterThanPrecondition((Expr.IntegerGreaterThan) expr);
		case EXPR_integergreaterequal:
			return visitIntegerGreaterThanOrEqualPrecondition((Expr.IntegerGreaterThanOrEqual) expr);
		case EXPR_integeraddition: {
			return visitIntegerAdditionPrecondition((Expr.IntegerAddition) expr);
		}
		case EXPR_integersubtraction: {
			return visitIntegerSubtractionPrecondition((Expr.IntegerSubtraction) expr);
		}
		case EXPR_integermultiplication: {
			return visitIntegerMultiplicationPrecondition((Expr.IntegerMultiplication) expr);
		}
		case EXPR_integerdivision: {
			return visitIntegerDivisionPrecondition((Expr.IntegerDivision) expr);
		}
		case EXPR_integerremainder: {
			return visitIntegerRemainderPrecondition((Expr.IntegerRemainder) expr);
		}
		case EXPR_bitwiseshl:
			return visitBitwiseShiftLeftPrecondition((Expr.BitwiseShiftLeft) expr);
		case EXPR_bitwiseshr:
			return visitBitwiseShiftRightPrecondition((Expr.BitwiseShiftRight) expr);
		case EXPR_arraygenerator: {
			return visitArrayGeneratorPrecondition((Expr.ArrayGenerator) expr);
		}
		case EXPR_arrayaccess:
		case EXPR_arrayborrow:
			return visitArrayAccessPrecondition((Expr.ArrayAccess) expr);
		case EXPR_arrayrange: {
			return visitArrayRangePrecondition((Expr.ArrayRange) expr);
		}
		case EXPR_recordupdate:
			return visitRecordUpdatePrecondition((Expr.RecordUpdate) expr);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<E> visitTernaryOperatorPrecondition(Expr.TernaryOperator expr) {
		switch (expr.getOpcode()) {
		// Ternary Operators
		case EXPR_arrayupdate:
			return visitArrayUpdatePrecondition((Expr.ArrayUpdate) expr);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<E> visitNaryOperatorPrecondition(Expr.NaryOperator expr) {
		switch (expr.getOpcode()) {
		// Nary Operators
		case EXPR_arrayinitialiser:
			return visitArrayInitialiserPrecondition((Expr.ArrayInitialiser) expr);
		case EXPR_bitwiseand:
			return visitBitwiseAndPrecondition((Expr.BitwiseAnd) expr);
		case EXPR_bitwiseor:
			return visitBitwiseOrPrecondition((Expr.BitwiseOr) expr);
		case EXPR_bitwisexor:
			return visitBitwiseXorPrecondition((Expr.BitwiseXor) expr);
		case EXPR_invoke:
			return visitInvokePrecondition((Expr.Invoke) expr);
		case EXPR_logicaland:
			return visitLogicalAndPrecondition((Expr.LogicalAnd) expr);
		case EXPR_logicalor:
			return visitLogicalOrPrecondition((Expr.LogicalOr) expr);
		case EXPR_recordinitialiser:
			return visitRecordInitialiserPrecondition((Expr.RecordInitialiser) expr);
		case EXPR_tupleinitialiser:
			return visitTupleInitialiserPrecondition((Expr.TupleInitialiser) expr);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<E> visitArrayAccessPrecondition(Expr.ArrayAccess expr) {
		List<E> source = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> index = visitExpressionPrecondition(expr.getSecondOperand());
		E s = visitExpression(expr.getFirstOperand());
		E i = visitExpression(expr.getSecondOperand());
		E pre = constructArrayAccessPrecondition(expr, s, i);
		return append(append(source, index), pre);
	}

	public List<E> visitArrayLengthPrecondition(Expr.ArrayLength expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitArrayGeneratorPrecondition(Expr.ArrayGenerator expr) {
		List<E> value = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> length = visitExpressionPrecondition(expr.getSecondOperand());
		return append(value,length);
	}

	public List<E> visitArrayInitialiserPrecondition(Expr.ArrayInitialiser expr) {
		return visitExpressionsPrecondition(expr.getOperands());
	}

	public List<E> visitArrayRangePrecondition(Expr.ArrayRange expr) {
		throw new UnsupportedOperationException();
	}

	public List<E> visitArrayUpdatePrecondition(Expr.ArrayUpdate expr) {
		throw new UnsupportedOperationException();
	}

	public List<E> visitBitwiseComplementPrecondition(Expr.BitwiseComplement expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitBitwiseAndPrecondition(Expr.BitwiseAnd expr) {
		return visitExpressionsPrecondition(expr.getOperands());
	}

	public List<E> visitBitwiseOrPrecondition(Expr.BitwiseOr expr) {
		return visitExpressionsPrecondition(expr.getOperands());
	}

	public List<E> visitBitwiseXorPrecondition(Expr.BitwiseXor expr) {
		return visitExpressionsPrecondition(expr.getOperands());
	}

	public List<E> visitBitwiseShiftLeftPrecondition(Expr.BitwiseShiftLeft expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitBitwiseShiftRightPrecondition(Expr.BitwiseShiftRight expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitCastPrecondition(Expr.Cast expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitConstantPrecondition(Expr.Constant expr) {
		return Collections.EMPTY_LIST;
	}

	public List<E> visitDereferencePrecondition(Expr.Dereference expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitFieldDereferencePrecondition(Expr.FieldDereference expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitEqualPrecondition(Expr.Equal expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerLessThanPrecondition(Expr.IntegerLessThan expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerLessThanOrEqualPrecondition(Expr.IntegerLessThanOrEqual expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerGreaterThanPrecondition(Expr.IntegerGreaterThan expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerGreaterThanOrEqualPrecondition(Expr.IntegerGreaterThanOrEqual expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerNegationPrecondition(Expr.IntegerNegation expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitIntegerAdditionPrecondition(Expr.IntegerAddition expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerSubtractionPrecondition(Expr.IntegerSubtraction expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerMultiplicationPrecondition(Expr.IntegerMultiplication expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIntegerDivisionPrecondition(Expr.IntegerDivision expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		E l = visitExpression(expr.getFirstOperand());
		E r = visitExpression(expr.getSecondOperand());
		E pre = constructIntegerDivisionPrecondition(expr,l,r);
		return append(append(lhs, rhs), pre);
	}

	public List<E> visitIntegerRemainderPrecondition(Expr.IntegerRemainder expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitIsPrecondition(Expr.Is expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitLogicalAndPrecondition(Expr.LogicalAnd expr) {
		return visitExpressionsPrecondition(expr.getOperands());
	}


	public List<E> visitLogicalImplicationPrecondition(Expr.LogicalImplication expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}


	public List<E> visitLogicalIffPrecondition(Expr.LogicalIff expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}

	public List<E> visitLogicalNotPrecondition(Expr.LogicalNot expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}

	public List<E> visitLogicalOrPrecondition(Expr.LogicalOr expr) {
		return visitExpressionsPrecondition(expr.getOperands());
	}

	public List<E> visitExistentialQuantifierPrecondition(Expr.ExistentialQuantifier expr) {
		Tuple<Decl.StaticVariable> parameters = expr.getParameters();
		List<E> ranges = Collections.EMPTY_LIST;
		for (int i = 0; i != parameters.size(); ++i) {
			Decl.StaticVariable parameter = parameters.get(i);
			// NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
			// be deprecated.
			Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
			List<E> start = visitExpressionPrecondition(range.getFirstOperand());
			List<E> end = visitExpressionPrecondition(range.getSecondOperand());
			ranges = append(ranges,start);
			ranges = append(ranges,end);
		}
		List<E> body = visitExpressionPrecondition(expr.getOperand());
		return append(ranges,body);
	}


	public List<E> visitUniversalQuantifierPrecondition(Expr.UniversalQuantifier expr) {
		Tuple<Decl.StaticVariable> parameters = expr.getParameters();
		List<E> ranges = Collections.EMPTY_LIST;
		for (int i = 0; i != parameters.size(); ++i) {
			Decl.StaticVariable parameter = parameters.get(i);
			// NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
			// be deprecated.
			Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
			List<E> start = visitExpressionPrecondition(range.getFirstOperand());
			List<E> end = visitExpressionPrecondition(range.getSecondOperand());
			ranges = append(ranges,start);
			ranges = append(ranges,end);
		}
		List<E> body = visitExpressionPrecondition(expr.getOperand());
		return append(ranges,body);
	}


	public List<E> visitInvokePrecondition(Expr.Invoke expr) {
		List<E> argPreconditions = visitExpressionsPrecondition(expr.getOperands());
		List<E> args = visitExpressions(expr.getOperands());
		E pre = constructInvokePrecondition(expr, args);
		if(pre != null) {
			return append(argPreconditions,pre);
		} else {
			return argPreconditions;
		}
	}


	public List<E> visitIndirectInvokePrecondition(Expr.IndirectInvoke expr) {
		List<E> operand = visitExpressionPrecondition(expr.getSource());
		List<E> operands = visitExpressionsPrecondition(expr.getArguments());
		return append(operand,operands);
	}


	public List<E> visitLambdaAccessPrecondition(Expr.LambdaAccess expr) {
		return Collections.EMPTY_LIST;
	}


	public List<E> visitNewPrecondition(Expr.New expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}


	public List<E> visitNotEqualPrecondition(Expr.NotEqual expr) {
		List<E> lhs = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> rhs = visitExpressionPrecondition(expr.getSecondOperand());
		return append(lhs,rhs);
	}


	public List<E> visitRecordAccessPrecondition(Expr.RecordAccess expr) {
		return visitExpressionPrecondition(expr.getOperand());
	}


	public List<E> visitRecordInitialiserPrecondition(Expr.RecordInitialiser expr) {
		Tuple<Identifier> fields = expr.getFields();
		Tuple<Expr> operands = expr.getOperands();
		List<E> args = new ArrayList<>();
		for (int i = 0; i != fields.size(); ++i) {
			Expr operand = operands.get(i);
			args.addAll(visitExpressionPrecondition(operand));
		}
		return args;
	}

	public List<E> visitRecordUpdatePrecondition(Expr.RecordUpdate expr) {
		List<E> src = visitExpressionPrecondition(expr.getFirstOperand());
		List<E> val = visitExpressionPrecondition(expr.getSecondOperand());
		// TODO: implement me!
		// return constructRecordUpdate(expr,src,val);
		throw new UnsupportedOperationException();
	}

	public List<E> visitTupleInitialiserPrecondition(Expr.TupleInitialiser expr) {
		Tuple<Expr> operands = expr.getOperands();
		List<E> args = new ArrayList<>();
		for (int i = 0; i != operands.size(); ++i) {
			Expr operand = operands.get(i);
			args.addAll(visitExpressionPrecondition(operand));
		}
		return args;
	}

	public List<E> visitStaticVariableAccessPrecondition(Expr.StaticVariableAccess expr) {
		return Collections.EMPTY_LIST;
	}

	public List<E> visitVariableAccessPrecondition(Expr.VariableAccess expr) {
		return Collections.EMPTY_LIST;
	}

	// ====================================================================================
	// Old Statement Constructors
	// ====================================================================================

	@Override
	public final S constructAssert(Stmt.Assert stmt, E condition) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructAssign(Stmt.Assign stmt, List<E> lvals, List<E> rvals) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructAssume(Stmt.Assume stmt, E condition) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructDebug(Stmt.Debug stmt, E operand) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructDoWhile(Stmt.DoWhile stmt, S body, E condition, List<E> invariant) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructFor(Stmt.For stmt, Pair<E,E> range, List<E> invariant, S body) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructIfElse(Stmt.IfElse stmt, E condition, S trueBranch, S falseBranch){
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructInitialiser(Stmt.Initialiser stmt, E initialiser) {
		throw new UnsupportedOperationException();
	}

	@Override
	public S constructInvokeStmt(Expr.Invoke stmt, List<E> arguments) {
		throw new UnsupportedOperationException();
	}

	@Override
	public S constructIndirectInvokeStmt(Expr.IndirectInvoke stmt, E source, List<E> arguments) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructReturn(Stmt.Return stmt, E ret) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructSwitch(Stmt.Switch stmt, E condition, List<Pair<List<E>,S>> cases) {
		throw new UnsupportedOperationException();
	}

	@Override
	public final S constructWhile(Stmt.While stmt, E condition, List<E> invariant, S body) {
		throw new UnsupportedOperationException();
	}

	// ====================================================================================
	// New Statement Constructors
	// ====================================================================================

	public abstract S constructAssert(Stmt.Assert stmt, E condition, List<E> preconditions);

	public abstract S constructAssign(Stmt.Assign stmt, List<E> lvals, List<E> rvals, List<E> preconditions);

	public abstract S constructAssume(Stmt.Assume stmt, E condition, List<E> preconditions);

	public abstract S constructDebug(Stmt.Debug stmt, E operand, List<E> preconditions);

	public abstract S constructDoWhile(Stmt.DoWhile stmt, S body, E condition, List<E> invariant, List<E> preconditions);

	public abstract S constructFor(Stmt.For stmt, Pair<E,E> range, List<E> invariant, S body, List<E> preconditions);

	public abstract S constructIfElse(Stmt.IfElse stmt, E condition, S trueBranch, S falseBranch, List<E> preconditions);

	public abstract S constructInitialiser(Stmt.Initialiser stmt, E initialiser, List<E> preconditions);

	public abstract S constructInvokeStmt(Expr.Invoke stmt, List<E> arguments, List<E> preconditions);

	public abstract S constructIndirectInvokeStmt(Expr.IndirectInvoke stmt, E source, List<E> arguments, List<E> preconditions);

	public abstract S constructReturn(Stmt.Return stmt, E ret, List<E> preconditions);

	public abstract S constructSwitch(Stmt.Switch stmt, E condition, List<Pair<List<E>,S>> cases, List<E> preconditions);

	public abstract S constructWhile(Stmt.While stmt, E condition, List<E> invariant, S body, List<E> preconditions);

	// ====================================================================================
	// Precondition Constructors
	// ====================================================================================

	public abstract E constructArrayAccessPrecondition(Expr.ArrayAccess expr, E source, E index);

	public abstract E constructIntegerDivisionPrecondition(Expr.IntegerDivision expr, E lhs, E rhs);

	public abstract E constructInvokePrecondition(Expr.Invoke expr, List<E> arguments);

	public static <S> List<S> append(List<S> lhs, List<S> rhs) {
		if(lhs.isEmpty() && rhs.isEmpty()) {
			return Collections.EMPTY_LIST;
		}
		ArrayList<S> rs = new ArrayList<>();
		rs.addAll(lhs);
		rs.addAll(rhs);
		return rs;
	}

	public static <S> List<S> append(List<S> lhs, S rhs) {
		ArrayList<S> rs = new ArrayList<>();
		rs.addAll(lhs);
		rs.add(rhs);
		return rs;
	}
}
