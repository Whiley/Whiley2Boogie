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
	public S visitAssert(Stmt.Assert stmt, Environment environment, EnclosingScope scope) {
		List<S> preconditions = visitExpressionPrecondition(stmt.getCondition(),environment);
		return constructSequence(preconditions, super.visitAssert(stmt, environment, scope));
	}

	@Override
	public S visitAssign(Stmt.Assign stmt, Environment environment, EnclosingScope scope) {
		List<S> preconditions = visitExpressionsPrecondition(stmt.getRightHandSide(), environment);
		return constructSequence(preconditions, super.visitAssign(stmt, environment, scope));
	}


	@Override
	public S visitAssume(Stmt.Assume stmt, Environment environment, EnclosingScope scope) {
		List<S> preconditions = visitExpressionPrecondition(stmt.getCondition(),environment);
		return constructSequence(preconditions, super.visitAssume(stmt,environment,scope));
	}


	@Override
	public S visitDebug(Stmt.Debug stmt, Environment environment, EnclosingScope scope) {
		List<S> preconditions = visitExpressionPrecondition(stmt.getOperand(), environment);
		return constructSequence(preconditions, super.visitDebug(stmt, environment, scope));
	}


	@Override
	public S visitDoWhile(Stmt.DoWhile stmt, Environment environment, EnclosingScope scope) {
		// FIXME: this is broken
		List<S> preconditions = visitExpressionPrecondition(stmt.getCondition(), environment);
		System.out.println("BROKEN DO-WHILE PRECONDITIONS");
		return constructSequence(preconditions, super.visitDoWhile(stmt,environment,scope));
	}

	@Override
	public S visitFor(Stmt.For stmt, Environment environment, EnclosingScope scope) {
		Expr.ArrayRange range = (Expr.ArrayRange) stmt.getVariable().getInitialiser();
		List<S> start = visitExpressionPrecondition(range.getFirstOperand(),environment);
		List<S> end = visitExpressionPrecondition(range.getSecondOperand(),environment);
		return constructSequence(append(start, end), super.visitFor(stmt, environment, scope));
	}

	@Override
	public S visitIfElse(Stmt.IfElse stmt, Environment environment, EnclosingScope scope) {
		List<S> preconditions = visitExpressionPrecondition(stmt.getCondition(),environment);
		return constructSequence(preconditions, super.visitIfElse(stmt, environment, scope));
	}

	@Override
	public S visitInitialiser(Stmt.Initialiser stmt, Environment environment) {
		if(stmt.hasInitialiser()) {
			List<S> preconditions = visitExpressionPrecondition(stmt.getInitialiser(),environment);
			return constructSequence(preconditions, super.visitInitialiser(stmt,environment));
		} else {
			return super.visitInitialiser(stmt,environment);
		}
	}

	@Override
	public S visitReturn(Stmt.Return stmt, Environment environment, EnclosingScope scope) {
		if (stmt.hasReturn()) {
			List<S> preconditions = visitExpressionPrecondition(stmt.getReturn(), environment);
			return constructSequence(preconditions, super.visitReturn(stmt, environment, scope));
		} else {
			return super.visitReturn(stmt, environment, scope);
		}
	}

	@Override
	public S visitSwitch(Stmt.Switch stmt, Environment environment, EnclosingScope scope) {
		List<S> preconditions = visitExpressionPrecondition(stmt.getCondition(),environment);
		return constructSequence(preconditions, super.visitSwitch(stmt, environment, scope));
	}

	@Override
	public S visitWhile(Stmt.While stmt, Environment environment, EnclosingScope scope) {
		// FIXME: this is broken
		List<S> preconditions = visitExpressionPrecondition(stmt.getCondition(), environment);
		System.out.println("BROKEN WHILE PRECONDITIONS");
		return constructSequence(preconditions, super.visitWhile(stmt, environment, scope));
	}

	public List<S> visitExpressionsPrecondition(Tuple<Expr> exprs, Environment environment) {
		List<S> results = Collections.EMPTY_LIST;
		for (int i = 0; i != exprs.size(); ++i) {
			results = append(results, visitExpressionPrecondition(exprs.get(i), environment));
		}
		return results;
	}

	public List<S> visitExpressionPrecondition(Expr expr, Environment environment) {
		meter.step("expression");
		//
		switch (expr.getOpcode()) {
		// Terminals
		case EXPR_constant:
			return visitConstantPrecondition((Expr.Constant) expr, environment);
		case EXPR_indirectinvoke:
			return visitIndirectInvokePrecondition((Expr.IndirectInvoke) expr, environment);
		case EXPR_lambdaaccess:
			return visitLambdaAccessPrecondition((Expr.LambdaAccess) expr, environment);
		case DECL_lambda:
			throw new IllegalArgumentException("implement me");
		case EXPR_staticvariable:
			return visitStaticVariableAccessPrecondition((Expr.StaticVariableAccess) expr, environment);
		case EXPR_variablecopy:
		case EXPR_variablemove:
			return visitVariableAccessPrecondition((Expr.VariableAccess) expr, environment);
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
			return visitUnaryOperatorPrecondition((Expr.UnaryOperator) expr, environment);
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
			return visitBinaryOperatorPrecondition((Expr.BinaryOperator) expr, environment);
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
			return visitNaryOperatorPrecondition((Expr.NaryOperator) expr, environment);
		// Ternary Operators
		case EXPR_arrayupdate:
			return visitTernaryOperatorPrecondition((Expr.TernaryOperator) expr, environment);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<S> visitUnaryOperatorPrecondition(Expr.UnaryOperator expr, Environment environment) {
		switch (expr.getOpcode()) {
		// Unary Operators
		case EXPR_cast:
			return visitCastPrecondition((Expr.Cast) expr, environment);
		case EXPR_integernegation: {
			return visitIntegerNegationPrecondition((Expr.IntegerNegation) expr, environment);
		}
		case EXPR_is:
			return visitIsPrecondition((Expr.Is) expr, environment);
		case EXPR_logicalnot:
			return visitLogicalNotPrecondition((Expr.LogicalNot) expr, environment);
		case EXPR_logicalexistential:
			return visitExistentialQuantifierPrecondition((Expr.ExistentialQuantifier) expr, environment);
		case EXPR_logicaluniversal:
			return visitUniversalQuantifierPrecondition((Expr.UniversalQuantifier) expr, environment);
		case EXPR_bitwisenot:
			return visitBitwiseComplementPrecondition((Expr.BitwiseComplement) expr, environment);
		case EXPR_dereference:
			return visitDereferencePrecondition((Expr.Dereference) expr, environment);
		case EXPR_fielddereference:
			return visitFieldDereferencePrecondition((Expr.FieldDereference) expr, environment);
		case EXPR_new: {
			return visitNewPrecondition((Expr.New) expr, environment);
		}
		case EXPR_recordaccess:
		case EXPR_recordborrow:
			return visitRecordAccessPrecondition((Expr.RecordAccess) expr, environment);
		case EXPR_arraylength: {
			return visitArrayLengthPrecondition((Expr.ArrayLength) expr, environment);
		}
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public List<S> visitBinaryOperatorPrecondition(Expr.BinaryOperator expr, Environment environment) {
		switch (expr.getOpcode()) {
		// Binary Operators
		case EXPR_equal:
			return visitEqualPrecondition((Expr.Equal) expr, environment);
		case EXPR_notequal:
			return visitNotEqualPrecondition((Expr.NotEqual) expr, environment);
		case EXPR_logicalimplication:
			return visitLogicalImplicationPrecondition((Expr.LogicalImplication) expr, environment);
		case EXPR_logicaliff:
			return visitLogicalIffPrecondition((Expr.LogicalIff) expr, environment);
		case EXPR_integerlessthan:
			return visitIntegerLessThanPrecondition((Expr.IntegerLessThan) expr, environment);
		case EXPR_integerlessequal:
			return visitIntegerLessThanOrEqualPrecondition((Expr.IntegerLessThanOrEqual) expr, environment);
		case EXPR_integergreaterthan:
			return visitIntegerGreaterThanPrecondition((Expr.IntegerGreaterThan) expr, environment);
		case EXPR_integergreaterequal:
			return visitIntegerGreaterThanOrEqualPrecondition((Expr.IntegerGreaterThanOrEqual) expr, environment);
		case EXPR_integeraddition: {
			return visitIntegerAdditionPrecondition((Expr.IntegerAddition) expr, environment);
		}
		case EXPR_integersubtraction: {
			return visitIntegerSubtractionPrecondition((Expr.IntegerSubtraction) expr, environment);
		}
		case EXPR_integermultiplication: {
			return visitIntegerMultiplicationPrecondition((Expr.IntegerMultiplication) expr, environment);
		}
		case EXPR_integerdivision: {
			return visitIntegerDivisionPrecondition((Expr.IntegerDivision) expr, environment);
		}
		case EXPR_integerremainder: {
			return visitIntegerRemainderPrecondition((Expr.IntegerRemainder) expr, environment);
		}
		case EXPR_bitwiseshl:
			return visitBitwiseShiftLeftPrecondition((Expr.BitwiseShiftLeft) expr, environment);
		case EXPR_bitwiseshr:
			return visitBitwiseShiftRightPrecondition((Expr.BitwiseShiftRight) expr, environment);
		case EXPR_arraygenerator: {
			return visitArrayGeneratorPrecondition((Expr.ArrayGenerator) expr, environment);
		}
		case EXPR_arrayaccess:
		case EXPR_arrayborrow:
			return visitArrayAccessPrecondition((Expr.ArrayAccess) expr, environment);
		case EXPR_arrayrange: {
			return visitArrayRangePrecondition((Expr.ArrayRange) expr, environment);
		}
		case EXPR_recordupdate:
			return visitRecordUpdatePrecondition((Expr.RecordUpdate) expr, environment);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}


	public List<S> visitTernaryOperatorPrecondition(Expr.TernaryOperator expr, Environment environment) {
		switch (expr.getOpcode()) {
		// Ternary Operators
		case EXPR_arrayupdate:
			return visitArrayUpdatePrecondition((Expr.ArrayUpdate) expr, environment);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}


	public List<S> visitNaryOperatorPrecondition(Expr.NaryOperator expr, Environment environment) {
		switch (expr.getOpcode()) {
		// Nary Operators
		case EXPR_arrayinitialiser:
			return visitArrayInitialiserPrecondition((Expr.ArrayInitialiser) expr, environment);
		case EXPR_bitwiseand:
			return visitBitwiseAndPrecondition((Expr.BitwiseAnd) expr, environment);
		case EXPR_bitwiseor:
			return visitBitwiseOrPrecondition((Expr.BitwiseOr) expr, environment);
		case EXPR_bitwisexor:
			return visitBitwiseXorPrecondition((Expr.BitwiseXor) expr, environment);
		case EXPR_invoke:
			return visitInvokePrecondition((Expr.Invoke) expr, environment);
		case EXPR_logicaland:
			return visitLogicalAndPrecondition((Expr.LogicalAnd) expr, environment);
		case EXPR_logicalor:
			return visitLogicalOrPrecondition((Expr.LogicalOr) expr, environment);
		case EXPR_recordinitialiser:
			return visitRecordInitialiserPrecondition((Expr.RecordInitialiser) expr, environment);
		case EXPR_tupleinitialiser:
			return visitTupleInitialiserPrecondition((Expr.TupleInitialiser) expr, environment);
		default:
			throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}


	public List<S> visitArrayAccessPrecondition(Expr.ArrayAccess expr, Environment environment) {
		List<S> source = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> index = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(source,index);
	}


	public List<S> visitArrayLengthPrecondition(Expr.ArrayLength expr,  Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitArrayGeneratorPrecondition(Expr.ArrayGenerator expr,Environment environment) {
		List<S> value = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> length = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(value,length);
	}


	public List<S> visitArrayInitialiserPrecondition(Expr.ArrayInitialiser expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitArrayRangePrecondition(Expr.ArrayRange expr, Environment environment) {
		throw new UnsupportedOperationException();
	}


	public List<S> visitArrayUpdatePrecondition(Expr.ArrayUpdate expr, Environment environment) {
		throw new UnsupportedOperationException();
	}


	public List<S> visitBitwiseComplementPrecondition(Expr.BitwiseComplement expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitBitwiseAndPrecondition(Expr.BitwiseAnd expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitBitwiseOrPrecondition(Expr.BitwiseOr expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitBitwiseXorPrecondition(Expr.BitwiseXor expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitBitwiseShiftLeftPrecondition(Expr.BitwiseShiftLeft expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitBitwiseShiftRightPrecondition(Expr.BitwiseShiftRight expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitCastPrecondition(Expr.Cast expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitConstantPrecondition(Expr.Constant expr, Environment environment) {
		return Collections.EMPTY_LIST;
	}


	public List<S> visitDereferencePrecondition(Expr.Dereference expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitFieldDereferencePrecondition(Expr.FieldDereference expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitEqualPrecondition(Expr.Equal expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerLessThanPrecondition(Expr.IntegerLessThan expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerLessThanOrEqualPrecondition(Expr.IntegerLessThanOrEqual expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerGreaterThanPrecondition(Expr.IntegerGreaterThan expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerGreaterThanOrEqualPrecondition(Expr.IntegerGreaterThanOrEqual expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerNegationPrecondition(Expr.IntegerNegation expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitIntegerAdditionPrecondition(Expr.IntegerAddition expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerSubtractionPrecondition(Expr.IntegerSubtraction expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerMultiplicationPrecondition(Expr.IntegerMultiplication expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerDivisionPrecondition(Expr.IntegerDivision expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIntegerRemainderPrecondition(Expr.IntegerRemainder expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitIsPrecondition(Expr.Is expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitLogicalAndPrecondition(Expr.LogicalAnd expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitLogicalImplicationPrecondition(Expr.LogicalImplication expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitLogicalIffPrecondition(Expr.LogicalIff expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitLogicalNotPrecondition(Expr.LogicalNot expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitLogicalOrPrecondition(Expr.LogicalOr expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitExistentialQuantifierPrecondition(Expr.ExistentialQuantifier expr, Environment environment) {
		Tuple<Decl.StaticVariable> parameters = expr.getParameters();
		List<S> ranges = Collections.EMPTY_LIST;
		for (int i = 0; i != parameters.size(); ++i) {
			Decl.StaticVariable parameter = parameters.get(i);
			// NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
			// be deprecated.
			Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
			List<S> start = visitExpressionPrecondition(range.getFirstOperand(), environment);
			List<S> end = visitExpressionPrecondition(range.getSecondOperand(), environment);
			ranges = append(ranges,start);
			ranges = append(ranges,end);
		}
		List<S> body = visitExpressionPrecondition(expr.getOperand(), environment);
		return append(ranges,body);
	}


	public List<S> visitUniversalQuantifierPrecondition(Expr.UniversalQuantifier expr, Environment environment) {
		Tuple<Decl.StaticVariable> parameters = expr.getParameters();
		List<S> ranges = Collections.EMPTY_LIST;
		for (int i = 0; i != parameters.size(); ++i) {
			Decl.StaticVariable parameter = parameters.get(i);
			// NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
			// be deprecated.
			Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
			List<S> start = visitExpressionPrecondition(range.getFirstOperand(), environment);
			List<S> end = visitExpressionPrecondition(range.getSecondOperand(), environment);
			ranges = append(ranges,start);
			ranges = append(ranges,end);
		}
		List<S> body = visitExpressionPrecondition(expr.getOperand(), environment);
		return append(ranges,body);
	}


	public List<S> visitInvokePrecondition(Expr.Invoke expr, Environment environment) {
		return visitExpressionsPrecondition(expr.getOperands(), environment);
	}


	public List<S> visitIndirectInvokePrecondition(Expr.IndirectInvoke expr, Environment environment) {
		List<S> operand = visitExpressionPrecondition(expr.getSource(), environment);
		List<S> operands = visitExpressionsPrecondition(expr.getArguments(), environment);
		return append(operand,operands);
	}


	public List<S> visitLambdaAccessPrecondition(Expr.LambdaAccess expr, Environment environment) {
		return Collections.EMPTY_LIST;
	}


	public List<S> visitNewPrecondition(Expr.New expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitNotEqualPrecondition(Expr.NotEqual expr, Environment environment) {
		List<S> lhs = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> rhs = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		return append(lhs,rhs);
	}


	public List<S> visitRecordAccessPrecondition(Expr.RecordAccess expr, Environment environment) {
		return visitExpressionPrecondition(expr.getOperand(), environment);
	}


	public List<S> visitRecordInitialiserPrecondition(Expr.RecordInitialiser expr, Environment environment) {
		Tuple<Identifier> fields = expr.getFields();
		Tuple<Expr> operands = expr.getOperands();
		List<S> args = new ArrayList<>();
		for (int i = 0; i != fields.size(); ++i) {
			Expr operand = operands.get(i);
			args.addAll(visitExpressionPrecondition(operand, environment));
		}
		return args;
	}

	public List<S> visitRecordUpdatePrecondition(Expr.RecordUpdate expr, Environment environment) {
		List<S> src = visitExpressionPrecondition(expr.getFirstOperand(), environment);
		List<S> val = visitExpressionPrecondition(expr.getSecondOperand(), environment);
		// TODO: implement me!
		// return constructRecordUpdate(expr,src,val);
		throw new UnsupportedOperationException();
	}

	public List<S> visitTupleInitialiserPrecondition(Expr.TupleInitialiser expr, Environment environment) {
		Tuple<Expr> operands = expr.getOperands();
		List<S> args = new ArrayList<>();
		for (int i = 0; i != operands.size(); ++i) {
			Expr operand = operands.get(i);
			args.addAll(visitExpressionPrecondition(operand, environment));
		}
		return args;
	}

	public List<S> visitStaticVariableAccessPrecondition(Expr.StaticVariableAccess expr, Environment environment) {
		return Collections.EMPTY_LIST;
	}

	public List<S> visitVariableAccessPrecondition(Expr.VariableAccess expr, Environment environment) {
		return Collections.EMPTY_LIST;
	}

	public abstract S constructSequence(List<S> preconditions, S stmt);

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
