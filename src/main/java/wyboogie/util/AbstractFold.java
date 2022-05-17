// Copyright 2011 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wyboogie.util;

import wycc.util.AbstractCompilationUnit.Tuple;
import wyil.lang.WyilFile.*;

import java.util.ArrayList;
import java.util.List;

import static wyil.lang.WyilFile.*;

/**
 * A simple visitor over all declarations, statements, expressions and types in
 * a given WhileyFile which consumes one data parameter and returns one value.
 * The intention is that this is extended as necessary to provide custom
 * functionality.
 *
 * @author David J. Pearce
 *
 */
public abstract class AbstractFold<R> {

	public R visitStatement(Stmt stmt) {
		switch (stmt.getOpcode()) {
			case STMT_assert:
				return visitAssert((Stmt.Assert) stmt);
			case STMT_assign:
				return visitAssign((Stmt.Assign) stmt);
			case STMT_assume:
				return visitAssume((Stmt.Assume) stmt);
			case STMT_block:
				return visitBlock((Stmt.Block) stmt);
			case STMT_break:
				return constructBreak((Stmt.Break) stmt);
			case STMT_continue:
				return constructContinue((Stmt.Continue) stmt);
			case STMT_debug:
				return visitDebug((Stmt.Debug) stmt);
			case STMT_dowhile:
				return visitDoWhile((Stmt.DoWhile) stmt);
			case STMT_fail:
				return constructFail((Stmt.Fail) stmt);
			case STMT_for:
				return visitFor((Stmt.For) stmt);
			case STMT_if:
			case STMT_ifelse:
				return visitIfElse((Stmt.IfElse) stmt);
			case STMT_initialiser:
			case STMT_initialiservoid:
				return visitInitialiser((Stmt.Initialiser) stmt);
			case EXPR_invoke:
				return visitInvoke((Expr.Invoke) stmt);
			case EXPR_indirectinvoke:
				return visitIndirectInvoke((Expr.IndirectInvoke) stmt);
			case STMT_namedblock:
				return visitNamedBlock((Stmt.NamedBlock) stmt);
			case STMT_return:
			case STMT_returnvoid:
				return visitReturn((Stmt.Return) stmt);
			case STMT_skip:
				return constructSkip((Stmt.Skip) stmt);
			case STMT_switch:
				return visitSwitch((Stmt.Switch) stmt);
			case STMT_while:
				return visitWhile((Stmt.While) stmt);
			default:
				return visitExpression((Expr) stmt);
		}
	}

	public R visitAssert(Stmt.Assert stmt) {
		R operand = visitExpression(stmt.getCondition());
		return constructAssert(stmt,operand);
	}


	public R visitAssign(Stmt.Assign stmt) {
		List<R> lvals = visitLVals(stmt.getLeftHandSide());
		List<R> rvals = visitExpressions(stmt.getRightHandSide());
		return constructAssign(stmt,lvals,rvals);
	}

	public List<R> visitLVals(Tuple<LVal> lvals) {
		ArrayList<R> r = new ArrayList<>();
		for(int i=0;i!=lvals.size();++i) {
			r.add(visitExpression(lvals.get(i)));
		}
		return r;
	}

	public R visitAssume(Stmt.Assume stmt) {
		R operand = visitExpression(stmt.getCondition());
		return constructAssume(stmt,operand);
	}

	public R visitBlock(Stmt.Block stmt) {
		ArrayList<R> r = new ArrayList<>();
		for(int i=0;i!=stmt.size();++i) {
			r.add(visitStatement(stmt.get(i)));
		}
		return constructBlock(stmt,r);
	}

	public R visitDebug(Stmt.Debug stmt) {
		R operand = visitExpression(stmt.getOperand());
		return constructDebug(stmt,operand);
	}

	public R visitDoWhile(Stmt.DoWhile stmt) {
		R body = visitStatement(stmt.getBody());
		R condition = visitExpression(stmt.getCondition());
		List<R> invariants = visitExpressions(stmt.getInvariant());
		return constructDoWhile(stmt,condition,invariants,body);
	}

	public R visitFor(Stmt.For stmt) {
		ArrayList<R> ranges = new ArrayList<>();
		R var = visitExpression(stmt.getVariable().getInitialiser());
		List<R> invariant = visitExpressions(stmt.getInvariant());
		R body = visitStatement(stmt.getBody());
		return constructFor(stmt,var,invariant,body);
	}


	public R visitIfElse(Stmt.IfElse stmt) {
		R condition = visitExpression(stmt.getCondition());
		R trueBranch = visitStatement(stmt.getTrueBranch());
		R falseBranch = bottom();
		if(stmt.hasFalseBranch()) {
			falseBranch = visitStatement(stmt.getFalseBranch());
		}
		return constructIfElse(stmt,condition,trueBranch,falseBranch);
	}


	public R visitInitialiser(Stmt.Initialiser stmt) {
		R init = bottom();
		if(stmt.hasInitialiser()) {
			init = visitExpression(stmt.getInitialiser());
		}
		return constructInitialiser(stmt,init);
	}

	public R visitNamedBlock(Stmt.NamedBlock stmt) {
		R body = visitStatement(stmt.getBlock());
		return constructNamedBlock(stmt,body);
	}

	public R visitReturn(Stmt.Return stmt) {
		R rv = bottom();
		if(stmt.hasReturn()) {
			rv = visitExpression(stmt.getReturn());
		}
		return constructReturn(stmt,rv);
	}

	public R visitSwitch(Stmt.Switch stmt) {
		R condition = visitExpression(stmt.getCondition());
		List<R> rs = new ArrayList<>();
		Tuple<Stmt.Case> cases = stmt.getCases();
		for(int i=0;i!=cases.size();++i) {
			rs.add(visitCase(cases.get(i)));
		}
		return constructSwitch(stmt,condition,rs);
	}

	public R visitCase(Stmt.Case stmt) {
		List<R> conditions = visitExpressions(stmt.getConditions());
		R body = visitStatement(stmt.getBlock());
		return constructCase(stmt,conditions,body);
	}

	public R visitWhile(Stmt.While stmt) {
		R condition = visitExpression(stmt.getCondition());
		List<R> invariants = visitExpressions(stmt.getInvariant());
		R body = visitStatement(stmt.getBody());
		return constructWhile(stmt,condition,invariants,body);
	}


	public R constructAssert(Stmt.Assert stmt, R operand) {
		return operand;
	}


	public R constructAssign(Stmt.Assign stmt, List<R> lvals, List<R> rvals) {
		return join(join(lvals),join(rvals));
	}

	public R constructAssume(Stmt.Assume stmt, R operand) {
		return operand;
	}

	public R constructBreak(Stmt.Break stmt) {
		return bottom();
	}

	public R constructBlock(Stmt.Block stmt, List<R> operands) {
		return join(operands);
	}

	public R constructContinue(Stmt.Continue stmt) {
		return bottom();
	}

	public R constructDebug(Stmt.Debug stmt, R operand) {
		return operand;
	}

	public R constructDoWhile(Stmt.DoWhile stmt, R condition, List<R> invariants, R body) {
		return join(condition, join(join(invariants), body));
	}

	public R constructFail(Stmt.Fail stmt) {
		return bottom();
	}

	public R constructFor(Stmt.For stmt, R var, List<R> invariants, R body) {
		return join(var, join(join(invariants), body));
	}

	public R constructIfElse(Stmt.IfElse stmt, R condition, R trueBranch, R falseBranch) {
		return join(condition, join(trueBranch, falseBranch));
	}

	public R constructInitialiser(Stmt.Initialiser stmt, R operand) {
		return operand;
	}

	public R constructNamedBlock(Stmt.NamedBlock stmt, R body) {
		return body;
	}

	public R constructReturn(Stmt.Return stmt, R operand) {
		return operand;
	}

	public R constructSwitch(Stmt.Switch stmt, R condition, List<R> cases) {
		return join(condition,join(cases));
	}

	public R constructSkip(Stmt.Skip stmt) {
		return bottom();
	}

	public R constructCase(Stmt.Case stmt, List<R> conditions, R body) {
		return join(join(conditions),body);
	}

	public R constructWhile(Stmt.While stmt, R condition, List<R> invariants, R body) {
		return join(condition, join(join(invariants), body));
	}


	public List<R> visitExpressions(Tuple<Expr> exprs) {
		ArrayList<R> r = new ArrayList<>();
		for (int i = 0; i != exprs.size(); ++i) {
			r.add(visitExpression(exprs.get(i)));
		}
		return r;
	}

	public R visitExpression(Expr expr) {
		switch (expr.getOpcode()) {
			// Terminals
			case EXPR_constant:
				return constructConstant((Expr.Constant) expr);
			case EXPR_indirectinvoke:
				return visitIndirectInvoke((Expr.IndirectInvoke) expr);
			case EXPR_lambdaaccess:
				return constructLambdaAccess((Expr.LambdaAccess) expr);
			case DECL_lambda:
				return visitLambda((Decl.Lambda) expr);
			case EXPR_staticvariable:
				return constructStaticVariableAccess((Expr.StaticVariableAccess) expr);
			case EXPR_variablecopy:
			case EXPR_variablemove:
				return constructVariableAccess((Expr.VariableAccess) expr);
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
			case EXPR_old:
			case EXPR_recordaccess:
			case EXPR_recordborrow:
			case EXPR_arraylength:
				return visitUnaryOperator((Expr.UnaryOperator) expr);
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
			case EXPR_integerexponent:
			case EXPR_bitwiseshl:
			case EXPR_bitwiseshr:
			case EXPR_arrayaccess:
			case EXPR_arrayborrow:
			case EXPR_arrayrange:
			case EXPR_recordupdate:
			case EXPR_arraygenerator:
				return visitBinaryOperator((Expr.BinaryOperator) expr);
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
				return visitNaryOperator((Expr.NaryOperator) expr);
			// Ternary Operators
			case EXPR_arrayupdate:
				return visitTernaryOperator((Expr.TernaryOperator) expr);
			default:
				throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public R visitUnaryOperator(Expr.UnaryOperator expr) {
		switch (expr.getOpcode()) {
			// Unary Operators
			case EXPR_cast:
				return visitCast((Expr.Cast) expr);
			case EXPR_integernegation:
				return visitIntegerNegation((Expr.IntegerNegation) expr);
			case EXPR_is:
				return visitIs((Expr.Is) expr);
			case EXPR_logicalnot:
				return visitLogicalNot((Expr.LogicalNot) expr);
			case EXPR_logicalexistential:
				return visitExistentialQuantifier((Expr.ExistentialQuantifier) expr);
			case EXPR_logicaluniversal:
				return visitUniversalQuantifier((Expr.UniversalQuantifier) expr);
			case EXPR_bitwisenot:
				return visitBitwiseComplement((Expr.BitwiseComplement) expr);
			case EXPR_dereference:
				return visitDereference((Expr.Dereference) expr);
			case EXPR_fielddereference:
				return visitFieldDereference((Expr.FieldDereference) expr);
			case EXPR_new:
				return visitNew((Expr.New) expr);
			case EXPR_old:
				return visitOld((Expr.Old) expr);
			case EXPR_recordaccess:
			case EXPR_recordborrow:
				return visitRecordAccess((Expr.RecordAccess) expr);
			case EXPR_arraylength:
				return visitArrayLength((Expr.ArrayLength) expr);
			default:
				throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public R visitBinaryOperator(Expr.BinaryOperator expr) {
		switch (expr.getOpcode()) {
			// Binary Operators
			case EXPR_equal:
				return visitEqual((Expr.Equal) expr);
			case EXPR_notequal:
				return visitNotEqual((Expr.NotEqual) expr);
			case EXPR_logicalimplication:
				return visitLogicalImplication((Expr.LogicalImplication) expr);
			case EXPR_logicaliff:
				return visitLogicalIff((Expr.LogicalIff) expr);
			case EXPR_integerlessthan:
				return visitIntegerLessThan((Expr.IntegerLessThan) expr);
			case EXPR_integerlessequal:
				return visitIntegerLessThanOrEqual((Expr.IntegerLessThanOrEqual) expr);
			case EXPR_integergreaterthan:
				return visitIntegerGreaterThan((Expr.IntegerGreaterThan) expr);
			case EXPR_integergreaterequal:
				return visitIntegerGreaterThanOrEqual((Expr.IntegerGreaterThanOrEqual) expr);
			case EXPR_integeraddition:
				return visitIntegerAddition((Expr.IntegerAddition) expr);
			case EXPR_integersubtraction:
				return visitIntegerSubtraction((Expr.IntegerSubtraction) expr);
			case EXPR_integermultiplication:
				return visitIntegerMultiplication((Expr.IntegerMultiplication) expr);
			case EXPR_integerdivision:
				return visitIntegerDivision((Expr.IntegerDivision) expr);
			case EXPR_integerremainder:
				return visitIntegerRemainder((Expr.IntegerRemainder) expr);
			case EXPR_integerexponent:
				return visitIntegerExponent((Expr.IntegerExponent) expr);
			case EXPR_bitwiseshl:
				return visitBitwiseShiftLeft((Expr.BitwiseShiftLeft) expr);
			case EXPR_bitwiseshr:
				return visitBitwiseShiftRight((Expr.BitwiseShiftRight) expr);
			case EXPR_arraygenerator:
				return visitArrayGenerator((Expr.ArrayGenerator) expr);
			case EXPR_arrayaccess:
			case EXPR_arrayborrow:
				return visitArrayAccess((Expr.ArrayAccess) expr);
			case EXPR_arrayrange:
				return visitArrayRange((Expr.ArrayRange) expr);
			case EXPR_recordupdate:
				return visitRecordUpdate((Expr.RecordUpdate) expr);
			default:
				throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public R visitTernaryOperator(Expr.TernaryOperator expr) {
		switch (expr.getOpcode()) {
			// Ternary Operators
			case EXPR_arrayupdate:
				return visitArrayUpdate((Expr.ArrayUpdate) expr);

			default:
				throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public R visitNaryOperator(Expr.NaryOperator expr) {
		switch (expr.getOpcode()) {
			// Nary Operators
			case EXPR_arrayinitialiser:
				return visitArrayInitialiser((Expr.ArrayInitialiser) expr);
			case EXPR_bitwiseand:
				return visitBitwiseAnd((Expr.BitwiseAnd) expr);
			case EXPR_bitwiseor:
				return visitBitwiseOr((Expr.BitwiseOr) expr);
			case EXPR_bitwisexor:
				return visitBitwiseXor((Expr.BitwiseXor) expr);
			case EXPR_invoke:
				return visitInvoke((Expr.Invoke) expr);
			case EXPR_logicaland:
				return visitLogicalAnd((Expr.LogicalAnd) expr);
			case EXPR_logicalor:
				return visitLogicalOr((Expr.LogicalOr) expr);
			case EXPR_recordinitialiser:
				return visitRecordInitialiser((Expr.RecordInitialiser) expr);
			case EXPR_tupleinitialiser:
				return visitTupleInitialiser((Expr.TupleInitialiser) expr);
			default:
				throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
		}
	}

	public R visitArrayAccess(Expr.ArrayAccess expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructArrayAccess(expr,lhs,rhs);
	}

	public R visitArrayLength(Expr.ArrayLength expr) {
		R r = visitExpression(expr.getOperand());
		return constructArrayLength(expr,r);
	}

	public R visitArrayGenerator(Expr.ArrayGenerator expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructArrayGenerator(expr,lhs,rhs);
	}

	public R visitArrayInitialiser(Expr.ArrayInitialiser expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructArrayInitialiser(expr, vs);
	}

	public R visitArrayRange(Expr.ArrayRange expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructArrayRange(expr,lhs,rhs);
	}

	public R visitArrayUpdate(Expr.ArrayUpdate expr) {
		R one = visitExpression(expr.getFirstOperand());
		R two = visitExpression(expr.getSecondOperand());
		R three = visitExpression(expr.getThirdOperand());
		return constructArrayUpdate(expr,one,two,three);
	}

	public R visitBitwiseComplement(Expr.BitwiseComplement expr) {
		R r = visitExpression(expr.getOperand());
		return constructBitwiseComplement(expr, r);
	}

	public R visitBitwiseAnd(Expr.BitwiseAnd expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructBitwiseAnd(expr, vs);
	}

	public R visitBitwiseOr(Expr.BitwiseOr expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructBitwiseOr(expr, vs);
	}

	public R visitBitwiseXor(Expr.BitwiseXor expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructBitwiseXor(expr, vs);
	}

	public R visitBitwiseShiftLeft(Expr.BitwiseShiftLeft expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructBitwiseShiftLeft(expr,lhs,rhs);
	}

	public R visitBitwiseShiftRight(Expr.BitwiseShiftRight expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructBitwiseShiftRight(expr,lhs,rhs);
	}

	public R visitCast(Expr.Cast expr) {
		R r = visitExpression(expr.getOperand());
		return constructCast(expr,r);
	}

	public R visitDereference(Expr.Dereference expr) {
		R r = visitExpression(expr.getOperand());
		return constructDereference(expr,r);
	}

	public R visitFieldDereference(Expr.FieldDereference expr) {
		R r = visitExpression(expr.getOperand());
		return constructFieldDereference(expr,r);
	}

	public R visitEqual(Expr.Equal expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructEqual(expr,lhs,rhs);
	}

	public R visitIntegerLessThan(Expr.IntegerLessThan expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerLessThan(expr,lhs,rhs);
	}

	public R visitIntegerLessThanOrEqual(Expr.IntegerLessThanOrEqual expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerLessThanOrEqual(expr,lhs,rhs);
	}

	public R visitIntegerGreaterThan(Expr.IntegerGreaterThan expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerGreaterThan(expr,lhs,rhs);
	}

	public R visitIntegerGreaterThanOrEqual(Expr.IntegerGreaterThanOrEqual expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerGreaterThanOrEqual(expr,lhs,rhs);
	}

	public R visitIntegerNegation(Expr.IntegerNegation expr) {
		R r = visitExpression(expr.getOperand());
		return constructIntegerNegation(expr,r);
	}

	public R visitIntegerAddition(Expr.IntegerAddition expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerAddition(expr,lhs,rhs);
	}

	public R visitIntegerSubtraction(Expr.IntegerSubtraction expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerSubtraction(expr,lhs,rhs);
	}

	public R visitIntegerMultiplication(Expr.IntegerMultiplication expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerMultiplication(expr,lhs,rhs);
	}

	public R visitIntegerDivision(Expr.IntegerDivision expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerDivision(expr,lhs,rhs);
	}

	public R visitIntegerRemainder(Expr.IntegerRemainder expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerRemainder(expr,lhs,rhs);
	}

	public R visitIntegerExponent(Expr.IntegerExponent expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructIntegerExponent(expr,lhs,rhs);
	}

	public R visitIs(Expr.Is expr) {
		R r = visitExpression(expr.getOperand());
		return constructIs(expr,r);
	}

	public R visitLambda(Decl.Lambda expr) {
		R r = visitExpression(expr.getBody());
		return constructLambda(expr,r);
	}

	public R visitLogicalAnd(Expr.LogicalAnd expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructLogicalAnd(expr, vs);
	}

	public R visitLogicalImplication(Expr.LogicalImplication expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructLogicalImplication(expr,lhs,rhs);
	}

	public R visitLogicalIff(Expr.LogicalIff expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructLogicalIff(expr,lhs,rhs);
	}

	public R visitLogicalNot(Expr.LogicalNot expr) {
		R r = visitExpression(expr.getOperand());
		return constructLogicalNot(expr,r);
	}

	public R visitLogicalOr(Expr.LogicalOr expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructLogicalOr(expr, vs);
	}

	public R visitExistentialQuantifier(Expr.ExistentialQuantifier expr) {
		ArrayList<R> ranges = new ArrayList<>();
		for (Decl.StaticVariable p : expr.getParameters()) {
			ranges.add(visitExpression(p.getInitialiser()));
		}
		R body = visitExpression(expr.getOperand());
		return constructExistentialQuantifier(expr, ranges, body);
	}

	public R visitUniversalQuantifier(Expr.UniversalQuantifier expr) {
		ArrayList<R> ranges = new ArrayList<>();
		for(Decl.StaticVariable p : expr.getParameters()) {
			ranges.add(visitExpression(p.getInitialiser()));
		}
		R body = visitExpression(expr.getOperand());
		return constructUniversalQuantifier(expr,ranges,body);
	}

	public R visitInvoke(Expr.Invoke expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructInvoke(expr, vs);
	}

	public R visitIndirectInvoke(Expr.IndirectInvoke expr) {
		R r = visitExpression(expr.getSource());
		List<R> vs = visitExpressions(expr.getArguments());
		return constructIndirectInvoke(expr, r, vs);
	}

	public R visitNew(Expr.New expr) {
		R r = visitExpression(expr.getOperand());
		return constructNew(expr,r);
	}

	public R visitOld(Expr.Old expr) {
		R r = visitExpression(expr.getOperand());
		return constructOld(expr,r);
	}

	public R visitNotEqual(Expr.NotEqual expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructNotEqual(expr,lhs,rhs);
	}

	public R visitRecordAccess(Expr.RecordAccess expr) {
		R r = visitExpression(expr.getOperand());
		return constructRecordAccess(expr,r);
	}

	public R visitRecordInitialiser(Expr.RecordInitialiser expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructRecordInitialiser(expr, vs);
	}

	public R visitRecordUpdate(Expr.RecordUpdate expr) {
		R lhs = visitExpression(expr.getFirstOperand());
		R rhs = visitExpression(expr.getSecondOperand());
		return constructRecordUpdate(expr,lhs,rhs);
	}

	public R visitTupleInitialiser(Expr.TupleInitialiser expr) {
		List<R> vs = visitExpressions(expr.getOperands());
		return constructTupleInitialiser(expr,vs);
	}

	public R constructArrayAccess(Expr.ArrayAccess expr, R source, R index) {
		return join(source,index);
	}

	public R constructArrayLength(Expr.ArrayLength expr, R source) {
		return source;
	}

	public R constructArrayGenerator(Expr.ArrayGenerator expr, R element, R length) {
		return join(element,length);
	}

	public R constructArrayInitialiser(Expr.ArrayInitialiser expr, List<R> operands) {
		return join(operands);
	}

	public R constructArrayRange(Expr.ArrayRange expr, R start, R end) {
		return join(start,end);
	}

	public R constructArrayUpdate(Expr.ArrayUpdate expr, R source, R index, R value) {
		return join(join(source, index), value);
	}

	public R constructBitwiseComplement(Expr.BitwiseComplement expr, R operand) {
		return operand;
	}

	public R constructBitwiseAnd(Expr.BitwiseAnd expr, List<R> operands) {
		return join(operands);
	}

	public R constructBitwiseOr(Expr.BitwiseOr expr, List<R> operands) {
		return join(operands);
	}

	public R constructBitwiseXor(Expr.BitwiseXor expr, List<R> operands) {
		return join(operands);
	}

	public R constructBitwiseShiftLeft(Expr.BitwiseShiftLeft expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructBitwiseShiftRight(Expr.BitwiseShiftRight expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructCast(Expr.Cast expr, R operand) {
		return operand;
	}

	public R constructConstant(Expr.Constant expr) {
		return bottom();
	}

	public R constructDereference(Expr.Dereference expr, R operand) {
		return operand;
	}

	public R constructFieldDereference(Expr.FieldDereference expr, R operand) {
		return operand;
	}

	public R constructEqual(Expr.Equal expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerLessThan(Expr.IntegerLessThan expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerLessThanOrEqual(Expr.IntegerLessThanOrEqual expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerGreaterThan(Expr.IntegerGreaterThan expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerGreaterThanOrEqual(Expr.IntegerGreaterThanOrEqual expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerNegation(Expr.IntegerNegation expr, R operand) {
		return operand;
	}

	public R constructIntegerAddition(Expr.IntegerAddition expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerSubtraction(Expr.IntegerSubtraction expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerMultiplication(Expr.IntegerMultiplication expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerDivision(Expr.IntegerDivision expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerRemainder(Expr.IntegerRemainder expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIntegerExponent(Expr.IntegerExponent expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructIs(Expr.Is expr, R operand) {
		return operand;
	}

	public R constructLogicalAnd(Expr.LogicalAnd expr, List<R> operands) {
		return join(operands);
	}

	public R constructLogicalImplication(Expr.LogicalImplication expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructLogicalIff(Expr.LogicalIff expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructLogicalNot(Expr.LogicalNot expr, R operand) {
		return operand;
	}

	public R constructLogicalOr(Expr.LogicalOr expr, List<R> operands) {
		return join(operands);
	}

	public R constructExistentialQuantifier(Expr.ExistentialQuantifier expr, List<R> ranges, R body) {
		return join(join(ranges),body);
	}

	public R constructUniversalQuantifier(Expr.UniversalQuantifier expr, List<R> ranges, R body) {
		return join(join(ranges),body);
	}

	public R constructInvoke(Expr.Invoke expr, List<R> operands) {
		return join(operands);
	}

	public R constructIndirectInvoke(Expr.IndirectInvoke expr, R source, List<R> operands) {
		return join(source, join(operands));
	}

	public R constructLambda(Decl.Lambda expr, R body) {
		return body;
	}

	public R constructLambdaAccess(Expr.LambdaAccess expr) {
		return bottom();
	}

	public R constructNew(Expr.New expr, R operand) {
		return operand;
	}

	public R constructOld(Expr.Old expr, R operand) {
		return operand;
	}

	public R constructNotEqual(Expr.NotEqual expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructRecordAccess(Expr.RecordAccess expr, R operand) {
		return operand;
	}

	public R constructRecordInitialiser(Expr.RecordInitialiser expr, List<R> operands) {
		return join(operands);
	}

	public R constructRecordUpdate(Expr.RecordUpdate expr, R lhs, R rhs) {
		return join(lhs,rhs);
	}

	public R constructStaticVariableAccess(Expr.StaticVariableAccess expr) {
		return bottom();
	}

	public R constructVariableAccess(Expr.VariableAccess expr) {
		return bottom();
	}

	public R constructTupleInitialiser(Expr.TupleInitialiser expr, List<R> operands) {
		return join(operands);
	}

	public abstract R join(List<R> operands);

	public abstract R join(R lhs, R rhs);

	public abstract R bottom();
}