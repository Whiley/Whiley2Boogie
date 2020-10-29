// Copyright 2020 The Whiley Project Developers
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
package wyboogie.tasks;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;
import wyboogie.core.BoogieFile.Expr.Constant;
import wyboogie.core.BoogieFile.LVal;
import wybs.lang.Build.Meter;
import wyfs.util.Pair;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Decl.*;
import wyil.lang.WyilFile.Expr.*;
import wyil.lang.WyilFile.Stmt.*;
import wyil.util.AbstractTranslator;
import wyil.util.IncrementalSubtypingEnvironment;
import wyil.util.Subtyping;
import wyil.util.TypeMangler;

public class BoogieCompiler extends AbstractTranslator<Decl,Stmt,Expr> {
	/**
	 * Provides a standard mechanism for writing out type mangles.
	 */
	private final static TypeMangler mangler = new TypeMangler.Default();

	/**
	 * Provides a standard mechanism for checking whether two Whiley types are
	 * subtypes or not.
	 */
	private final static Subtyping.Environment subtyping = new IncrementalSubtypingEnvironment();

	private final BoogieFile boogieFile;

	public BoogieCompiler(Meter meter, BoogieFile target) {
		super(meter, subtyping);
		this.boogieFile = target;
	}

	public void visitModule(WyilFile wf) {
		// Translate local units
		for (Unit unit : wf.getModule().getUnits()) {
			for (WyilFile.Decl decl : unit.getDeclarations()) {
				BoogieFile.Decl d = visitDeclaration(decl);
				if (d != null) {
					boogieFile.getDeclarations().add(d);
				}
			}
		}
	}

	@Override
	public Decl constructImport(Import d) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Decl constructType(Type d, List<Expr> invariant) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Decl constructStaticVariable(StaticVariable d, Expr initialiser) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Decl constructProperty(Property decl, List<Expr> clauses) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Decl constructFunction(Function d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Decl constructMethod(Method d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		String mangled = d.getName().toString();
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		List<Decl.Parameter> returns = constructParameters(d.getReturns());
		return new Decl.Procedure(mangled, parameters, returns, precondition, postcondition, (Stmt.Block) body);
	}

	public List<Decl.Parameter> constructParameters(WyilFile.Tuple<WyilFile.Decl.Variable> params) {
		ArrayList<Decl.Parameter> ps = new ArrayList<>();
		for(int i=0;i!=params.size();++i) {
			ps.add(constructParameter(params.get(i)));
		}
		return ps;
	}

	public Decl.Parameter constructParameter(WyilFile.Decl.Variable ps) {
		BoogieFile.Type type = constructType(ps.getType());
		return new Decl.Parameter(ps.getName().get(), type);
	}

	@Override
	public Expr constructLambda(Lambda decl, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructAssert(Assert stmt, Expr condition) {
		return new Stmt.Assert(condition);
	}

	@Override
	public Stmt constructAssign(Assign stmt, List<Expr> lvals, List<Expr> rvals) {
		if(lvals.size() != 1 || rvals.size() != 1) {
			throw new UnsupportedOperationException("Multiple assignments not supported (yet)");
		}
		return new Stmt.Assignment((LVal) lvals.get(0), rvals.get(0));
	}

	@Override
	public Stmt constructAssume(Assume stmt, Expr condition) {
		return new Stmt.Assume(condition);
	}

	@Override
	public Stmt constructBlock(Block stmt, List<Stmt> stmts) {
		return new Stmt.Block(stmts);
	}

	@Override
	public Stmt constructBreak(Break stmt) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructContinue(Continue stmt) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructDebug(Debug stmt, Expr operand) {
		return new Stmt.Assert(new Expr.Constant(true));
	}

	@Override
	public Stmt constructDoWhile(DoWhile stmt, Stmt body, Expr condition, List<Expr> invariant) {
		Stmt loop = new Stmt.While(condition, invariant, (Stmt.Block) body);
		return new Stmt.Sequence(body, loop);
	}

	@Override
	public Stmt constructFail(Fail stmt) {
		return new Stmt.Assert(new Expr.Constant(false));
	}

	@Override
	public Stmt constructFor(For stmt, Pair<Expr, Expr> range, List<Expr> invariant, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructIfElse(IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch) {
		return new Stmt.IfElse(condition, (Stmt.Block) trueBranch, (Stmt.Block) falseBranch);
	}

	@Override
	public Stmt constructInitialiser(Initialiser stmt, Expr initialiser) {
		WyilFile.Tuple<Variable> vars = stmt.getVariables();
		if(vars.size() != 1) {
			throw new UnsupportedOperationException("Multiple initialisers not supported (yet)");
		}
		String name = vars.get(0).getName().toString();
		BoogieFile.Type type = constructType(vars.get(0).getType());
		//
		Stmt.VariableDeclarations decl = new Stmt.VariableDeclarations(name, type);
		//
		if(initialiser == null) {
			return decl;
		} else {
			Stmt.Assignment init = new Stmt.Assignment(new Expr.VariableAccess(name),initialiser);
			return new Stmt.Sequence(decl,init);
		}
	}

	@Override
	public Stmt constructNamedBlock(NamedBlock stmt, List<Stmt> stmts) {
		return new Stmt.Block(stmts);
	}

	@Override
	public Stmt constructReturn(Return stmt, Expr ret) {
		if (ret != null) {
			// Identify enclosing function or method to figure out names of return
			// variables.
			Callable enclosing = stmt.getAncestor(WyilFile.Decl.FunctionOrMethod.class);
			WyilFile.Tuple<Variable> returns = enclosing.getReturns();
			if (returns.size() != 1) {
				// TODO: implement this!
				throw new IllegalArgumentException("Missing support for multiple returns");
			} else {
				String rv = returns.get(0).getName().get();
				Stmt s1 = new Stmt.Assignment(new Expr.VariableAccess(rv), ret);
				Stmt s2 = new Stmt.Return();
				return new Stmt.Sequence(s1, s2);
			}
		} else {
			return new Stmt.Return();
		}
	}

	@Override
	public Stmt constructSkip(Skip stmt) {
		return new Stmt.Assert(new Expr.Constant(true));
	}

	@Override
	public Stmt constructSwitch(Switch stmt, Expr condition, List<Pair<List<Expr>, Stmt>> cases) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructWhile(While stmt, Expr condition, List<Expr> invariant, Stmt body) {
		return new Stmt.While(condition, invariant, (Stmt.Block) body);
	}

	@Override
	public Expr constructArrayAccessLVal(ArrayAccess expr, Expr source, Expr index) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructDereferenceLVal(Dereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructFieldDereferenceLVal(FieldDereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructRecordAccessLVal(RecordAccess expr, Expr source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructTupleInitialiserLVal(TupleInitialiser expr, List<Expr> source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructVariableAccessLVal(VariableAccess expr) {
		return constructVariableAccess(expr);
	}

	@Override
	public Expr constructArrayAccess(ArrayAccess expr, Expr source, Expr index) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructArrayLength(ArrayLength expr, Expr source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructArrayGenerator(ArrayGenerator expr, Expr value, Expr length) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructArrayInitialiser(ArrayInitialiser expr, List<Expr> values) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseComplement(BitwiseComplement expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseAnd(BitwiseAnd expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseOr(BitwiseOr expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseXor(BitwiseXor expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseShiftLeft(BitwiseShiftLeft expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseShiftRight(BitwiseShiftRight expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructCast(Cast expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructConstant(WyilFile.Expr.Constant expr) {
		WyilFile.Value v = expr.getValue();
		switch(v.getOpcode()) {
		case WyilFile.ITEM_bool: {
			boolean b = ((WyilFile.Value.Bool) v).get();
			return b ? Expr.Constant.TRUE : Expr.Constant.FALSE;
		}
		case WyilFile.ITEM_int: {
			BigInteger i = ((WyilFile.Value.Int) v).get();
			return new Expr.Constant(i);
		}
		default:
			throw new IllegalArgumentException("unknown constant encountered (" + expr.getClass().getName() + ")");
		}
	}

	@Override
	public Expr constructDereference(Dereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructFieldDereference(FieldDereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructEqual(Equal expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.EQ, lhs, rhs);
	}

	@Override
	public Expr constructIntegerLessThan(IntegerLessThan expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LT, lhs, rhs);
	}

	@Override
	public Expr constructIntegerLessThanOrEqual(IntegerLessThanOrEqual expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LTEQ, lhs, rhs);
	}

	@Override
	public Expr constructIntegerGreaterThan(IntegerGreaterThan expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.GT, lhs, rhs);
	}

	@Override
	public Expr constructIntegerGreaterThanOrEqual(IntegerGreaterThanOrEqual expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.GTEQ, lhs, rhs);
	}

	@Override
	public Expr constructIntegerNegation(IntegerNegation expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerAddition(IntegerAddition expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.ADD, lhs, rhs);
	}

	@Override
	public Expr constructIntegerSubtraction(IntegerSubtraction expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.SUB, lhs, rhs);
	}

	@Override
	public Expr constructIntegerMultiplication(IntegerMultiplication expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.MUL, lhs, rhs);
	}

	@Override
	public Expr constructIntegerDivision(IntegerDivision expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.DIV, lhs, rhs);
	}

	@Override
	public Expr constructIntegerRemainder(IntegerRemainder expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.REM, lhs, rhs);
	}

	@Override
	public Expr constructIs(Is expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalAnd(LogicalAnd expr, List<Expr> operands) {
		return new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, operands);
	}

	@Override
	public Expr constructLogicalImplication(LogicalImplication expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.IF, lhs, rhs);
	}

	@Override
	public Expr constructLogicalIff(LogicalIff expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.IFF, lhs, rhs);
	}

	@Override
	public Expr constructLogicalNot(LogicalNot expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalOr(LogicalOr expr, List<Expr> operands) {
		return new Expr.NaryOperator(Expr.NaryOperator.Kind.OR, operands);
	}

	@Override
	public Expr constructExistentialQuantifier(ExistentialQuantifier expr, List<Pair<Expr, Expr>> ranges, Expr body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructUniversalQuantifier(UniversalQuantifier expr, List<Pair<Expr, Expr>> ranges, Expr body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructInvoke(Invoke expr, List<Expr> arguments) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIndirectInvoke(IndirectInvoke expr, Expr source, List<Expr> arguments) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLambdaAccess(LambdaAccess expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructNew(New expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructNotEqual(NotEqual expr, Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.NEQ, lhs, rhs);
	}

	@Override
	public Expr constructRecordAccess(RecordAccess expr, Expr source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructRecordInitialiser(RecordInitialiser expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructTupleInitialiser(TupleInitialiser expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructStaticVariableAccess(StaticVariableAccess expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructVariableAccess(VariableAccess expr) {
		return new Expr.VariableAccess(expr.getVariableDeclaration().getName().toString());
	}

	public BoogieFile.Type constructType(WyilFile.Type type) {
		// FIXME: this should be moved into AbstractTranslator.
		switch(type.getOpcode()) {
		case WyilFile.TYPE_bool:
			return BoogieFile.Type.Bool;
		case WyilFile.TYPE_int:
			return BoogieFile.Type.Int;
		default:
			throw new IllegalArgumentException("unknown type encoutnered (" + type.getClass().getName() + ")");
		}
	}

	@Override
	public Stmt applyImplicitCoercion(wyil.lang.WyilFile.Type target, wyil.lang.WyilFile.Type source, Stmt expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}
}
