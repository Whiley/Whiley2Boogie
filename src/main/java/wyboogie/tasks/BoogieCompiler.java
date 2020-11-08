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
import java.util.List;

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;
import wyboogie.core.BoogieFile.LVal;
import wybs.lang.Build.Meter;
import wyfs.util.Pair;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Decl.*;
import wyil.lang.WyilFile.Expr.*;
import wyil.lang.WyilFile.Stmt.*;
import wyil.util.AbstractTranslator;
import wyil.util.AbstractVisitor;
import wyil.util.IncrementalSubtypingEnvironment;
import wyil.util.Subtyping;
import wyil.util.TypeMangler;

public class BoogieCompiler extends AbstractTranslator<Decl, Stmt, Expr> {
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
		// FIXME: mangling required here
		WyilFile.Decl.Variable var = d.getVariableDeclaration();
		String name = d.getName().get();
		Decl t = new Decl.TypeSynonym(name, constructType(var.getType()));
		//
		if (invariant.isEmpty()) {
			return t;
		} else {
			// FIXME: this translation is not valid.
			Decl.Parameter p = new Decl.Parameter(var.getName().get(), new BoogieFile.Type.Synonym(name));
			Expr inv = new Expr.Quantifier(true, new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, invariant), p);
			Decl a = new Decl.Axiom(inv);
			return new Decl.Sequence(t, a);
		}
	}

	@Override
	public Decl constructStaticVariable(StaticVariable d, Expr initialiser) {
		BoogieFile.Type type = constructType(d.getType());
		// FIXME: mangling required here.
		String name = d.getName().get();
		//
		if (d.getModifiers().match(WyilFile.Modifier.Final.class) != null) {
			// Final static variables declared as constants with corresponding axiom
			Decl d1 = new Decl.Constant(name, type);
			Decl d2 = new Decl.Axiom(
					new Expr.BinaryOperator(Expr.BinaryOperator.Kind.EQ, new Expr.VariableAccess(name), initialiser));
			return new Decl.Sequence(d1, d2);
		} else if (initialiser == null) {
			return new Decl.Variable(name, type, null);
		} else {
			throw new IllegalArgumentException("non-final static variables with initialisers not supported");
		}
	}

	@Override
	public Decl constructProperty(Property d, List<Expr> clauses) {
		// TODO: implement name mangling
		String name = d.getName().toString();
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		Expr body = new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, clauses);
		return new Decl.Function(name, parameters, BoogieFile.Type.Bool, body);
	}

	@Override
	public Decl constructFunction(Function d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		// TODO: implement name mangling
		String name = d.getName().toString();
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		List<Decl.Parameter> returns = constructParameters(d.getReturns());
		return new Decl.Procedure(name, parameters, returns, precondition, postcondition, (Stmt.Block) body);
	}

	@Override
	public Decl constructMethod(Method d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		// TODO: implement name mangling
		String name = d.getName().toString();
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		List<Decl.Parameter> returns = constructParameters(d.getReturns());
		return new Decl.Procedure(name, parameters, returns, precondition, postcondition, (Stmt.Block) body);
	}

	public List<Decl.Parameter> constructParameters(WyilFile.Tuple<WyilFile.Decl.Variable> params) {
		ArrayList<Decl.Parameter> ps = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
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
		if (lvals.size() != 1 || rvals.size() != 1) {
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
		WyilFile.Stmt loop = getEnclosingLoop(stmt);
		String label = "BREAK_" + loop.getIndex();
		return new Stmt.Goto(label);
	}

	@Override
	public Stmt constructContinue(Continue stmt) {
		WyilFile.Stmt loop = getEnclosingLoop(stmt);
		String label = "CONTINUE_" + loop.getIndex();
		return new Stmt.Goto(label);
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
		// Determine name of loop variable
		String name = stmt.getVariable().getName().get();
		Expr.VariableAccess var = new Expr.VariableAccess(name);
		// Extract loop contents so it can be appended later
		ArrayList<Stmt> loopBody = new ArrayList<>(((Stmt.Block)body).getAll());
		// Declare index variable
		// FIXME: could include invariant on this declaration to ensure within range
		Stmt.VariableDeclarations decl = new Stmt.VariableDeclarations(name, BoogieFile.Type.Int);
		// Initialise index variable with first value from range
		Stmt.Assignment init = new Stmt.Assignment(var, range.first());
		Expr condition = new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LT, var, range.second());
		// Add variable increment for completeness
		loopBody.add(new Stmt.Assignment(var,
				new Expr.BinaryOperator(Expr.BinaryOperator.Kind.ADD, var, new Expr.Constant(1))));
		// Construct the loop
		Stmt.While loop = new Stmt.While(condition, invariant, new Stmt.Block(loopBody));
		// Done.
		return new Stmt.Sequence(decl, init, loop);
	}

	@Override
	public Stmt constructIfElse(IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch) {
		return new Stmt.IfElse(condition, (Stmt.Block) trueBranch, (Stmt.Block) falseBranch);
	}

	@Override
	public Stmt constructInitialiser(Initialiser stmt, Expr initialiser) {
		WyilFile.Tuple<Variable> vars = stmt.getVariables();
		if (vars.size() != 1) {
			throw new UnsupportedOperationException("Multiple initialisers not supported (yet)");
		}
		String name = vars.get(0).getName().toString();
		BoogieFile.Type type = constructType(vars.get(0).getType());
		//
		Stmt.VariableDeclarations decl = new Stmt.VariableDeclarations(name, type);
		//
		if (initialiser == null) {
			return decl;
		} else {
			Stmt.Assignment init = new Stmt.Assignment(new Expr.VariableAccess(name), initialiser);
			return new Stmt.Sequence(decl, init);
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
		boolean needContinueLabel = containsContinueOrBreak(stmt, false);
		boolean needBreakLabel = containsContinueOrBreak(stmt, true);
		Stmt.While s = new Stmt.While(condition, invariant, (Stmt.Block) body);
		// Handle need for continue / break
		if (needContinueLabel && needBreakLabel) {
			Stmt.Label continueLabel = new Stmt.Label("CONTINUE_" + stmt.getIndex());
			Stmt.Label breakLabel = new Stmt.Label("BREAK_" + stmt.getIndex());
			return new Stmt.Sequence(continueLabel, s, breakLabel);
		} else if (needContinueLabel) {
			Stmt.Label continueLabel = new Stmt.Label("CONTINUE_" + stmt.getIndex());
			return new Stmt.Sequence(continueLabel, s);
		} else if (needBreakLabel) {
			Stmt.Label breakLabel = new Stmt.Label("BREAK_" + stmt.getIndex());
			return new Stmt.Sequence(s, breakLabel);
		} else {
			return s;
		}
	}

	@Override
	public Expr constructArrayAccessLVal(ArrayAccess expr, Expr source, Expr index) {
		return new Expr.Access(source, index);
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
		return new Expr.Access(source, index);
	}

	@Override
	public Expr constructArrayLength(ArrayLength expr, Expr source) {
		return new Expr.Invoke("length", source);
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
		switch (v.getOpcode()) {
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
		WyilFile.Tuple<StaticVariable> params = expr.getParameters();
		List<Decl.Parameter> ps = new ArrayList<>();
		List<Expr> clauses = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			Pair<Expr, Expr> ith = ranges.get(i);
			String name = params.get(i).getName().get();
			ps.add(new Decl.Parameter(name, BoogieFile.Type.Int));
			clauses.add(
					new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LTEQ, ith.first(), new Expr.VariableAccess(name)));
			clauses.add(
					new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LT, new Expr.VariableAccess(name), ith.second()));
		}
		clauses.add(body);
		return new Expr.Quantifier(false, new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, clauses), ps);
	}

	@Override
	public Expr constructUniversalQuantifier(UniversalQuantifier expr, List<Pair<Expr, Expr>> ranges, Expr body) {
		WyilFile.Tuple<StaticVariable> params = expr.getParameters();
		List<Decl.Parameter> ps = new ArrayList<>();
		List<Expr> clauses = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			Pair<Expr, Expr> ith = ranges.get(i);
			String name = params.get(i).getName().get();
			ps.add(new Decl.Parameter(name, BoogieFile.Type.Int));
			clauses.add(
					new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LTEQ, ith.first(), new Expr.VariableAccess(name)));
			clauses.add(
					new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LT, new Expr.VariableAccess(name), ith.second()));
		}
		Expr lhs = new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, clauses);
		return new Expr.Quantifier(true, new Expr.BinaryOperator(Expr.BinaryOperator.Kind.IF, lhs, body), ps);
	}

	@Override
	public Expr constructInvoke(Invoke expr, List<Expr> arguments) {
		// FIXME: mangling required here
		String name = expr.getLink().getName().toString();
		return new Expr.Invoke(name, arguments);
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
		// FIXME: name mangling required here
		return new Expr.VariableAccess(expr.getLink().getName().toString().toString());
	}

	@Override
	public Expr constructVariableAccess(VariableAccess expr) {
		return new Expr.VariableAccess(expr.getVariableDeclaration().getName().toString());
	}

	public BoogieFile.Type constructType(WyilFile.Type type) {
		// FIXME: this should be moved into AbstractTranslator.
		switch (type.getOpcode()) {
		case WyilFile.TYPE_bool:
			return BoogieFile.Type.Bool;
		case WyilFile.TYPE_int:
			return BoogieFile.Type.Int;
		case WyilFile.TYPE_nominal:
			return constructNominalType((WyilFile.Type.Nominal) type);
		case WyilFile.TYPE_array:
			return constructArrayType((WyilFile.Type.Array) type);
		default:
			throw new IllegalArgumentException("unknown type encoutnered (" + type.getClass().getName() + ")");
		}
	}

	public BoogieFile.Type constructArrayType(WyilFile.Type.Array type) {
		BoogieFile.Type t = constructType(type.getElement());
		return new BoogieFile.Type.Map(BoogieFile.Type.Int, t);
	}

	public BoogieFile.Type constructNominalType(WyilFile.Type.Nominal type) {
		// FIXME: mangling required here
		String name = type.getLink().getName().toString();
		return new BoogieFile.Type.Synonym(name);
	}

	@Override
	public Stmt applyImplicitCoercion(wyil.lang.WyilFile.Type target, wyil.lang.WyilFile.Type source, Stmt expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	/**
	 * Check whether a given (loop) statement contains a break or continue (which is
	 * not contained within another). Observer that only the outermost loop counts,
	 * and we should terminate the search for any inner loops. To do this, we use a
	 * simple visitor over the abstract tree.
	 *
	 * @param s
	 * @param isBreak
	 * @return
	 */
	private boolean containsContinueOrBreak(WyilFile.Stmt s, boolean isBreak) {
		//
		return new AbstractVisitor(meter) {
			public boolean result = false;

			public boolean run() {
				super.visitStatement(s);
				return result;
			}

			@Override
			public void visitBreak(WyilFile.Stmt.Break stmt) {
				if (isBreak) {
					result = true;
				}
			}

			@Override
			public void visitContinue(WyilFile.Stmt.Continue stmt) {
				if (!isBreak) {
					result = true;
				}
			}

			@Override
			public void visitDoWhile(WyilFile.Stmt.DoWhile stmt) {
				if (stmt != s) {
					return;
				} else {
					super.visitDoWhile(stmt);
				}
			}

			@Override
			public void visitFor(WyilFile.Stmt.For stmt) {
				if (stmt != s) {
					return;
				} else {
					super.visitFor(stmt);
				}
			}

			@Override
			public void visitLambda(WyilFile.Decl.Lambda stmt) {
				if (stmt != s) {
					return;
				} else {
					super.visitLambda(stmt);
				}
			}

			@Override
			public void visitWhile(WyilFile.Stmt.While stmt) {
				if (stmt != s) {
					return;
				} else {
					super.visitWhile(stmt);
				}
			}
		}.run();
	}

	/**
	 * Find the enclosing loop of a given statement. This could be deprecated in the
	 * future using a better query mechanism for ASTs in <code>WyilFile</code>.
	 *
	 * @param stmt
	 * @return
	 */
	private static WyilFile.Stmt getEnclosingLoop(WyilFile.Stmt stmt) {
		if (stmt == null) {
			throw new IllegalArgumentException("no enclosing loop found");
		} else if (stmt instanceof WyilFile.Stmt.Loop || stmt instanceof WyilFile.Stmt.For) {
			return stmt;
		} else {
			return getEnclosingLoop(stmt.getParent(WyilFile.Stmt.class));
		}
	}
}
