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
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;
import wyboogie.core.BoogieFile.LVal;
import wyboogie.util.AbstractTranslator;
import wybs.lang.Build.Meter;
import wyfs.util.Pair;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Decl.*;
import wyil.lang.WyilFile.Expr.*;
import wyil.lang.WyilFile.Stmt.*;
import wyil.util.AbstractVisitor;
import wyil.util.IncrementalSubtypingEnvironment;
import wyil.util.Subtyping;
import wyil.util.TypeMangler;
import wyil.util.AbstractTranslator.Environment;

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
		// Add general axioms
		boogieFile.getDeclarations().addAll(constructAxioms(wf));
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
		return new Decl.Sequence();
	}

	@Override
	public Decl constructType(Type d, List<Expr> invariant) {
		WyilFile.Decl.Variable var = d.getVariableDeclaration();
		// Apply name mangling
		String name = toMangledName(d);
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
		// Apply name mangling
		String name = toMangledName(d);
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
		// Apply name mangling
		String name = toMangledName(d);
		//
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		Expr body = new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, clauses);
		return new Decl.Function(name, parameters, BoogieFile.Type.Bool, body);
	}

	@Override
	public Decl constructFunction(Function d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		// Apply name mangling
		String name = toMangledName(d);
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		List<Decl.Parameter> returns = constructParameters(d.getReturns());
		ArrayList<Decl.Parameter> parametersAndReturns = new ArrayList<>();
		parametersAndReturns.addAll(parameters);
		parametersAndReturns.addAll(returns);
		// FIXME: obviously broken for multiple returns!
		BoogieFile.Type returnType = returns.get(0).getType();
		// Construct function representation precondition
		Decl.Function pre = new Decl.Function(name + "#pre", parameters, BoogieFile.Type.Bool, and(precondition));
		// Construct function representation postcondition
		Decl.Function post = new Decl.Function(name + "#post", parametersAndReturns, BoogieFile.Type.Bool, and(postcondition));
		// Construct prototype which can be called from expressions.
		Decl.Function prototype = new Decl.Function(name, parameters, returnType);
		// Construct implementation which can be checked against its specification.
		Decl.Procedure impl = new Decl.Procedure(name + "#impl", parameters, returns, precondition, postcondition,
				(Stmt.Block) body);
		// Done
		return new Decl.Sequence(prototype, pre, post, impl);
	}

	@Override
	public Decl constructMethod(Method d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		// Apply name mangling
		String name = toMangledName(d);
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
			//return assertPreconditions(new Stmt.Sequence(decl, init));
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
		ArrayList<Stmt> stmts = new ArrayList<>();
		String breakLabel = "SWITCH_" + stmt.getIndex() + "_BREAK";
		// Construct case labels
		String[] labels = new String[cases.size()];
		for (int i = 0; i != labels.length; ++i) {
			labels[i] = "SWITCH_" + stmt.getIndex() + "_" + i;
		}
		// Construct non-deterministic goto
		stmts.add(new Stmt.Goto(labels));
		// Construct cases
		for (int i = 0; i != labels.length; ++i) {
			Pair<List<Expr>, Stmt> ith = cases.get(i);
			List<Expr> ith_first = ith.first();
			ArrayList<Expr> labs = new ArrayList<>();
			for (int j = 0; j != ith_first.size(); ++j) {
				labs.add(new Expr.BinaryOperator(Expr.BinaryOperator.Kind.EQ, condition, ith_first.get(j)));
			}
			stmts.add(new Stmt.Label(labels[i]));
			stmts.add(new Stmt.Assume(new Expr.NaryOperator(Expr.NaryOperator.Kind.OR, labs)));
			stmts.add(ith.second());
			stmts.add(new Stmt.Goto(breakLabel));
		}
		//
		return new Stmt.Sequence(stmts);
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
		return new Expr.DictionaryAccess(source, index);
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
		return unbox(expr.getType(),new Expr.DictionaryAccess(source, index));
	}

	@Override
	public Expr constructArrayLength(ArrayLength expr, Expr source) {
		return new Expr.Invoke("WArray#Length", source);
	}

	@Override
	public Expr constructArrayGenerator(ArrayGenerator expr, Expr value, Expr length) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructArrayInitialiser(ArrayInitialiser expr, List<Expr> values) {
		WyilFile.Type elementType = expr.getType().as(WyilFile.Type.Array.class).getElement();
		Expr arr = invoke("WArray#Empty",constant(values.size()));
		//
		for (int i = 0; i != values.size(); ++i) {
			Expr ith = box(elementType, values.get(i));
			arr = new Expr.DictionaryUpdate(arr, new Expr.Constant(i), ith);
		}
		//
		return arr;
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
		// Box operands for simplicity
		lhs = box(expr.getFirstOperand().getType(),lhs);
		rhs = box(expr.getSecondOperand().getType(),rhs);
		// Done
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
		return new Expr.UnaryOperator(Expr.UnaryOperator.Kind.NEG, operand);
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
	public List<Stmt> visitIntegerDivisionPrecondition(IntegerDivision expr, Environment environment) {
		// Generate suitable preconditions.
		List<Stmt> preconds = super.visitIntegerDivisionPrecondition(expr, environment);
		Expr rhs = visitExpression(expr.getSecondOperand(), environment);
		return append(preconds, new Stmt.Assert(neq(rhs, constant(0))));
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
		Callable c = expr.getLink().getTarget();
		// Apply name mangling
		String name = toMangledName(expr.getLink().getTarget());
		//
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
		// Box operands for simplicity
		lhs = box(expr.getFirstOperand().getType(),lhs);
		rhs = box(expr.getSecondOperand().getType(),rhs);
		// Done
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.NEQ, lhs, rhs);
	}

	@Override
	public Expr constructRecordAccess(RecordAccess expr, Expr source) {
		Expr field = var("$" + expr.getField().get());
		return unbox(expr.getType(), new Expr.DictionaryAccess(source, field));
	}

	@Override
	public Expr constructRecordInitialiser(RecordInitialiser expr, List<Expr> operands) {
		WyilFile.Tuple<WyilFile.Expr> values = expr.getOperands();
		WyilFile.Tuple<WyilFile.Identifier> fields = expr.getFields();
		//
		Expr rec = new Expr.VariableAccess("WRecord#Empty");
		//
		for (int i = 0; i != operands.size(); ++i) {
			Expr ith = box(values.get(i).getType(), operands.get(i));
			String field = "$" + fields.get(i).get();
			rec = new Expr.DictionaryUpdate(rec, new Expr.VariableAccess(field), ith);
		}
		//
		return rec;
	}

	@Override
	public Expr constructTupleInitialiser(TupleInitialiser expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructStaticVariableAccess(StaticVariableAccess expr) {
		// Apply name mangling
		String name = toMangledName(expr.getLink().getTarget());
		// Done
		return new Expr.VariableAccess(name);
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
		case WyilFile.TYPE_record:
			return constructRecordType((WyilFile.Type.Record) type);
		default:
			throw new IllegalArgumentException("unknown type encoutnered (" + type.getClass().getName() + ")");
		}
	}

	public BoogieFile.Type constructArrayType(WyilFile.Type.Array type) {
		return IntWVals;
	}

	public BoogieFile.Type constructRecordType(WyilFile.Type.Record type) {
		return WFieldWVals;
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
	 * Generate declarations for all axioms used within the Boogie translation.
	 *
	 * @return
	 */
	private List<Decl> constructAxioms(WyilFile wf) {
		ArrayList<Decl> axioms = new ArrayList<>();
		//
		axioms.add(new Decl.LineComment("=== Begin Preamble ==="));
		// Define the top-level Whiley value which contains all others.
		axioms.add(new Decl.TypeSynonym("WVal", null));
		// Define the top-level Whiley type which contains all others.
		axioms.add(new Decl.TypeSynonym("WType", null));
		// Add void constant
		axioms.add(new Decl.Constant(true, "WVoid", WVal));
		// Add all int axioms
		axioms.addAll(constructIntAxioms(wf));
		// Add all array axioms
		axioms.addAll(constructArrayAxioms(wf));
		// Add all record axioms
		axioms.addAll(constructRecordAxioms(wf));
		//
		axioms.add(new Decl.LineComment("=== End Preamble ==="));
		// Done
		return axioms;
	}

	/**
	 * Construct axioms and functions relevant to integer types.
	 *
	 * @param wf
	 * @return
	 */
	private List<Decl> constructIntAxioms(WyilFile wf) {
		Decl header = new Decl.LineComment("Integers");
		Decl.Function fromInt = fun("fromInt", BoogieFile.Type.Int, WVal);
		Decl.Function toInt = fun("toInt", WVal, BoogieFile.Type.Int);
		// Establish connection between toInt and fromInt
		Decl.Axiom axiom1 = new Decl.Axiom(
				forall("i", BoogieFile.Type.Int, eq(invoke("toInt", invoke("fromInt", var("i"))), var("i"))));
		return Arrays.asList(header,fromInt,toInt,axiom1);
	}

	/**
	 * Construct axioms relevant to array types.
	 *
	 * @return
	 */
	private List<Decl> constructArrayAxioms(WyilFile wf) {
		// NOTE: we could reduce the amount of boxing / unboxing necessary by generating
		// custom array types for each different array type encountered.
		ArrayList<Decl> decls = new ArrayList<>();
		decls.add(new Decl.LineComment("Arrays"));
		decls.add(fun("WArray#Length", IntWVals, BoogieFile.Type.Int));
		// Enforce array length is non-negative
		decls.add(new Decl.Axiom(forall("a", IntWVals, lteq(constant(0), invoke("WArray#Length", var("a"))))));
		// Empty arrays
		decls.add(fun("WArray#Empty", BoogieFile.Type.Int, IntWVals));
		// Ensure that all elements outside array length are void
		decls.add(new Decl.Axiom(
				forall("l", BoogieFile.Type.Int, "i", BoogieFile.Type.Int, or(and(lteq(constant(0), var("i")),lt(var("i"),var("l"))),
						eq(get(invoke("WArray#Empty", var("l")), var("i")), var("WVoid"))))));
		// Relate empty array with its length
		decls.add(new Decl.Axiom(forall("a", IntWVals, "l", BoogieFile.Type.Int,
				or(neq(invoke("WArray#Empty", var("l")), var("a")), eq(invoke("WArray#Length", var("a")), var("l"))))));
		// Done
		return decls;
	}

	/**
	 * Construct axioms relevant to record types. An import issue is to determine
	 * the full set of field names which are in play.
	 *
	 * @return
	 */
	private List<Decl> constructRecordAxioms(WyilFile wf) {
		ArrayList<Decl> decls = new ArrayList<>();
		decls.add(new Decl.LineComment("Fields"));
		// Defines the type of all fields
		decls.add(new Decl.TypeSynonym("WField", null));
		// Add all known field names
		for(String field : determineFieldNames(wf)) {
			String name = "$" + field;
			decls.add(new Decl.Constant(true, name, WField));
		}
		//
		decls.add(new Decl.LineComment("Records"));
		// Defines the empty record (i.e. the base from which all other records are
		// constructed).
		decls.add(new Decl.Constant(true, "WRecord#Empty", WFieldWVals));
		decls.add(new Decl.Axiom(forall("f", WField, eq(get(var("WRecord#Empty"), var("f")), var("WVoid")))));
		// Done
		return decls;
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

	/**
	 * Box a given expression into a <code>WVal</code> as necessary.
	 *
	 * @param type
	 * @param e
	 * @return
	 */
	private static Expr box(WyilFile.Type type, Expr e) {
		switch (type.getOpcode()) {
		case WyilFile.TYPE_int:
			return fromInt(e);
		}
		return e;
	}

	/**
	 * Unbox a given expression into a <code>WVal</code> as necessary. This is
	 * required, for example, when primitive values are moving into general
	 * dictionaries.
	 *
	 * @param type
	 * @param e
	 * @return
	 */
	private static Expr unbox(WyilFile.Type type, Expr e) {
		switch (type.getOpcode()) {
		case WyilFile.TYPE_int:
			return toInt(e);
		}
		return e;
	}

	/**
	 * Ensure that a given expression is in its primitive form. In some situations,
	 * we can simplify the expression by removing a previous boxing call.
	 *
	 * @param e
	 * @return
	 */
	private static Expr toInt(Expr e) {
		if(e instanceof Expr.Invoke) {
			Expr.Invoke i = (Expr.Invoke) e;
			if(i.getName().equals("fromInt")) {
				return i.getArguments().get(0);
			}
		}
		return new Expr.Invoke("toInt", e);
	}

	/**
	 * Ensure that a given expression is in its boxed form. In some situations,
	 * we can simplify the expression by removing a previous unboxing call.
	 *
	 * @param e
	 * @return
	 */
	private static Expr fromInt(Expr e) {
		if(e instanceof Expr.Invoke) {
			Expr.Invoke i = (Expr.Invoke) e;
			if(i.getName().equals("toInt")) {
				return i.getArguments().get(0);
			}
		}
		return new Expr.Invoke("fromInt", e);
	}

	/**
	 * Determine the set of all field names used within a given WyilFile. This is
	 * necessary as we must enumerate field names in order to use them. To achieve
	 * this, we recurse the AST looking for all record types.
	 *
	 * @param wf
	 * @return
	 */
	private Set<String> determineFieldNames(WyilFile wf) {
		Set<String> names = new HashSet<>();
		//
		for (Unit unit : wf.getModule().getUnits()) {
			//
			new AbstractVisitor(meter) {
				@Override
				public void visitTypeRecord(WyilFile.Type.Record t) {
					// Continue visiting children
					super.visitTypeRecord(t);
					// Add all field names
					for (WyilFile.Type.Field f : t.getFields()) {
						names.add(f.getName().get());
					}
				}
			}.visitUnit(unit);

		}
		return names;
	}

	/**
	 * Determine the appropriate mangled string for a given named declaration. This
	 * is critical to ensuring that overloaded declarations do not clash.
	 *
	 * @param decl
	 * @return
	 */
	private String toMangledName(Named<?> decl) {
		// Determine whether this is an exported symbol or not
		boolean exported = decl.getModifiers().match(WyilFile.Modifier.Export.class) != null;
		// Construct base name
		String name = decl.getQualifiedName().toString().replace("::", "$");
		// Add type mangles for non-exported symbols
		if(!exported && decl instanceof Method) {
			// FIXME: this could be simplified if TypeMangler was updated to support void.
			Method method = (Method) decl;
			WyilFile.Type parameters = method.getType().getParameter();
			WyilFile.Type returns = method.getType().getReturn();
			name += getMangle(parameters);
			name += getMangle(returns);
		} else if(!exported && decl instanceof Callable) {
			// FIXME: this could be simplified if TypeMangler was updated to support void.
			Callable callable = (Callable) decl;
			WyilFile.Type parameters = callable.getType().getParameter();
			WyilFile.Type returns = callable.getType().getReturn();
			name += getMangle(parameters);
			name += getMangle(returns);
		} else if(decl instanceof Type) {
			name += "$type";
		} else if(decl instanceof StaticVariable) {
			name += "$static";
		}
		return name;
	}

	/**
	 * Determine the mangle for a given set of types.
	 *
	 * @param type
	 * @return
	 */
	private String getMangle(WyilFile.Type type) {
		if (type.shape() == 0) {
			return "$V";
		} else {
			return "$" + mangler.getMangle(type);
		}
	}

	private String getMangle(WyilFile.Type... types) {
		if (types.length == 0) {
			return "$V";
		} else {
			return "$" + mangler.getMangle(types);
		}
	}
	public static final BoogieFile.Type WVal = new BoogieFile.Type.Synonym("WVal");
	public static final BoogieFile.Type WField = new BoogieFile.Type.Synonym("WField");
	public static final BoogieFile.Type WType = new BoogieFile.Type.Synonym("WType");
	public static final BoogieFile.Type IntWVals = new BoogieFile.Type.Dictionary(BoogieFile.Type.Int, WVal);
	public static final BoogieFile.Type WFieldWVals = new BoogieFile.Type.Dictionary(WField, WVal);

	public static Expr.Quantifier forall(String name, BoogieFile.Type type, Expr body) {
		return new Expr.Quantifier(true, body, new Decl.Parameter(name, type));
	}

	public static Expr.Quantifier forall(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2, Expr body) {
		return new Expr.Quantifier(true, body, new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2));
	}

	public static Decl.Function fun(String name, BoogieFile.Type parameter, BoogieFile.Type returns) {
		return new Decl.Function(name, parameter, returns);
	}

	public static Expr or(Expr... operands) {
		if(operands.length == 0) {
			return new Expr.Constant(false);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.OR, operands);
		}
	}

	public static Expr and(List<Expr> operands) {
		if(operands.size() == 0) {
			return new Expr.Constant(true);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, operands);
		}
	}

	public static Expr and(Expr... operands) {
		if(operands.length == 0) {
			return new Expr.Constant(true);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, operands);
		}
	}

	public static Expr.BinaryOperator eq(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.EQ, lhs, rhs);
	}

	public static Expr.BinaryOperator neq(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.NEQ, lhs, rhs);
	}

	public static Expr.BinaryOperator lteq(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LTEQ, lhs, rhs);
	}

	public static Expr.BinaryOperator lt(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LT, lhs, rhs);
	}

	public static Expr.DictionaryAccess get(Expr src, Expr index) {
		return new Expr.DictionaryAccess(src, index);
	}

	public static Expr.VariableAccess var(String name) {
		return new Expr.VariableAccess(name);
	}

	public static Expr.Constant constant(int i) {
		return new Expr.Constant(i);
	}

	public static Expr.Invoke invoke(String name, Expr parameter) {
		return new Expr.Invoke(name, parameter);
	}
}
