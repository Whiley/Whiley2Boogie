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

import static wyboogie.core.BoogieFile.*;
import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;
import wyboogie.core.BoogieFile.LVal;
import wyboogie.util.AbstractTranslator;
import wybs.lang.Build.Meter;
import wyfs.util.ArrayUtils;
import wyfs.util.Pair;
import wyil.lang.WyilFile;
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
		// Add general axioms
		boogieFile.getDeclarations().addAll(constructAxioms(wf));
		// Translate local units
		for (WyilFile.Decl.Unit unit : wf.getModule().getUnits()) {
			for (WyilFile.Decl decl : unit.getDeclarations()) {
				BoogieFile.Decl d = visitDeclaration(decl);
				if (d != null) {
					boogieFile.getDeclarations().add(d);
				}
			}
		}
	}

	@Override
	public Decl constructImport(WyilFile.Decl.Import d) {
		return new Decl.Sequence();
	}

	@Override
	public Decl constructType(WyilFile.Decl.Type d, List<Expr> invariant) {
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
	public Decl constructStaticVariable(WyilFile.Decl.StaticVariable d, Expr initialiser) {
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
	public Decl constructProperty(WyilFile.Decl.Property d, List<Expr> clauses) {
		// Apply name mangling
		String name = toMangledName(d);
		//
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		Expr body = new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, clauses);
		return new Decl.Function(name, parameters, BoogieFile.Type.Bool, body);
	}

	@Override
	public Decl constructFunction(WyilFile.Decl.Function d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		return constructFunctionOrMethod(d,precondition,postcondition,body);
	}

	@Override
	public Decl constructMethod(WyilFile.Decl.Method d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		return constructFunctionOrMethod(d,precondition,postcondition,body);
	}

	public Decl constructFunctionOrMethod(WyilFile.Decl.FunctionOrMethod d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		// Apply name mangling
		String name = toMangledName(d);
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		List<Decl.Parameter> returns = constructParameters(d.getReturns());
		ArrayList<Decl.Parameter> parametersAndReturns = new ArrayList<>();
		parametersAndReturns.addAll(parameters);
		parametersAndReturns.addAll(returns);
		// FIXME: obviously broken for multiple returns!
		BoogieFile.Type returnType = returns.isEmpty() ? WVal : returns.get(0).getType();
		// Construct function representation precondition
		Decl.Function pre = new Decl.Function(name + "#pre", parameters, BoogieFile.Type.Bool, AND(precondition));
		// Construct function representation postcondition
		Decl.Function post = new Decl.Function(name + "#post", parametersAndReturns, BoogieFile.Type.Bool, AND(postcondition));
		// Construct prototype which can be called from expressions.
		Decl.Function prototype = new Decl.Function(name, parameters, returnType);
		// Construct procedure prototype
		Decl proc = new Decl.Procedure(name + "#impl", parameters, returns, precondition, postcondition);
		// Determine local variables
		List<Decl.Variable> locals = constructLocals(d.getBody());
		// Construct implementation (if applicable)
		List<Decl.Parameter> shadows = constructShadowParameters(d.getParameters(),parameters);
		//
		body = addShadowAssignments(locals, body, parameters, shadows);
		// Construct implementation which can be checked against its specification.
		Decl impl = new Decl.Implementation(name + "#impl", shadows, returns, locals, body);
		if(returns.size() > 0) {
			// Construct axiom linking post-condition with prototype.
			Decl axiom = constructPostconditionAxiom(name, parameters, returns);
			return new Decl.Sequence(prototype, pre, post, proc, impl, axiom);
		} else {
			// Done
			return new Decl.Sequence(prototype, pre, post, proc, impl);
		}
	}

	/**
	 * Convert a sequence of Wyil parameter declarations into a sequence of Boogie
	 * parameter declarations. This requires converting the Wyil type to its
	 * corresponding Boogie type.
	 *
	 * @param params
	 * @return
	 */
	public List<Decl.Parameter> constructParameters(WyilFile.Tuple<WyilFile.Decl.Variable> params) {
		ArrayList<Decl.Parameter> ps = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			ps.add(constructParameter(params.get(i)));
		}
		return ps;
	}

	/**
	 * Construct the list of parameters to use in the implementation. This differs
	 * from that used in the protype / procedure declaration because it must account
	 * for <i>shadows</i>. These arise because Whiley allows parameters to be
	 * mutated, where as Boogie does not. To work around this, we have shadow
	 * parameters (i.e. with different names) which are then assigned to local
	 * variables (which can be modified).
	 *
	 * @param params
	 * @param parameters
	 * @return
	 */
	public List<Decl.Parameter> constructShadowParameters(WyilFile.Tuple<WyilFile.Decl.Variable> params,
			List<Decl.Parameter> parameters) {
		ArrayList<Decl.Parameter> ps = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			WyilFile.Decl.Variable ith = params.get(i);
			if (isFinal(ith)) {
				ps.add(parameters.get(i));
			} else {
				BoogieFile.Type type = constructType(ith.getType());
				ps.add(new Decl.Parameter(ith.getName().get() + "#", type));
			}
		}
		return ps;
	}

	/**
	 * Check whether a given variable is marked as final or not. This is useful to
	 * avoid shadow variables in some case.
	 *
	 * @param var
	 * @return
	 */
	public boolean isFinal(WyilFile.Decl.Variable var) {
		return var.getModifiers().match(WyilFile.Modifier.Final.class) != null;
	}

	/**
	 * Convert a Wyil parameter declaration into a corresponding Boogie one which,
	 * in turn, requires converting their types.
	 *
	 * @param ps
	 * @return
	 */
	public Decl.Parameter constructParameter(WyilFile.Decl.Variable ps) {
		BoogieFile.Type type = constructType(ps.getType());
		return new Decl.Parameter(ps.getName().get(), type);
	}

	/**
	 * Add the list of assignments for the shadow parameters to a given function or
	 * method body. Basically, for every shadow parameter, there is one assignment
	 * to its corresponding local variable.
	 *
	 * @param locals
	 * @param body
	 * @param parameters
	 * @param implementation
	 * @return
	 */
	public Stmt addShadowAssignments(List<Decl.Variable> locals, Stmt body, List<Decl.Parameter> parameters,
			List<Decl.Parameter> implementation) {
		// Handle parameter shadows
		ArrayList<Stmt> stmts = new ArrayList<>();
		for (int i = 0; i != implementation.size(); ++i) {
			Decl.Parameter ith = implementation.get(i);
			Decl.Parameter pth = parameters.get(i);
			if (ith != pth) {
				locals.add(new Decl.Variable(pth.getName(), pth.getType()));
				stmts.add(new Stmt.Assignment(new Expr.VariableAccess(pth.getName()),
						new Expr.VariableAccess(ith.getName())));
			}
		}
		stmts.add(body);
		return new Stmt.Sequence(stmts);
	}

	/**
	 * Determine the set of local variables declared within this block. This is
	 * necessary as Boogie, unlike Whiley, requires that all local variables are
	 * declared up front (like C does).
	 *
	 * @param blk
	 * @return
	 */
	public List<Decl.Variable> constructLocals(WyilFile.Stmt.Block blk) {
		ArrayList<Decl.Variable> decls = new ArrayList<>();
		// Handle local variables
		new AbstractVisitor(meter) {
			@Override
			public void visitInitialiser(WyilFile.Stmt.Initialiser stmt) {
				WyilFile.Tuple<WyilFile.Decl.Variable> vars = stmt.getVariables();
				if (vars.size() != 1) {
					throw new UnsupportedOperationException("Multiple initialisers not supported (yet)");
				}
				String name = vars.get(0).getName().toString();
				BoogieFile.Type type = constructType(vars.get(0).getType());
				decls.add(new Decl.Variable(name, type));
			}

			@Override
			public void visitDeclaration(WyilFile.Decl d) {
				// Prevent unexpected traverals of declarations.
			}

			@Override
			public void visitType(WyilFile.Type t) {
				// Prevent unexpected traverals of types
			}
		}.visitBlock(blk);
		// Done
		return decls;
	}

	/**
	 * Construct the "postcondition axiom" which relates a given function prototype
	 * to its postcondition. Without this, when an invocation is made to that
	 * prototype, Boogie will not be aware of what the postcondition implies.
	 *
	 * @param prototype
	 * @param parameters
	 * @return
	 */
	public Decl.Axiom constructPostconditionAxiom(String name, List<Decl.Parameter> parameters,
			List<Decl.Parameter> returns) {
		//
		if (returns.size() != 1) {
			throw new IllegalArgumentException("multiple returns not supported");
		} else if (parameters.size() == 0) {
			// Easy case, since we don't even need a quantifier.
			return new Decl.Axiom(CALL(name + "#post", CALL(name)));
		} else {
			// A universal quantifier is required!
			Expr[] pargs = new Expr[parameters.size()];
			for (int i = 0; i != pargs.length; ++i) {
				pargs[i] = VAR(parameters.get(i).getName());
			}
			// Construct the axiom
			return new Decl.Axiom(FORALL(parameters, IMPLIES(CALL(name + "#pre", pargs),
					CALL(name + "#post", ArrayUtils.append(pargs, CALL(name, pargs))))));
		}
	}

	@Override
	public Expr constructLambda(WyilFile.Decl.Lambda decl, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructAssert(WyilFile.Stmt.Assert stmt, Expr condition, List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.Assert(condition));
	}

	@Override
	public Stmt constructAssign(WyilFile.Stmt.Assign stmt, List<Expr> lvals, List<Expr> rvals, List<Expr> preconditions) {
		if (lvals.size() != 1 || rvals.size() != 1) {
			throw new UnsupportedOperationException("Multiple assignments not supported (yet)");
		}
		LVal lhs = (LVal) lvals.get(0);
		Expr rhs = cast(stmt.getLeftHandSide().get(0).getType(), stmt.getRightHandSide().get(0).getType(),
				rvals.get(0));
		return applyPreconditions(preconditions, new Stmt.Assignment(lhs, rhs));
	}

	@Override
	public Stmt constructAssume(WyilFile.Stmt.Assume stmt, Expr condition, List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.Assume(condition));
	}

	@Override
	public Stmt constructBlock(WyilFile.Stmt.Block stmt, List<Stmt> stmts) {
		return new Stmt.Sequence(stmts);
	}

	@Override
	public Stmt constructBreak(WyilFile.Stmt.Break stmt) {
		WyilFile.Stmt loop = getEnclosingLoop(stmt);
		String label = "BREAK_" + loop.getIndex();
		return new Stmt.Goto(label);
	}

	@Override
	public Stmt constructContinue(WyilFile.Stmt.Continue stmt) {
		WyilFile.Stmt loop = getEnclosingLoop(stmt);
		String label = "CONTINUE_" + loop.getIndex();
		return new Stmt.Goto(label);
	}

	@Override
	public Stmt constructDebug(WyilFile.Stmt.Debug stmt, Expr operand, List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.Assert(CONST(true)));
	}

	@Override
	public Stmt constructDoWhile(WyilFile.Stmt.DoWhile stmt, Stmt body, Expr condition, List<Expr> invariant,
			List<Expr> preconditions) {
		Stmt loop = new Stmt.While(condition, invariant, body);
		// FIXME: handle preconditions
		return new Stmt.Sequence(body, loop);
	}

	@Override
	public Stmt constructFail(WyilFile.Stmt.Fail stmt) {
		return new Stmt.Assert(CONST(false));
	}

	@Override
	public Stmt constructFor(WyilFile.Stmt.For stmt, Pair<Expr, Expr> range, List<Expr> invariant, Stmt body,
			List<Expr> preconditions) {
		// Determine name of loop variable
		String name = stmt.getVariable().getName().get();
		Expr.VariableAccess var = new Expr.VariableAccess(name);
		// Extract loop contents so it can be appended later
		ArrayList<Stmt> loopBody = new ArrayList<>();
		loopBody.add(body);
		// Initialise index variable with first value from range
		Stmt.Assignment init = new Stmt.Assignment(var, range.first());
		Expr condition = LT(var, range.second());
		// Add variable increment for completeness
		loopBody.add(new Stmt.Assignment(var, ADD(var, CONST(1))));
		// Construct the loop
		Stmt.While loop = new Stmt.While(condition, invariant, new Stmt.Sequence(loopBody));
		// FIXME: handle preconditions
		// Done.
		return new Stmt.Sequence(init, loop);
	}

	@Override
	public Stmt constructIfElse(WyilFile.Stmt.IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch,
			List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.IfElse(condition, trueBranch, falseBranch));
	}

	@Override
	public Stmt constructInitialiser(WyilFile.Stmt.Initialiser stmt, Expr initialiser, List<Expr> preconditions) {
		WyilFile.Tuple<WyilFile.Decl.Variable> vars = stmt.getVariables();
		if (vars.size() != 1) {
			throw new UnsupportedOperationException("Multiple initialisers not supported (yet)");
		}
		String name = vars.get(0).getName().toString();
		//
		if (initialiser == null) {
			return new Stmt.Sequence();
		} else {
			Stmt.Assignment init = new Stmt.Assignment(new Expr.VariableAccess(name), initialiser);
			// FIXME: need post condition!
			return applyPreconditions(preconditions, init);
		}
	}

	@Override
	public Stmt constructNamedBlock(WyilFile.Stmt.NamedBlock stmt, List<Stmt> stmts) {
		throw new IllegalArgumentException("GOT HERE");
	}

	@Override
	public Stmt constructReturn(WyilFile.Stmt.Return stmt, Expr ret, List<Expr> preconditions) {
		if (ret != null) {
			// Identify enclosing function or method to figure out names of return
			// variables.
			WyilFile.Decl.Callable enclosing = stmt.getAncestor(WyilFile.Decl.FunctionOrMethod.class);
			WyilFile.Tuple<WyilFile.Decl.Variable> returns = enclosing.getReturns();
			if (returns.size() != 1) {
				// TODO: implement this!
				throw new IllegalArgumentException("Missing support for multiple returns");
			} else {
				String rv = returns.get(0).getName().get();
				Stmt s1 = new Stmt.Assignment(VAR(rv), ret);
				Stmt s2 = new Stmt.Return();
				return applyPreconditions(preconditions, new Stmt.Sequence(s1, s2));
			}
		} else {
			return new Stmt.Return();
		}
	}

	@Override
	public Stmt constructSkip(WyilFile.Stmt.Skip stmt) {
		return new Stmt.Assert(new Expr.Constant(true));
	}

	@Override
	public Stmt constructSwitch(WyilFile.Stmt.Switch stmt, Expr condition, List<Pair<List<Expr>, Stmt>> cases,
			List<Expr> preconditions) {
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
				labs.add(EQ(condition, ith_first.get(j)));
			}
			stmts.add(new Stmt.Label(labels[i]));
			stmts.add(new Stmt.Assume(OR(labs)));
			stmts.add(ith.second());
			stmts.add(new Stmt.Goto(breakLabel));
		}
		//
		return applyPreconditions(preconditions, new Stmt.Sequence(stmts));
	}

	@Override
	public Stmt constructWhile(WyilFile.Stmt.While stmt, Expr condition, List<Expr> invariant, Stmt body, List<Expr> preconditions) {
		boolean needContinueLabel = containsContinueOrBreak(stmt, false);
		boolean needBreakLabel = containsContinueOrBreak(stmt, true);
		Stmt.While s = new Stmt.While(condition, invariant, body);
		// FIXME: handle preconditions
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

	public Stmt applyPreconditions(List<Expr> preconditions, Stmt stmt) {
		if (preconditions.isEmpty()) {
			return stmt;
		} else {
			List<Stmt> assertions = constructAssertions(preconditions);
			return new Stmt.Sequence(assertions, stmt);
		}
	}

	public List<Stmt> constructAssertions(List<Expr> exprs) {
		ArrayList<Stmt> assertions = new ArrayList<>();
		for (int i = 0; i != exprs.size(); ++i) {
			assertions.add(new Stmt.Assert(exprs.get(i)));
		}
		return assertions;
	}

	@Override
	public Expr constructArrayAccessLVal(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
		return new Expr.DictionaryAccess(source, index);
	}

	@Override
	public Expr constructDereferenceLVal(WyilFile.Expr.Dereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructFieldDereferenceLVal(WyilFile.Expr.FieldDereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructRecordAccessLVal(WyilFile.Expr.RecordAccess expr, Expr source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructTupleInitialiserLVal(WyilFile.Expr.TupleInitialiser expr, List<Expr> source) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructVariableAccessLVal(WyilFile.Expr.VariableAccess expr) {
		return constructVariableAccess(expr);
	}

	@Override
	public Expr constructArrayAccess(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
		return unbox(expr.getType(), new Expr.DictionaryAccess(source, index));
	}

	@Override
	public Expr constructArrayLength(WyilFile.Expr.ArrayLength expr, Expr source) {
		return CALL("WArray#Length", source);
	}

	@Override
	public Expr constructArrayGenerator(WyilFile.Expr.ArrayGenerator expr, Expr value, Expr length) {
		WyilFile.Type vt = expr.getFirstOperand().getType();
		WyilFile.Type lt = expr.getSecondOperand().getType();
		return CALL("WArray#Generator", box(vt, value), cast(WyilFile.Type.Int, lt, length));
	}

	@Override
	public Expr constructArrayInitialiser(WyilFile.Expr.ArrayInitialiser expr, List<Expr> values) {
		WyilFile.Type elementType = expr.getType().as(WyilFile.Type.Array.class).getElement();
		Expr arr = CALL("WArray#Empty", CONST(values.size()));
		//
		for (int i = 0; i != values.size(); ++i) {
			WyilFile.Type type = expr.getOperands().get(i).getType();
			Expr ith = box(type, values.get(i));
			arr = new Expr.DictionaryUpdate(arr, new Expr.Constant(i), ith);
		}
		//
		return arr;
	}

	@Override
	public Expr constructBitwiseComplement(WyilFile.Expr.BitwiseComplement expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseAnd(WyilFile.Expr.BitwiseAnd expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseOr(WyilFile.Expr.BitwiseOr expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseXor(WyilFile.Expr.BitwiseXor expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseShiftLeft(WyilFile.Expr.BitwiseShiftLeft expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructBitwiseShiftRight(WyilFile.Expr.BitwiseShiftRight expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructCast(WyilFile.Expr.Cast expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructConstant(WyilFile.Expr.Constant expr) {
		WyilFile.Value v = expr.getValue();
		switch (v.getOpcode()) {
		case WyilFile.ITEM_null: {
			return Expr.Constant.NULL;
		}
		case WyilFile.ITEM_bool: {
			boolean b = ((WyilFile.Value.Bool) v).get();
			return b ? Expr.Constant.TRUE : Expr.Constant.FALSE;
		}
		case WyilFile.ITEM_int: {
			BigInteger i = ((WyilFile.Value.Int) v).get();
			return CONST(i);
		}
		case WyilFile.ITEM_utf8: {
			byte[] bytes = ((WyilFile.Value.UTF8) v).get();
			Expr arr = CALL("WArray#Empty", CONST(bytes.length));
			//
			for (int i = 0; i != bytes.length; ++i) {
				Expr ith = fromInt(new Expr.Constant(bytes[i]));
				arr = new Expr.DictionaryUpdate(arr, new Expr.Constant(i), ith);
			}
			return arr;
		}
		default:
			throw new IllegalArgumentException("unknown constant encountered (" + expr.getClass().getName() + ")");
		}
	}

	@Override
	public Expr constructDereference(WyilFile.Expr.Dereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructFieldDereference(WyilFile.Expr.FieldDereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructEqual(WyilFile.Expr.Equal expr, Expr lhs, Expr rhs) {
		// Box operands for simplicity
		lhs = box(expr.getFirstOperand().getType(), lhs);
		rhs = box(expr.getSecondOperand().getType(), rhs);
		// Done
		return EQ(lhs, rhs);
	}

	@Override
	public Expr constructIntegerLessThan(WyilFile.Expr.IntegerLessThan expr, Expr lhs, Expr rhs) {
		return LT(lhs, rhs);
	}

	@Override
	public Expr constructIntegerLessThanOrEqual(WyilFile.Expr.IntegerLessThanOrEqual expr, Expr lhs, Expr rhs) {
		return LTEQ(lhs, rhs);
	}

	@Override
	public Expr constructIntegerGreaterThan(WyilFile.Expr.IntegerGreaterThan expr, Expr lhs, Expr rhs) {
		return GT(lhs, rhs);
	}

	@Override
	public Expr constructIntegerGreaterThanOrEqual(WyilFile.Expr.IntegerGreaterThanOrEqual expr, Expr lhs, Expr rhs) {
		return GTEQ(lhs, rhs);
	}

	@Override
	public Expr constructIntegerNegation(WyilFile.Expr.IntegerNegation expr, Expr operand) {
		return NEG(operand);
	}

	@Override
	public Expr constructIntegerAddition(WyilFile.Expr.IntegerAddition expr, Expr lhs, Expr rhs) {
		return ADD(lhs, rhs);
	}

	@Override
	public Expr constructIntegerSubtraction(WyilFile.Expr.IntegerSubtraction expr, Expr lhs, Expr rhs) {
		return SUB(lhs, rhs);
	}

	@Override
	public Expr constructIntegerMultiplication(WyilFile.Expr.IntegerMultiplication expr, Expr lhs, Expr rhs) {
		return MUL(lhs, rhs);
	}

	@Override
	public Expr constructIntegerDivision(WyilFile.Expr.IntegerDivision expr, Expr lhs, Expr rhs) {
		return IDIV(lhs, rhs);
	}

	@Override
	public Expr constructIntegerRemainder(WyilFile.Expr.IntegerRemainder expr, Expr lhs, Expr rhs) {
		return REM(lhs, rhs);
	}

	@Override
	public Expr constructIs(WyilFile.Expr.Is expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalAnd(WyilFile.Expr.LogicalAnd expr, List<Expr> operands) {
		return AND(operands);
	}

	@Override
	public Expr constructLogicalImplication(WyilFile.Expr.LogicalImplication expr, Expr lhs, Expr rhs) {
		return IMPLIES(lhs, rhs);
	}

	@Override
	public Expr constructLogicalIff(WyilFile.Expr.LogicalIff expr, Expr lhs, Expr rhs) {
		return IFF(lhs, rhs);
	}

	@Override
	public Expr constructLogicalNot(WyilFile.Expr.LogicalNot expr, Expr operand) {
		return NOT(operand);
	}

	@Override
	public Expr constructLogicalOr(WyilFile.Expr.LogicalOr expr, List<Expr> operands) {
		return OR(operands);
	}

	@Override
	public Expr constructExistentialQuantifier(WyilFile.Expr.ExistentialQuantifier expr, List<Pair<Expr, Expr>> ranges, Expr body) {
		WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
		List<Decl.Parameter> ps = new ArrayList<>();
		List<Expr> clauses = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			Pair<Expr, Expr> ith = ranges.get(i);
			String name = params.get(i).getName().get();
			ps.add(new Decl.Parameter(name, BoogieFile.Type.Int));
			clauses.add(LTEQ(ith.first(), VAR(name)));
			clauses.add(LT(VAR(name), ith.second()));
		}
		clauses.add(body);
		return new Expr.Quantifier(false, AND(clauses), ps);
	}

	@Override
	public Expr constructUniversalQuantifier(WyilFile.Expr.UniversalQuantifier expr, List<Pair<Expr, Expr>> ranges, Expr body) {
		WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
		List<Decl.Parameter> ps = new ArrayList<>();
		List<Expr> clauses = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			Pair<Expr, Expr> ith = ranges.get(i);
			String name = params.get(i).getName().get();
			ps.add(new Decl.Parameter(name, BoogieFile.Type.Int));
			clauses.add(LTEQ(ith.first(), VAR(name)));
			clauses.add(LT(VAR(name), ith.second()));
		}
		return new Expr.Quantifier(true, IMPLIES(AND(clauses),body), ps);
	}

	@Override
	public Expr constructInvoke(WyilFile.Expr.Invoke expr, List<Expr> arguments) {
		// Apply name mangling
		String name = toMangledName(expr.getLink().getTarget());
		//
		return CALL(name, arguments);
	}

	@Override
	public Expr constructIndirectInvoke(WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> arguments) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLambdaAccess(WyilFile.Expr.LambdaAccess expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructNew(WyilFile.Expr.New expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructNotEqual(WyilFile.Expr.NotEqual expr, Expr lhs, Expr rhs) {
		// Box operands for simplicity
		lhs = box(expr.getFirstOperand().getType(), lhs);
		rhs = box(expr.getSecondOperand().getType(), rhs);
		// Done
		return NEQ(lhs, rhs);
	}

	@Override
	public Expr constructRecordAccess(WyilFile.Expr.RecordAccess expr, Expr source) {
		Expr field = VAR("$" + expr.getField().get());
		return unbox(expr.getType(), new Expr.DictionaryAccess(source, field));
	}

	@Override
	public Expr constructRecordInitialiser(WyilFile.Expr.RecordInitialiser expr, List<Expr> operands) {
		WyilFile.Tuple<WyilFile.Expr> values = expr.getOperands();
		WyilFile.Tuple<WyilFile.Identifier> fields = expr.getFields();
		//
		Expr rec = VAR("WRecord#Empty");
		//
		for (int i = 0; i != operands.size(); ++i) {
			Expr ith = box(values.get(i).getType(), operands.get(i));
			String field = "$" + fields.get(i).get();
			rec = new Expr.DictionaryUpdate(rec, VAR(field), ith);
		}
		//
		return rec;
	}

	@Override
	public Expr constructTupleInitialiser(WyilFile.Expr.TupleInitialiser expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructStaticVariableAccess(WyilFile.Expr.StaticVariableAccess expr) {
		// Apply name mangling
		String name = toMangledName(expr.getLink().getTarget());
		// Done
		return VAR(name);
	}

	@Override
	public Expr constructVariableAccess(WyilFile.Expr.VariableAccess expr) {
		return VAR(expr.getVariableDeclaration().getName().toString());
	}

	// =========================================================================================
	// Preconditions
	// =========================================================================================

	@Override
	public Expr constructArrayAccessPrecondition(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
		return AND(LTEQ(CONST(0), index), LT(index, CALL("WArray#Length", source)));
	}

	@Override
	public Expr constructIntegerDivisionPrecondition(WyilFile.Expr.IntegerDivision expr, Expr lhs, Expr rhs) {
		return NEQ(rhs, CONST(0));
	}

	@Override
	public Expr constructInvokePrecondition(WyilFile.Expr.Invoke expr, List<Expr> args) {
		WyilFile.Decl.Callable c = expr.getLink().getTarget();
		String name = toMangledName(c);
		//
		if (c instanceof WyilFile.Decl.FunctionOrMethod) {
			return CALL(name + "#pre", args);
		} else {
			return null;
		}
	}

	// =========================================================================================
	// Types
	// =========================================================================================

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
		case WyilFile.TYPE_union:
			return constructUnionType((WyilFile.Type.Union) type);
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

	public BoogieFile.Type constructUnionType(WyilFile.Type.Union type) {
		return WVal;
	}

	public BoogieFile.Type constructNominalType(WyilFile.Type.Nominal type) {
		// Apply name mangling
		String name = toMangledName(type.getLink().getTarget());
		// Done!
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
		// Add null constant
		axioms.add(new Decl.Constant(true, "null", WVal));
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
		Decl.Function fromInt = FUN("fromInt", BoogieFile.Type.Int, WVal);
		Decl.Function toInt = FUN("toInt", WVal, BoogieFile.Type.Int);
		// Establish connection between toInt and fromInt
		Decl.Axiom axiom1 = new Decl.Axiom(
				FORALL("i", BoogieFile.Type.Int, EQ(CALL("toInt", CALL("fromInt", VAR("i"))), VAR("i"))));
		return Arrays.asList(header, fromInt, toInt, axiom1);
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
		decls.add(FUN("WArray#Length", IntWVals, BoogieFile.Type.Int));
		// Enforce array length is non-negative
		decls.add(new Decl.Axiom(FORALL("a", IntWVals, LTEQ(CONST(0), CALL("WArray#Length", VAR("a"))))));
		// Empty arrays
		decls.add(FUN("WArray#Empty", BoogieFile.Type.Int, IntWVals));
		decls.add(FUN("WArray#Generator", WVal, BoogieFile.Type.Int, IntWVals));
		// Ensure that all elements outside array length are void
		decls.add(new Decl.Axiom(FORALL("l", BoogieFile.Type.Int, "i", BoogieFile.Type.Int,
				OR(AND(LTEQ(CONST(0), VAR("i")), LT(VAR("i"), VAR("l"))),
						EQ(GET(CALL("WArray#Empty", VAR("l")), VAR("i")), VAR("WVoid"))))));
		// Relate empty array with its length
		decls.add(new Decl.Axiom(FORALL("a", IntWVals, "l", BoogieFile.Type.Int,
				OR(NEQ(CALL("WArray#Empty", VAR("l")), VAR("a")), EQ(CALL("WArray#Length", VAR("a")), VAR("l"))))));
		// Ensure that all elements inside generator length are void
		decls.add(new Decl.Axiom(FORALL("v", WVal, "l", BoogieFile.Type.Int, "i", BoogieFile.Type.Int,
				OR(LT(VAR("i"),CONST(0)), LTEQ(VAR("l"), VAR("i")),
						EQ(GET(CALL("WArray#Generator", VAR("v"), VAR("l")), VAR("i")), VAR("v"))))));
		// Ensure that all elements outside generator length are void
		decls.add(new Decl.Axiom(FORALL("v", WVal, "l", BoogieFile.Type.Int, "i", BoogieFile.Type.Int,
				OR(AND(LTEQ(CONST(0), VAR("i")), LT(VAR("i"), VAR("l"))),
						EQ(GET(CALL("WArray#Generator", VAR("v"), VAR("l")), VAR("i")), VAR("WVoid"))))));
			// Relate array generator with its length
		decls.add(new Decl.Axiom(FORALL("a", IntWVals, "v", WVal, "l", BoogieFile.Type.Int,
				OR(NEQ(CALL("WArray#Generator", VAR("v"), VAR("l")), VAR("a")), EQ(CALL("WArray#Length", VAR("a")), VAR("l"))))));
		// Relate updated array with its length
		decls.add(new Decl.Axiom(FORALL("a", IntWVals, "i", BoogieFile.Type.Int, "v", WVal,
				EQ(CALL("WArray#Length", VAR("a")), CALL("WArray#Length", PUT(VAR("a"), VAR("i"), VAR("v")))))));
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
		for (String field : determineFieldNames(wf)) {
			String name = "$" + field;
			decls.add(new Decl.Constant(true, name, WField));
		}
		//
		decls.add(new Decl.LineComment("Records"));
		// Defines the empty record (i.e. the base from which all other records are
		// constructed).
		decls.add(new Decl.Constant(true, "WRecord#Empty", WFieldWVals));
		decls.add(new Decl.Axiom(FORALL("f", WField, EQ(GET(VAR("WRecord#Empty"), VAR("f")), VAR("WVoid")))));
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

	private static Expr cast(WyilFile.Type to, WyilFile.Type from, Expr e) {
		switch (to.getOpcode()) {
		case WyilFile.TYPE_union:
			return box(from,e);
		}
		return e;
	}

	/**
	 * Box a given expression into a <code>WVal</code> as necessary. This is used in
	 * situations where a given expression must have type <code>WVal</code> but, at
	 * the given point, may be still unboxed.
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
		if (e instanceof Expr.Invoke) {
			Expr.Invoke i = (Expr.Invoke) e;
			if (i.getName().equals("fromInt")) {
				return i.getArguments().get(0);
			}
		}
		return new Expr.Invoke("toInt", e);
	}

	/**
	 * Ensure that a given expression is in its boxed form. In some situations, we
	 * can simplify the expression by removing a previous unboxing call.
	 *
	 * @param e
	 * @return
	 */
	private static Expr fromInt(Expr e) {
		if (e instanceof Expr.Invoke) {
			Expr.Invoke i = (Expr.Invoke) e;
			if (i.getName().equals("toInt")) {
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
		for (WyilFile.Decl.Unit unit : wf.getModule().getUnits()) {
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
	private String toMangledName(WyilFile.Decl.Named<?> decl) {
		// Determine whether this is an exported symbol or not
		boolean exported = decl.getModifiers().match(WyilFile.Modifier.Export.class) != null;
		// Construct base name
		String name = decl.getQualifiedName().toString().replace("::", "$");
		// Add type mangles for non-exported symbols
		if (!exported && decl instanceof WyilFile.Decl.Method) {
			// FIXME: this could be simplified if TypeMangler was updated to support void.
			WyilFile.Decl.Method method = (WyilFile.Decl.Method) decl;
			WyilFile.Type parameters = method.getType().getParameter();
			WyilFile.Type returns = method.getType().getReturn();
			name += getMangle(parameters);
			name += getMangle(returns);
		} else if (!exported && decl instanceof WyilFile.Decl.Callable) {
			// FIXME: this could be simplified if TypeMangler was updated to support void.
			WyilFile.Decl.Callable callable = (WyilFile.Decl.Callable) decl;
			WyilFile.Type parameters = callable.getType().getParameter();
			WyilFile.Type returns = callable.getType().getReturn();
			name += getMangle(parameters);
			name += getMangle(returns);
		} else if (decl instanceof WyilFile.Decl.Type) {
			name += "$type";
		} else if (decl instanceof WyilFile.Decl.StaticVariable) {
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
	public static final BoogieFile.Type WVoid = new BoogieFile.Type.Synonym("WVoid");
	public static final BoogieFile.Type WField = new BoogieFile.Type.Synonym("WField");
	public static final BoogieFile.Type WType = new BoogieFile.Type.Synonym("WType");
	public static final BoogieFile.Type IntWVals = new BoogieFile.Type.Dictionary(BoogieFile.Type.Int, WVal);
	public static final BoogieFile.Type WFieldWVals = new BoogieFile.Type.Dictionary(WField, WVal);

}
