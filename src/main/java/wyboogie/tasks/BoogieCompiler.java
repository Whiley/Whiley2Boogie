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
import wyboogie.core.BoogieFile.Expr.DictionaryUpdate;
import wyboogie.core.BoogieFile.LVal;
import wyboogie.util.AbstractTranslator;
import wybs.lang.Build.Meter;
import wybs.util.AbstractCompilationUnit.Tuple;
import wyfs.util.Pair;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Type.Array;
import wyil.util.AbstractVisitor;
import wyil.util.IncrementalSubtypingEnvironment;
import wyil.util.Subtyping;
import wyil.util.TypeMangler;
import wyil.util.WyilUtils;

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
		Type type = constructType(var.getType());
		// Apply name mangling
		String name = toMangledName(d);
		Decl t = new Decl.TypeSynonym(name, type);
		//
		Decl.Parameter p = new Decl.Parameter(var.getName().get(), type);
		Expr inv = AND(invariant);
		Decl a = FUNCTION(name + "#is", p, Type.Bool, inv);
		return new Decl.Sequence(t, a);
	}

	@Override
	public Decl constructStaticVariable(WyilFile.Decl.StaticVariable d, Expr initialiser) {
		Type type = constructType(d.getType());
		// Apply name mangling
		String name = toMangledName(d);
		// Final static variables declared as constants with corresponding axiom
		Decl d1 = new Decl.Constant(name, type);
		if (initialiser == null) {
			return d1;
		} else {
			Decl d2 = new Decl.Axiom(
					new Expr.BinaryOperator(Expr.BinaryOperator.Kind.EQ, new Expr.VariableAccess(name), initialiser));
			return new Decl.Sequence(d1, d2);
		}
	}

	@Override
	public Decl constructProperty(WyilFile.Decl.Property d, List<Expr> clauses) {
		// Apply name mangling
		String name = toMangledName(d);
		//
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		Expr body = new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, clauses);
		return FUNCTION(name, parameters, Type.Bool, body);
	}

	@Override
	public Decl constructFunction(WyilFile.Decl.Function d, List<Expr> precondition, List<Expr> postcondition,
			Stmt body) {
		return constructFunctionOrMethod(d, precondition, postcondition, body);
	}

	@Override
	public Decl constructMethod(WyilFile.Decl.Method d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
		return constructFunctionOrMethod(d, precondition, postcondition, body);
	}

	public Decl constructFunctionOrMethod(WyilFile.Decl.FunctionOrMethod d, List<Expr> precondition,
			List<Expr> postcondition, Stmt body) {
		ArrayList<Decl> decls = new ArrayList<>();
		// Apply name mangling
		String name = toMangledName(d);
		List<Decl.Parameter> parameters = constructParameters(d.getParameters());
		List<Decl.Parameter> protoParameters = new ArrayList<>(parameters);
		List<Decl.Parameter> returns = constructParameters(d.getReturns());
		// Construct parameters and arguments for specification helpers
		ArrayList<Decl.Parameter> specParametersAndReturns = new ArrayList<>();
		// Add heap argument (as necessary)
		if (d instanceof WyilFile.Decl.Method) {
			// To make this work, we override the existing heap variable name.
			protoParameters.add(0, new Decl.Variable("Heap#", REFMAP));
		}
		specParametersAndReturns.addAll(protoParameters);
		// Construct function representation precondition
		decls.add(FUNCTION(name + "#pre", specParametersAndReturns, Type.Bool, AND(precondition)));
		specParametersAndReturns.addAll(returns);
		// Construct function representation postcondition
		decls.add(FUNCTION(name + "#post", specParametersAndReturns, Type.Bool, AND(postcondition)));
		// Construct prototype which can be called from expressions.
		if (returns.isEmpty()) {
			decls.add(FUNCTION(name, parameters, VALUE));
		} else if (returns.size() == 1) {
			Type returnType = returns.get(0).getType();
			decls.add(FUNCTION(name, protoParameters, returnType));
		} else {
			// Multiple returns require special handling
			for (int i = 0; i != returns.size(); ++i) {
				Type returnType = returns.get(i).getType();
				decls.add(FUNCTION(name + "#" + i, protoParameters, returnType));
			}
		}
		// Construct procedure prototype
		decls.add(new Decl.Procedure(name + "#impl", parameters, returns, precondition, postcondition));
		// Determine local variables
		List<Decl.Variable> locals = constructLocals(d.getBody());
		// Construct implementation (if applicable)
		List<Decl.Parameter> shadows = constructShadowParameters(d.getParameters(), parameters);
		//
		body = addShadowAssignments(locals, body, parameters, shadows);
		// Construct implementation which can be checked against its specification.
		decls.add(new Decl.Implementation(name + "#impl", shadows, returns, locals, body));
		if (returns.size() > 0) {
			// Construct axiom linking post-condition with prototype.
			decls.add(constructPostconditionAxiom(d, name, parameters, returns));
		}
		// Done
		return new Decl.Sequence(decls);
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
				Type type = constructType(ith.getType());
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
		Type type = constructType(ps.getType());
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
		return SEQUENCE(stmts);
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
				for (int i = 0; i != vars.size(); ++i) {
					WyilFile.Decl.Variable ith = vars.get(i);
					decls.add(new Decl.Variable(ith.getName().get(), constructType(ith.getType())));
				}
			}

			@Override
			public void visitAssign(WyilFile.Stmt.Assign stmt) {
				super.visitAssign(stmt);
				if (!WyilUtils.isSimple(stmt) && WyilUtils.hasInterference(stmt, meter)) {
					Tuple<WyilFile.LVal> lhs = stmt.getLeftHandSide();
					for (int i = 0, k = 0; i != lhs.size(); ++i) {
						WyilFile.LVal lv = lhs.get(i);
						WyilFile.Type t = lv.getType();
						for (int j = 0; j != t.shape(); ++j) {
							Type type = constructType(t.dimension(j));
							decls.add(new Decl.Variable(TEMP(stmt, k), type));
							k = k + 1;
						}
					}
				}
			}

			@Override
			public void visitFor(WyilFile.Stmt.For stmt) {
				super.visitFor(stmt);
				WyilFile.Decl.StaticVariable v = stmt.getVariable();
				String name = v.getName().toString();
				Type type = constructType(v.getType());
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
	public Decl.Axiom constructPostconditionAxiom(WyilFile.Decl.FunctionOrMethod d, String name,
			List<Decl.Parameter> parameters, List<Decl.Parameter> returns) {
		//
		if (d instanceof WyilFile.Decl.Function && parameters.size() == 0) {
			// Easy case, since we don't even need a quantifier.
			return new Decl.Axiom(CALL(name + "#post", CALL(name)));
		} else {
			// A universal quantifier is required!
			List<Expr> args = new ArrayList<>();
			// Add heap variable (if applicable)
			if (d instanceof WyilFile.Decl.Method) {
				// Clone parameters list to prevent side-effects
				parameters = new ArrayList<>(parameters);
				// Insert new parameter at the beginning
				parameters.add(0, new Decl.Variable("Heap#", REFMAP));
			}
			// Add remaining arguments
			for (int i = 0; i != parameters.size(); ++i) {
				args.add(VAR(parameters.get(i).getName()));
			}
			ArrayList<Expr> postArgs = new ArrayList<>(args);
			//
			if (returns.size() == 1) {
				postArgs.add(CALL(name, args));
			} else {
				// Functions with multiple returns require special handling
				for (int i = 0; i != returns.size(); ++i) {
					postArgs.add(CALL(name + "#" + i, args));
				}
			}
			// Construct the axiom
			return new Decl.Axiom(
					FORALL(parameters, IMPLIES(CALL(name + "#pre", args), CALL(name + "#post", postArgs))));
		}
	}

	@Override
	public Expr constructLambda(WyilFile.Decl.Lambda decl, Expr body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructAssert(WyilFile.Stmt.Assert stmt, Expr condition, List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.Assert(condition));
	}

	@Override
	public Stmt constructAssign(WyilFile.Stmt.Assign stmt, List<Expr> _, List<Expr> rhs, List<Expr> preconditions) {
		ArrayList<Stmt> stmts = new ArrayList<>();
		// First, flatten left-hand side
		List<WyilFile.LVal> lvals = flatternAssignmentLeftHandSide(stmt.getLeftHandSide());
		// Second, flatten right-hand side
		List<Expr> rvals = flatternAssignmentRightHandSide(rhs);
		// Third, coerce right-hand side elements
		rvals = coerceAssignmentRightHandSide(lvals, stmt.getRightHandSide(), rvals);
		// Fourth, determine whether simple assign sufficient (or not)
		if (!WyilUtils.isSimple(stmt) && WyilUtils.hasInterference(stmt, meter)) {
			// Simple assignment is insufficient. Therefore, we need to assign every element
			// on the right-hand side into a temporary variable before (subsequently)
			// assigning it into the corresponding item on the left-hand side.
			for (int i = 0; i != rvals.size(); ++i) {
				// Assign item on rhs into temporary
				stmts.add(ASSIGN(VAR(TEMP(stmt, i)), rvals.get(i)));
				// Setup assignment from temporary to the lhs
				rvals.set(i, VAR(TEMP(stmt, i)));
			}
		}
		// Finally, action final assignments.
		for (int i = 0; i != lvals.size(); ++i) {
			stmts.add(constructAssign(lvals.get(i), rvals.get(i)));
		}
		// Done
		return SEQUENCE(stmts);
	}

	/**
	 * Flatten the left-hand side into an array of individual lvals. For example:
	 * 
	 * <pre>
	 * x,(y,z) = 1,f()
	 * </pre>
	 * 
	 * The left-hand side of the assignment would be flatterned into
	 * <code>x,y,z</code>. The purpose of flattening is simply to align primitive
	 * assignments on the left-hand side with those on the right hand side. In a
	 * general sense, this doesn't work because (as above) we may have fewer items
	 * on the right-hand side (strictly speaking). However, in this Boogie
	 * translation this will never arise because <code>FauxTuple</code>s have been
	 * employed to ensure they line up. More specifically, the above would become:
	 * 
	 * <pre>
	 * x,y,z = 1,f#1(),f#2
	 * </pre>
	 * 
	 * @param lhs
	 * @return
	 */
	private List<WyilFile.LVal> flatternAssignmentLeftHandSide(Tuple<WyilFile.LVal> lhs) {
		ArrayList<WyilFile.LVal> lvals = new ArrayList<>();
		for (int i = 0; i != lhs.size(); ++i) {
			WyilFile.LVal ith = lhs.get(i);
			if (ith instanceof WyilFile.Expr.TupleInitialiser) {
				WyilFile.Expr.TupleInitialiser ti = (WyilFile.Expr.TupleInitialiser) ith;
				for (int j = 0; j < ti.size(); ++j) {
					lvals.add((WyilFile.LVal) ti.get(j));
				}
			} else {
				lvals.add(ith);
			}
		}
		return lvals;
	}

	/**
	 * Flattern the right-hand side of a given assignment. This is relatively
	 * straightforward, though we just need to expand any <code>FauxTuple</code>s
	 * that we encounter. For example, the following:
	 * 
	 * <pre>
	 * x,(y,z) = 1,f()
	 * </pre>
	 * 
	 * The right-hand side above is translated into the following:
	 * 
	 * <pre>
	 * x,(y,z) = 1,(f#1(),f#2())
	 * </pre>
	 * 
	 * Here, <code>(f#1(),f#2())</code> is a <i>faux tuple</i>.
	 * 
	 * @param rhs
	 * @return
	 */
	private List<Expr> flatternAssignmentRightHandSide(List<Expr> rhs) {
		ArrayList<Expr> rvals = new ArrayList<>();
		// First, flattern all rvals
		for (int i = 0; i != rhs.size(); ++i) {
			Expr ith = rhs.get(i);
			if (ith instanceof FauxTuple) {
				rvals.addAll(((FauxTuple) ith).getItems());
			} else {
				rvals.add(ith);
			}
		}
		return rvals;
	}

	/**
	 * Coerce elements on the right-hand side of an assignment. This is necessary
	 * because some types in Boogie are boxed (e.g. arrays or unions), where as
	 * others are not (e.g. ints or booleans). Thus, consider the following:
	 * 
	 * <pre>
	 * int|null x = ...
	 * ...
	 * x = 1
	 * </pre>
	 * 
	 * In this case, the right-hand side has primitive (Boogie) type
	 * <code>int</code> (which is not boxex). whilst the left-hand side has (Boogie)
	 * type <code>Value</code> (which is boxed). Therefore, we need to box the
	 * right-hand side prior to the assignment.
	 * 
	 * @param lvals
	 * @param rhs
	 * @param rvals
	 * @return
	 */
	private List<Expr> coerceAssignmentRightHandSide(List<WyilFile.LVal> lvals, Tuple<WyilFile.Expr> rhs, List<Expr> rvals) {
		for (int i = 0, k = 0; i != rhs.size(); ++i) {
			WyilFile.Type t = rhs.get(i).getType();
			for (int j = 0; j < t.shape(); ++j) {
				WyilFile.Type l = lvals.get(k).getType();
				WyilFile.Type r = t.dimension(j);
				rvals.set(k, cast(l, r, rvals.get(k)));
				k = k + 1;
			}
		}
		return rvals;
	}

	public Stmt constructAssignOriginal(WyilFile.Stmt.Assign stmt, List<Expr> lvals, List<Expr> rvals,
			List<Expr> preconditions) {
		WyilFile.Tuple<WyilFile.LVal> lhs = stmt.getLeftHandSide();
		WyilFile.Tuple<WyilFile.Expr> rhs = stmt.getRightHandSide();
		//
		ArrayList<Stmt> stmts = new ArrayList<>();
		// Check whether parallel (easy) or sequential (hard) assignment
		if (WyilUtils.isSimple(stmt) || !WyilUtils.hasInterference(stmt, meter)) {
			// Easy case, parallel assignment meaning can make assignments directly.
			for (int i = 0; i != lvals.size(); ++i) {
				stmts.add(constructAssign(lhs.get(i), rhs.get(i), (LVal) lvals.get(i), rvals.get(i)));
			}
		} else {
			// Hard case, sequential assignment meaning must introduce temporary variables.
			ArrayList<Stmt> assigns = new ArrayList<>();
			for (int i = 0, k = 0; i != lvals.size(); ++i) {
				// Apply "split" assignment
				Pair<Stmt, Stmt> split = constructSplitAssign(stmt, k, lhs.get(i), rhs.get(i), lvals.get(i),
						rvals.get(i));
				// Distribute results
				stmts.add(split.first());
				assigns.add(split.second());
				// Done
				k = k + lhs.get(i).getType().shape();
			}
			stmts.addAll(assigns);
		}
		// Done
		return applyPreconditions(preconditions, SEQUENCE(stmts));
	}

	/**
	 * Construct a "split" assignment. This is one where the right-hand side is
	 * first assigned into a temporary before being finally assigned to the
	 * left-hand side. This generates two statements for each part so they can
	 * subsequently be combined in the right order.
	 *
	 * @param tmp Name of the temporary variable to use (which we assume has been
	 *            declared with the correct type).
	 * @param l
	 * @param r
	 * @return
	 */
	public Pair<Stmt, Stmt> constructSplitAssign(WyilFile.Stmt stmt, int k, WyilFile.LVal lhs, WyilFile.Expr rhs,
			Expr l, Expr r) {
		WyilFile.Type rhsT = rhs.getType();
		if (l instanceof FauxTuple) {
			ArrayList<Stmt> pre = new ArrayList<>();
			ArrayList<Stmt> post = new ArrayList<>();
			Tuple<WyilFile.Expr> lval = ((WyilFile.Expr.TupleInitialiser) lhs).getOperands();
			List<Expr> rvs = ((FauxTuple) r).getItems();
			for (int i = 0; i != rvs.size(); ++i, ++k) {
				// First assign right-hand sides to temporaries
				pre.add(ASSIGN(VAR(TEMP(stmt, k)), rvs.get(i)));
				// Second assign left-hand sides from temporaries
				post.add(constructAssign((WyilFile.LVal) lval.get(i), VAR(TEMP(stmt, k)), rhsT.dimension(i)));
			}
			return new Pair<>(SEQUENCE(pre), SEQUENCE(post));
		} else {
			return new Pair<>(ASSIGN(VAR(TEMP(stmt, k)), r), constructAssign(lhs, VAR(TEMP(stmt, k)), rhsT));
		}
	}

	/**
	 * Construct a straightforward assignment between an lval and an rval (both of
	 * which may, in fact, represent multiple values).
	 *
	 * @param lhs
	 * @param rhs
	 * @param l
	 * @param r
	 * @return
	 */
	public Stmt constructAssign(WyilFile.LVal lhs, WyilFile.Expr rhs, LVal l, Expr r) {
		WyilFile.Type lhsT = lhs.getType();
		WyilFile.Type rhsT = rhs.getType();
		if (l instanceof FauxTuple) {
			Tuple<WyilFile.Expr> lval = ((WyilFile.Expr.TupleInitialiser) lhs).getOperands();
			List<Expr> rvals = ((FauxTuple) r).getItems();
			ArrayList<Stmt> stmts = new ArrayList<>();
			for (int i = 0; i != lhsT.shape(); ++i) {
				// Construct sequential assignment
				stmts.add(constructAssign((WyilFile.LVal) lval.get(i), rvals.get(i), rhsT.dimension(i)));
			}
			return SEQUENCE(stmts);
		} else {
			return constructAssign(lhs, r, rhsT);
		}
	}

	public Stmt constructAssign(WyilFile.LVal lval, Expr rhs, WyilFile.Type rhsT) {
		WyilFile.Type lhsT = lval.getType();
		// Cast right-hand side as necessary
		rhs = cast(lhsT,rhsT,rhs);
		// Recursively rebuild assignment
		return constructAssign(lval, rhs);
	}

	/**
	 * Construct an assignment statement for a given lhs and rhs. The challenge here
	 * stems from the requirement in Boogie that we cannot assign to multiple nested
	 * dictionaries (e.g. <code>xs[i][j] = ...</code> is not permitted).
	 *
	 * @param lval Raw left-hand side
	 * @param rhs Translated and coerced right-hand side(s)
	 * @return
	 */
	public Stmt constructAssign(WyilFile.LVal lval, Expr rhs) {
		switch (lval.getOpcode()) {
		case WyilFile.EXPR_arrayaccess:
		case WyilFile.EXPR_arrayborrow: {
			WyilFile.Expr.ArrayAccess l = (WyilFile.Expr.ArrayAccess) lval;
			// Reconstruct source expression
			Expr src = visitExpression(l.getFirstOperand());
			// Reconstruct index expression
			Expr index = visitExpression(l.getSecondOperand());
			// Box the right-hand side (as necessary)
			rhs = box(lval.getType(),rhs);
			// Done
			return constructAssign((WyilFile.LVal) l.getFirstOperand(), PUT(src, index, rhs));
		}
		case WyilFile.EXPR_dereference: {

		}
		case WyilFile.EXPR_fielddereference: {

		}
		case WyilFile.EXPR_recordaccess:
		case WyilFile.EXPR_recordborrow: {
			WyilFile.Expr.RecordAccess l = (WyilFile.Expr.RecordAccess) lval;
			// Reconstruct source expression
			Expr src = visitExpression(l.getOperand());
			// Reconstruct index expression
			Expr index = VAR("$" + l.getField());
			// Box the right-hand side (as necessary)
			rhs = box(lval.getType(),rhs);
			// Done
			return constructAssign((WyilFile.LVal) l.getOperand(), PUT(src, index, rhs));
		}
		case WyilFile.EXPR_variablecopy:
		case WyilFile.EXPR_variablemove: {
			LVal l = (LVal) constructVariableAccess((WyilFile.Expr.VariableAccess) lval);
			// Done
			return new Stmt.Assignment(l, rhs);
		}
		default:
			throw new UnsupportedOperationException("invalid lval");
		}
	}

	@Override
	public Stmt constructAssume(WyilFile.Stmt.Assume stmt, Expr condition, List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.Assume(condition));
	}

	@Override
	public Stmt constructBlock(WyilFile.Stmt.Block stmt, List<Stmt> stmts) {
		return SEQUENCE(stmts);
	}

	@Override
	public Stmt constructBreak(WyilFile.Stmt.Break stmt) {
		WyilFile.Stmt loop = getEnclosingLoop(stmt);
		return GOTO("BREAK_" + loop.getIndex());
	}

	@Override
	public Stmt constructContinue(WyilFile.Stmt.Continue stmt) {
		WyilFile.Stmt loop = getEnclosingLoop(stmt);
		return GOTO("CONTINUE_" + loop.getIndex());
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
		return SEQUENCE(body, loop);
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
		Stmt.While loop = new Stmt.While(condition, invariant, SEQUENCE(loopBody));
		// FIXME: handle preconditions
		// Done.
		return SEQUENCE(init, loop);
	}

	@Override
	public Stmt constructIfElse(WyilFile.Stmt.IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch,
			List<Expr> preconditions) {
		return applyPreconditions(preconditions, new Stmt.IfElse(condition, trueBranch, falseBranch));
	}

	@Override
	public Stmt constructInitialiser(WyilFile.Stmt.Initialiser stmt, Expr init, List<Expr> preconditions) {
		WyilFile.Tuple<WyilFile.Decl.Variable> vars = stmt.getVariables();
		//
		if (init == null) {
			return SEQUENCE();
		} else {
			ArrayList<Stmt> stmts = new ArrayList<>();
			// Extract list of initialiser expressions
			List<Expr> inits = (init instanceof FauxTuple) ? ((FauxTuple) init).getItems() : Arrays.asList(init);
			// Determine type of initialiser expression
			WyilFile.Type initT = stmt.getInitialiser().getType();
			// Assign to each variable
			for (int i = 0; i != vars.size(); ++i) {
				WyilFile.Decl.Variable ith = vars.get(i);
				String name = ith.getName().toString();
				stmts.add(ASSIGN(new Expr.VariableAccess(name), cast(ith.getType(), initT.dimension(i), inits.get(i))));
			}
			// FIXME: need post condition!
			return applyPreconditions(preconditions, SEQUENCE(stmts));
		}
	}

	@Override
	public Stmt constructInvokeStmt(WyilFile.Expr.Invoke expr, List<Expr> arguments, List<Expr> preconditions) {
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIndirectInvokeStmt(WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> arguments,
			List<Expr> preconditions) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructNamedBlock(WyilFile.Stmt.NamedBlock stmt, List<Stmt> stmts) {
		// Named blocks are really a relic from the past which probably cannot currently
		// be encountered at the source-level in Whiley.
		throw new UnsupportedOperationException();
	}

	@Override
	public Stmt constructReturn(WyilFile.Stmt.Return stmt, Expr ret, List<Expr> preconditions) {
		if (ret != null) {
			// Identify enclosing function or method to figure out names of return
			// variables.
			WyilFile.Decl.Callable enclosing = stmt.getAncestor(WyilFile.Decl.FunctionOrMethod.class);
			WyilFile.Tuple<WyilFile.Decl.Variable> returns = enclosing.getReturns();
			WyilFile.Type type = stmt.getReturn().getType();
			// Extract return values
			List<Expr> rvs = returns.size() == 1 ? Arrays.asList(ret) : ((FauxTuple) ret).getItems();
			// Construct return value assignments
			ArrayList<Stmt> stmts = new ArrayList<>();
			for (int i = 0; i != rvs.size(); ++i) {
				WyilFile.Decl.Variable ith = returns.get(i);
				String rv = ith.getName().get();
				// Cast returned value as necessary
				Expr re = cast(ith.getType(), type.dimension(i), rvs.get(i));
				// Done
				stmts.add(new Stmt.Assignment(VAR(rv), re));
			}
			// Add the actual return statement
			stmts.add(new Stmt.Return());
			// Done
			return applyPreconditions(preconditions, SEQUENCE(stmts));
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
		String defaultLabel = "SWITCH_" + stmt.getIndex() + "_DEFAULT";
		Stmt defaultCase = null;
		// Construct case labels (ignoring default)
		List<String> labels = new ArrayList<>();
		for (int i = 0; i != cases.size(); ++i) {
			boolean isDefault = cases.get(i).first().isEmpty();
			if (!isDefault) {
				labels.add("SWITCH_" + stmt.getIndex() + "_" + i);
			}
		}
		// Add branch to default label
		labels.add(defaultLabel);
		// Construct non-deterministic goto
		stmts.add(GOTO(labels));
		// Construct cases
		ArrayList<Expr> defaultCases = new ArrayList<>();
		for (int i = 0; i != cases.size(); ++i) {
			Pair<List<Expr>, Stmt> ith = cases.get(i);
			List<Expr> ith_first = ith.first();
			ArrayList<Expr> cs = new ArrayList<>();
			for (int j = 0; j != ith_first.size(); ++j) {
				cs.add(EQ(condition, ith_first.get(j)));
				defaultCases.add(NEQ(condition, ith_first.get(j)));
			}
			if (cs.isEmpty()) {
				defaultCase = ith.second();
			} else {
				stmts.add(new Stmt.Label(labels.get(i)));
				stmts.add(new Stmt.Assume(OR(cs)));
				stmts.add(ith.second());
				stmts.add(GOTO(breakLabel));
			}
		}
		// Construct default case
		stmts.add(new Stmt.Label(defaultLabel));
		stmts.add(new Stmt.Assume(AND(defaultCases)));
		if (defaultCase != null) {
			stmts.add(defaultCase);
		}
		stmts.add(GOTO(breakLabel));
		// Add final break label
		stmts.add(new Stmt.Label(breakLabel));
		// Done
		return applyPreconditions(preconditions, SEQUENCE(stmts));
	}

	@Override
	public Stmt constructWhile(WyilFile.Stmt.While stmt, Expr condition, List<Expr> invariant, Stmt body,
			List<Expr> preconditions) {
		boolean needContinueLabel = containsContinueOrBreak(stmt, false);
		boolean needBreakLabel = containsContinueOrBreak(stmt, true);
		Stmt.While s = new Stmt.While(condition, invariant, body);
		// FIXME: handle preconditions
		// Handle need for continue / break
		if (needContinueLabel && needBreakLabel) {
			Stmt.Label continueLabel = new Stmt.Label("CONTINUE_" + stmt.getIndex());
			Stmt.Label breakLabel = new Stmt.Label("BREAK_" + stmt.getIndex());
			return SEQUENCE(continueLabel, s, breakLabel);
		} else if (needContinueLabel) {
			Stmt.Label continueLabel = new Stmt.Label("CONTINUE_" + stmt.getIndex());
			return SEQUENCE(continueLabel, s);
		} else if (needBreakLabel) {
			Stmt.Label breakLabel = new Stmt.Label("BREAK_" + stmt.getIndex());
			return SEQUENCE(s, breakLabel);
		} else {
			return s;
		}
	}

	public Stmt applyPreconditions(List<Expr> preconditions, Stmt stmt) {
		if (preconditions.isEmpty()) {
			return stmt;
		} else {
			List<Stmt> assertions = constructAssertions(preconditions);
			return SEQUENCE(assertions, stmt);
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
		return new Expr.DictionaryAccess(source,VAR("$" + expr.getField()));
	}

	@Override
	public Expr constructTupleInitialiserLVal(WyilFile.Expr.TupleInitialiser expr, List<Expr> source) {
		return new FauxTuple(source);
	}

	@Override
	public Expr constructVariableAccessLVal(WyilFile.Expr.VariableAccess expr) {
		return constructVariableAccess(expr);
	}

	@Override
	public Expr constructArrayAccess(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
		System.out.println("UNBOXING: " + expr.getType());
		return unbox(expr.getType(), new Expr.DictionaryAccess(source, index));
	}

	@Override
	public Expr constructArrayLength(WyilFile.Expr.ArrayLength expr, Expr source) {
		return CALL("Array#Length", source);
	}

	@Override
	public Expr constructArrayGenerator(WyilFile.Expr.ArrayGenerator expr, Expr value, Expr length) {
		WyilFile.Type vt = expr.getFirstOperand().getType();
		WyilFile.Type lt = expr.getSecondOperand().getType();
		return CALL("Array#Generator", box(vt, value), cast(WyilFile.Type.Int, lt, length));
	}

	@Override
	public Expr constructArrayInitialiser(WyilFile.Expr.ArrayInitialiser expr, List<Expr> values) {
		WyilFile.Type elementType = expr.getType().as(WyilFile.Type.Array.class).getElement();
		Expr arr = CALL("Array#Empty", CONST(values.size()));
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
		return CALL("Byte#Not", operand);
	}

	@Override
	public Expr constructBitwiseAnd(WyilFile.Expr.BitwiseAnd expr, List<Expr> operands) {
		Expr e = operands.get(0);
		for (int i = 1; i != operands.size(); ++i) {
			e = CALL("Byte#And", e, operands.get(i));
		}
		return e;
	}

	@Override
	public Expr constructBitwiseOr(WyilFile.Expr.BitwiseOr expr, List<Expr> operands) {
		Expr e = operands.get(0);
		for (int i = 1; i != operands.size(); ++i) {
			e = CALL("Byte#Or", e, operands.get(i));
		}
		return e;
	}

	@Override
	public Expr constructBitwiseXor(WyilFile.Expr.BitwiseXor expr, List<Expr> operands) {
		Expr e = operands.get(0);
		for (int i = 1; i != operands.size(); ++i) {
			e = CALL("Byte#Xor", e, operands.get(i));
		}
		return e;
	}

	@Override
	public Expr constructBitwiseShiftLeft(WyilFile.Expr.BitwiseShiftLeft expr, Expr lhs, Expr rhs) {
		return CALL("Byte#Shl", lhs, CALL("Byte#fromInt", rhs));
	}

	@Override
	public Expr constructBitwiseShiftRight(WyilFile.Expr.BitwiseShiftRight expr, Expr lhs, Expr rhs) {
		return CALL("Byte#Shr", lhs, CALL("Byte#fromInt", rhs));
	}

	@Override
	public Expr constructCast(WyilFile.Expr.Cast expr, Expr operand) {
		// FIXME: unsure whether this is sufficient.
		return cast(expr.getType(), expr.getOperand().getType(), operand);
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
		case WyilFile.ITEM_byte: {
			byte b = ((WyilFile.Value.Byte) v).get();
			return new Expr.Constant(new byte[] { b });
		}
		case WyilFile.ITEM_int: {
			BigInteger i = ((WyilFile.Value.Int) v).get();
			return CONST(i);
		}
		case WyilFile.ITEM_utf8: {
			byte[] bytes = ((WyilFile.Value.UTF8) v).get();
			Expr arr = CALL("Array#Empty", CONST(bytes.length));
			//
			for (int i = 0; i != bytes.length; ++i) {
				Expr ith = box(WyilFile.Type.Int, new Expr.Constant(bytes[i]));
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
		return unbox(expr.getType(), new Expr.DictionaryAccess(VAR("Heap#"), operand));
	}

	@Override
	public Expr constructFieldDereference(WyilFile.Expr.FieldDereference expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructEqual(WyilFile.Expr.Equal expr, Expr lhs, Expr rhs) {
		WyilFile.Type lhsT = expr.getFirstOperand().getType();
		WyilFile.Type rhsT = expr.getSecondOperand().getType();
		boolean boxing = !lhsT.equals(rhsT);
		//
		if (lhs instanceof FauxTuple) {
			List<Expr> ls = ((FauxTuple) lhs).getItems();
			List<Expr> rs = ((FauxTuple) rhs).getItems();
			Expr result = null;
			for (int i = 0; i != lhsT.shape(); ++i) {
				Expr l = ls.get(i);
				Expr r = rs.get(i);
				l = boxing ? box(lhsT.dimension(i), l) : l;
				r = boxing ? box(rhsT.dimension(i), r) : r;
				result = i == 0 ? EQ(l, r) : AND(result, EQ(l, r));
			}
			// Done
			return result;
		} else if (boxing) {
			return EQ(box(lhsT, lhs), box(rhsT, rhs));
		} else {
			return EQ(lhs, rhs);
		}
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
		return constructTypeTest(expr.getTestType(), expr.getOperand().getType(), operand);
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
	public Expr constructExistentialQuantifier(WyilFile.Expr.ExistentialQuantifier expr, List<Pair<Expr, Expr>> ranges,
			Expr body) {
		WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
		List<Decl.Parameter> ps = new ArrayList<>();
		List<Expr> clauses = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			Pair<Expr, Expr> ith = ranges.get(i);
			String name = params.get(i).getName().get();
			ps.add(new Decl.Parameter(name, Type.Int));
			clauses.add(LTEQ(ith.first(), VAR(name)));
			clauses.add(LT(VAR(name), ith.second()));
		}
		clauses.add(body);
		return new Expr.Quantifier(false, AND(clauses), ps);
	}

	@Override
	public Expr constructUniversalQuantifier(WyilFile.Expr.UniversalQuantifier expr, List<Pair<Expr, Expr>> ranges,
			Expr body) {
		WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
		List<Decl.Parameter> ps = new ArrayList<>();
		List<Expr> clauses = new ArrayList<>();
		for (int i = 0; i != params.size(); ++i) {
			Pair<Expr, Expr> ith = ranges.get(i);
			String name = params.get(i).getName().get();
			ps.add(new Decl.Parameter(name, Type.Int));
			clauses.add(LTEQ(ith.first(), VAR(name)));
			clauses.add(LT(VAR(name), ith.second()));
		}
		return new Expr.Quantifier(true, IMPLIES(AND(clauses), body), ps);
	}

	@Override
	public Expr constructInvoke(WyilFile.Expr.Invoke expr, List<Expr> arguments) {
		WyilFile.Decl.Callable ft = expr.getLink().getTarget();
		WyilFile.Type ftrt = ft.getType().getReturn();
		WyilFile.Type rt = expr.getBinding().getConcreteType().getReturn();
		boolean method = ft instanceof WyilFile.Decl.Method;
		// Apply name mangling
		String name = toMangledName(expr.getLink().getTarget());
		// Apply conversions to arguments as necessary
		arguments = cast(ft.getType().getParameter(), expr.getOperands(), arguments);
		//
		if (method) {
			// Add heap argument to invocation to ensure (amongst other things)
			// non-determinism.
			arguments.add(0, VAR("Heap#"));
		}
		//
		if (rt.shape() == 1) {
			return cast(rt, ftrt, CALL(name, arguments));
		} else {
			List<Expr> items = new ArrayList<>();
			for (int i = 0; i != rt.shape(); ++i) {
				items.add(cast(rt.dimension(i), ftrt.dimension(i), CALL(name + "#" + i, arguments)));
			}
			return new FauxTuple(items);
		}
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
		WyilFile.Type lhsT = expr.getFirstOperand().getType();
		WyilFile.Type rhsT = expr.getSecondOperand().getType();
		boolean boxing = !lhsT.equals(rhsT);
		//
		if (lhs instanceof FauxTuple) {
			List<Expr> ls = ((FauxTuple) lhs).getItems();
			List<Expr> rs = ((FauxTuple) rhs).getItems();
			Expr result = null;
			for (int i = 0; i != lhsT.shape(); ++i) {
				Expr l = ls.get(i);
				Expr r = rs.get(i);
				l = boxing ? box(lhsT.dimension(i), l) : l;
				r = boxing ? box(rhsT.dimension(i), r) : r;
				result = i == 0 ? NEQ(l, r) : OR(result, NEQ(l, r));
			}
			// Done
			return result;
		} else if (boxing) {
			return NEQ(box(lhsT, lhs), box(rhsT, rhs));
		} else {
			return NEQ(lhs, rhs);
		}
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
		Expr rec = VAR("Record#Empty");
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
		// NOTE: at this stage, we won't attempt to support general first-class tuples.
		return new FauxTuple(operands);
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
		WyilFile.Type declared = expr.getVariableDeclaration().getType();
		WyilFile.Type actual = expr.getType();
		return cast(actual, declared, VAR(expr.getVariableDeclaration().getName().toString()));
	}

	// =========================================================================================
	// Preconditions
	// =========================================================================================

	@Override
	public Expr constructArrayAccessPrecondition(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
		return AND(LTEQ(CONST(0), index), LT(index, CALL("Array#Length", source)));
	}

	@Override
	public Expr constructIntegerDivisionPrecondition(WyilFile.Expr.IntegerDivision expr, Expr lhs, Expr rhs) {
		return NEQ(rhs, CONST(0));
	}

	@Override
	public Expr constructInvokePrecondition(WyilFile.Expr.Invoke expr, List<Expr> args) {
		WyilFile.Decl.Callable c = expr.getLink().getTarget();
		// Mangle target name
		String name = toMangledName(c);
		// Coerce argument types (as necessary)
		args = cast(c.getType().getParameter(), expr.getOperands(), args);
		//
		if (c instanceof WyilFile.Decl.Function) {
			return CALL(name + "#pre", args);
		} else if (c instanceof WyilFile.Decl.Method) {
			args.add(0, VAR("Heap#"));
			return CALL(name + "#pre", args);
		} else {
			return null;
		}
	}

	// =========================================================================================
	// Types
	// =========================================================================================

	public Type constructType(WyilFile.Type type) {
		// FIXME: this should be moved into AbstractTranslator.
		switch (type.getOpcode()) {
		case WyilFile.TYPE_bool:
			return Type.Bool;
		case WyilFile.TYPE_byte:
			return Type.BitVector8;
		case WyilFile.TYPE_int:
			return Type.Int;
		case WyilFile.TYPE_reference:
			return REF;
		case WyilFile.TYPE_universal:
			return VALUE;
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

	public Type constructArrayType(WyilFile.Type.Array type) {
		return INTMAP;
	}

	public Type constructRecordType(WyilFile.Type.Record type) {
		return FIELDMAP;
	}

	public Type constructUnionType(WyilFile.Type.Union type) {
		return VALUE;
	}

	public Type constructNominalType(WyilFile.Type.Nominal type) {
		// Apply name mangling
		String name = toMangledName(type.getLink().getTarget());
		// Done!
		return new Type.Synonym(name);
	}

	@Override
	public Stmt applyImplicitCoercion(wyil.lang.WyilFile.Type target, wyil.lang.WyilFile.Type source, Stmt expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	/**
	 * Construct a runtime type test for a given argument operand. For example,
	 * consider the following:
	 *
	 * <pre>
	 * function f(int|null x) -> (int r):
	 *   if x is null:
	 *      return 0
	 *   else:
	 *      return x
	 * </pre>
	 *
	 * The expression <code>x is null</code> will be translated by this function.
	 *
	 * @param to       The type being tested against.
	 * @param from     The argument type
	 * @param argument The argument being tested.
	 * @return
	 */
	private Expr constructTypeTest(WyilFile.Type to, WyilFile.Type from, Expr argument) {
		switch (to.getOpcode()) {
		case WyilFile.TYPE_null:
			return EQ(argument, CONST(null));
		case WyilFile.TYPE_bool:
			return CALL("Bool#is", box(from, argument));
		case WyilFile.TYPE_byte:
			return CALL("Byte#is", box(from, argument));
		case WyilFile.TYPE_int:
			return CALL("Int#is", box(from, argument));
		case WyilFile.TYPE_nominal:
			return constructNominalTypeTest((WyilFile.Type.Nominal) to, from, argument);
		case WyilFile.TYPE_array:
			return constructArrayTypeTest((WyilFile.Type.Array) to, from, argument);
		case WyilFile.TYPE_record:
			return constructRecordTypeTest((WyilFile.Type.Record) to, from, argument);
		default:
			throw new IllegalArgumentException("unknown type encoutnered (" + to.getClass().getName() + ")");
		}
	}

	/**
	 * Construct a type test for a nominal type. This is done by simple calling the
	 * <code>is</code> method for the corresponding nominal type. For example,
	 * consider the following:
	 *
	 * <pre>
	 * type nat is (int x) where ...
	 *
	 *   ...
	 *   if x is nat:
	 *      ...
	 * </pre>
	 *
	 * For the type <code>nat</code> we will generate:
	 *
	 * <pre>
	 * function nat#is(Value v) { ... }
	 * </pre>
	 *
	 * And we can translate <code>x is nat</code> as a call to this function.
	 *
	 * @param to
	 * @param from
	 * @param argument
	 * @return
	 */
	private Expr constructNominalTypeTest(WyilFile.Type.Nominal to, WyilFile.Type from, Expr argument) {
		// Construct appropriate name mangle
		String name = toMangledName(to.getLink().getTarget());
		// Ensure argument is boxed
		return CALL(name + "#is", cast(to, from, argument));
	}

	/**
	 * Construct a type test for an unadorned record type. For simplicity, this is
	 * done inline. For example:
	 *
	 * <pre>
	 *   ...
	 *   if x is {int f, bool g}:
	 *      ...
	 * </pre>
	 *
	 * Then, the <code>is</code> expression is translated as:
	 *
	 * <pre>
	 *   Int#is(x[f]) && Bool#is(x[g])
	 * </pre>
	 *
	 * @param to
	 * @param from
	 * @param argument
	 * @return
	 */
	private Expr constructRecordTypeTest(WyilFile.Type.Record to, WyilFile.Type from, Expr argument) {
		// NOTE: this method for describing a type test should be deprecated in the
		// future in favour of something based around type tags.
		//
		Tuple<WyilFile.Type.Field> fields = to.getFields();
		Expr[] clauses = new Expr[fields.size()];
		// Cast argument to correct (unboxed) type
		argument = cast(to, from, argument);
		// Iterate fields constructing tests for each.
		for (int i = 0; i != clauses.length; ++i) {
			WyilFile.Type.Field f = fields.get(i);
			String field = "$" + f.getName().get();
			clauses[i] = constructTypeTest(f.getType(), WyilFile.Type.Any, GET(argument, VAR(field)));
		}
		// Done
		return AND(clauses);
	}

	/**
	 * Construct a type test for an unadorned array type. For simplicity, this is
	 * done inline. For example:
	 *
	 * <pre>
	 *   ...
	 *   if x is int[]:
	 *      ...
	 * </pre>
	 *
	 * Then, the <code>is</code> expression is translated as:
	 *
	 * <pre>
	 *   (forall i:int :: 0 <= i && i < length(x) ==> Int#is(x[i]))
	 * </pre>
	 *
	 * @param to
	 * @param from
	 * @param argument
	 * @return
	 */
	private Expr constructArrayTypeTest(WyilFile.Type.Array to, WyilFile.Type from, Expr argument) {
		// NOTE: this method for describing a type test should be deprecated in the
		// future in favour of something based around type tags.
		//
		// Generate temporary index variable (which avoids name clashes)
		Expr.VariableAccess i = VAR("i#" + to.getIndex());
		// Cast argument to (unboxed) array type
		argument = cast(to, from, argument);
		// Construct bounds check for index variable
		Expr lhs = AND(LTEQ(CONST(0), i), LT(i, CALL("Array#Length", argument)));
		// Recursively construct type test for element
		Expr rhs = constructTypeTest(to.getElement(), WyilFile.Type.Any, GET(argument, i));
		// Done
		return FORALL(i.getVariable(), Type.Int, IMPLIES(lhs, rhs));
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
		axioms.add(new Decl.TypeSynonym("Value", null));
		// Define the top-level Whiley type which contains all others.
		axioms.add(new Decl.TypeSynonym("Type", null));
		// Add void constant
		axioms.add(new Decl.Constant(true, "Void", VALUE));
		// Add null constant
		axioms.add(new Decl.Constant(true, "null", VALUE));
		// Add all bool axioms
		axioms.addAll(constructBoolAxioms(wf));
		// Add all byte axioms
		axioms.addAll(constructByteAxioms(wf));
		// Add all int axioms
		axioms.addAll(constructIntAxioms(wf));
		// Add all array axioms
		axioms.addAll(constructArrayAxioms(wf));
		// Add all record axioms
		axioms.addAll(constructRecordAxioms(wf));
		// Add all array axioms
		axioms.addAll(constructReferenceAxioms(wf));
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
	private List<Decl> constructBoolAxioms(WyilFile wf) {
		ArrayList<Decl> decls = new ArrayList<>();
		decls.add(new Decl.LineComment("Booleans"));
		decls.add(FUNCTION("Bool#box", Type.Bool, VALUE));
		decls.add(FUNCTION("Bool#unbox", VALUE, Type.Bool));
		decls.add(FUNCTION("Bool#is", new Decl.Parameter("v", VALUE), Type.Bool,
				EXISTS("b", Type.Bool, EQ(CALL("Bool#box", VAR("b")), VAR("v")))));
		// Establish connection between toInt and fromInt
		decls.add(new Decl.Axiom(FORALL("i", Type.Bool, EQ(CALL("Bool#unbox", CALL("Bool#box", VAR("i"))), VAR("i")))));
		// Done
		return decls;
	}

	/**
	 * Construct axioms and functions relevant to integer types.
	 *
	 * @param wf
	 * @return
	 */
	private List<Decl> constructIntAxioms(WyilFile wf) {
		Decl header = new Decl.LineComment("Integers");
		Decl.Function fromInt = FUNCTION("Int#box", Type.Int, VALUE);
		Decl.Function toInt = FUNCTION("Int#unbox", VALUE, Type.Int);
		Decl.Function isInt = FUNCTION("Int#is", new Decl.Parameter("v", VALUE), Type.Bool,
				EXISTS("i", Type.Int, EQ(CALL("Int#box", VAR("i")), VAR("v"))));
		// Establish connection between toInt and fromInt
		Decl.Axiom axiom1 = new Decl.Axiom(
				FORALL("i", Type.Int, EQ(CALL("Int#unbox", CALL("Int#box", VAR("i"))), VAR("i"))));
		return Arrays.asList(header, fromInt, toInt, isInt, axiom1);
	}

	/**
	 * Construct axioms and functions relevant to byte types.
	 *
	 * @param wf
	 * @return
	 */
	private List<Decl> constructByteAxioms(WyilFile wf) {
		ArrayList<Decl> decls = new ArrayList<>();
		decls.add(new Decl.LineComment("Bytes"));
		decls.add(FUNCTION("Byte#box", Type.BitVector8, VALUE));
		decls.add(FUNCTION("Byte#unbox", VALUE, Type.BitVector8));
		decls.add(FUNCTION("Byte#toInt", Type.BitVector8, Type.Int, ":bvbuiltin", "\"bv2int\""));
		decls.add(FUNCTION("Byte#is", new Decl.Parameter("v", VALUE), Type.Bool,
				EXISTS("b", Type.BitVector8, EQ(CALL("Byte#box", VAR("b")), VAR("v")))));
		// NOTE: figuring out int2bv was a challenge!
		decls.add(FUNCTION("Byte#fromInt", Type.Int, Type.BitVector8, ":bvbuiltin", "\"(_ int2bv 8)\""));
		decls.add(FUNCTION("Byte#Not", Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvnot\""));
		decls.add(FUNCTION("Byte#And", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvand\""));
		decls.add(FUNCTION("Byte#Or", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvor\""));
		decls.add(FUNCTION("Byte#Xor", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvxor\""));
		decls.add(FUNCTION("Byte#Shl", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvshl\""));
		decls.add(FUNCTION("Byte#Shr", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvlshr\""));
		// Establish connection between toByte and fromByte
		decls.add(new Decl.Axiom(
				FORALL("b", Type.BitVector8, EQ(CALL("Byte#unbox", CALL("Byte#box", VAR("b"))), VAR("b")))));
		// Done
		return decls;
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
		decls.add(FUNCTION("Array#box", INTMAP, VALUE));
		decls.add(FUNCTION("Array#unbox", VALUE, INTMAP));
		// Establish connection between toInt and fromInt
		decls.add(new Decl.Axiom(FORALL("i", INTMAP, EQ(CALL("Array#unbox", CALL("Array#box", VAR("i"))), VAR("i")))));
		// Array length function
		decls.add(FUNCTION("Array#Length", INTMAP, Type.Int));
		// Enforce array length is non-negative
		decls.add(new Decl.Axiom(FORALL("a", INTMAP, LTEQ(CONST(0), CALL("Array#Length", VAR("a"))))));
		// Empty arrays
		decls.add(FUNCTION("Array#Empty", Type.Int, INTMAP));
		decls.add(FUNCTION("Array#Generator", VALUE, Type.Int, INTMAP));
		// Ensure that all elements outside array length are void
		decls.add(new Decl.Axiom(
				FORALL("l", Type.Int, "i", Type.Int, OR(AND(LTEQ(CONST(0), VAR("i")), LT(VAR("i"), VAR("l"))),
						EQ(GET(CALL("Array#Empty", VAR("l")), VAR("i")), VAR("Void"))))));
		// Relate empty array with its length
		decls.add(new Decl.Axiom(FORALL("a", INTMAP, "l", Type.Int,
				OR(NEQ(CALL("Array#Empty", VAR("l")), VAR("a")), EQ(CALL("Array#Length", VAR("a")), VAR("l"))))));
		// Ensure that all elements inside generator length are void
		decls.add(new Decl.Axiom(FORALL("v", VALUE, "l", Type.Int, "i", Type.Int, OR(LT(VAR("i"), CONST(0)),
				LTEQ(VAR("l"), VAR("i")), EQ(GET(CALL("Array#Generator", VAR("v"), VAR("l")), VAR("i")), VAR("v"))))));
		// Ensure that all elements outside generator length are void
		decls.add(new Decl.Axiom(FORALL("v", VALUE, "l", Type.Int, "i", Type.Int,
				OR(AND(LTEQ(CONST(0), VAR("i")), LT(VAR("i"), VAR("l"))),
						EQ(GET(CALL("Array#Generator", VAR("v"), VAR("l")), VAR("i")), VAR("Void"))))));
		// Relate array generator with its length
		decls.add(new Decl.Axiom(FORALL("a", INTMAP, "v", VALUE, "l", Type.Int,
				OR(NEQ(CALL("Array#Generator", VAR("v"), VAR("l")), VAR("a")),
						EQ(CALL("Array#Length", VAR("a")), VAR("l"))))));
		// Relate updated array with its length
		decls.add(new Decl.Axiom(FORALL("a", INTMAP, "i", Type.Int, "v", VALUE,
				EQ(CALL("Array#Length", VAR("a")), CALL("Array#Length", PUT(VAR("a"), VAR("i"), VAR("v")))))));
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
		decls.add(new Decl.TypeSynonym("Field", null));
		// Add all known field names
		for (String field : determineFieldNames(wf)) {
			String name = "$" + field;
			decls.add(new Decl.Constant(true, name, FIELD));
		}
		//
		decls.add(new Decl.LineComment("Records"));
		decls.add(FUNCTION("Record#box", FIELDMAP, VALUE));
		decls.add(FUNCTION("Record#unbox", VALUE, FIELDMAP));
		// Establish connection between toInt and fromInt
		decls.add(new Decl.Axiom(
				FORALL("i", FIELDMAP, EQ(CALL("Record#unbox", CALL("Record#box", VAR("i"))), VAR("i")))));
		// Defines the empty record (i.e. the base from which all other records are
		// constructed).
		decls.add(new Decl.Constant(true, "Record#Empty", FIELDMAP));
		decls.add(new Decl.Axiom(FORALL("f", FIELD, EQ(GET(VAR("Record#Empty"), VAR("f")), VAR("Void")))));
		// Done
		return decls;
	}

	/**
	 * Construct axioms and functions relevant to reference types.
	 *
	 * @param wf
	 * @return
	 */
	private List<Decl> constructReferenceAxioms(WyilFile wf) {
		Decl header = new Decl.LineComment("References");
		Decl decl = new Decl.TypeSynonym("Ref", null);
		Decl heap = new Decl.Variable("Heap#", REFMAP);
		return Arrays.asList(header, decl, heap);
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

	private static List<Expr> cast(WyilFile.Type target, Tuple<WyilFile.Expr> from, List<Expr> args) {
		ArrayList<Expr> es = new ArrayList<>();
		for (int i = 0; i != args.size(); ++i) {
			es.add(cast(target.dimension(i), from.get(i).getType(), args.get(i)));
		}
		return es;
	}

	/**
	 * Box or Unbox a given type as necessary.
	 *
	 * @param to
	 * @param from
	 * @param e
	 * @return
	 */
	private static Expr cast(WyilFile.Type to, WyilFile.Type from, Expr e) {
		// Determine boxed status of each
		boolean t = isBoxed(to);
		boolean f = isBoxed(from);
		// box/unbox as necessary
		if (t && !f) {
			return box(from, e);
		} else if (!t && f) {
			return unbox(to, e);
		} else {
			return e;
		}
	}

	/**
	 * Determine whether the Boogie representation of a given Whiley type is
	 * naturally boxed or not. Boxed types are whose represented by `Value`.
	 * However, some Whiley types (e.g. `int`) can be represented directly in Boogie
	 * and, hence, are done so.
	 *
	 * @param type
	 * @return
	 */
	private static boolean isBoxed(WyilFile.Type type) {
		switch (type.getOpcode()) {
		case WyilFile.TYPE_any:
		case WyilFile.TYPE_reference:
		case WyilFile.TYPE_universal:
		case WyilFile.TYPE_union:
			return true;
		case WyilFile.TYPE_nominal: {
			WyilFile.Type.Nominal n = (WyilFile.Type.Nominal) type;
			// FIXME: problem with recursive types?
			return isBoxed(n.getConcreteType());
		}
		}
		return false;
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
		case WyilFile.TYPE_bool:
			return coerce(e, "Bool#unbox", "Bool#box");
		case WyilFile.TYPE_byte:
			return coerce(e, "Byte#unbox", "Byte#box");
		case WyilFile.TYPE_int:
			return coerce(e, "Int#unbox", "Int#box");
		case WyilFile.TYPE_record:
			return coerce(e, "Record#unbox", "Record#box");
		case WyilFile.TYPE_array:
			return coerce(e, "Array#unbox", "Array#box");
		case WyilFile.TYPE_nominal: {
			WyilFile.Type.Nominal t = (WyilFile.Type.Nominal) type;
			// Decision on whether boxing required depends on underlying type!
			return box(t.getConcreteType(), e);
		}
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
		case WyilFile.TYPE_bool:
			return coerce(e, "Bool#box", "Bool#unbox");
		case WyilFile.TYPE_byte:
			return coerce(e, "Byte#box", "Byte#unbox");
		case WyilFile.TYPE_int:
			return coerce(e, "Int#box", "Int#unbox");
		case WyilFile.TYPE_record:
			return coerce(e, "Record#box", "Record#unbox");
		case WyilFile.TYPE_array:
			return coerce(e, "Array#box", "Array#unbox");
		case WyilFile.TYPE_nominal: {
			WyilFile.Type.Nominal t = (WyilFile.Type.Nominal) type;
			// Decision on whether boxing required depends on underlying type!
			return unbox(t.getConcreteType(), e);
		}
		}
		return e;
	}

	/**
	 * Convert a given expression using two coercion functions (to and from). This
	 * performs some simple optimisations to eliminate chained coercions (e.g.
	 * <code>box(unbox(x))</code> becomes <code>x</code>).
	 *
	 * @param e
	 * @return
	 */
	private static Expr coerce(Expr e, String from, String to) {
		if (e instanceof Expr.Invoke) {
			Expr.Invoke i = (Expr.Invoke) e;
			if (i.getName().equals(from)) {
				return i.getArguments().get(0);
			}
		}
		return new Expr.Invoke(to, e);
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

	public static final Type VALUE = new Type.Synonym("Value");
	public static final Type VOID = new Type.Synonym("Void");
	public static final Type FIELD = new Type.Synonym("Field");
	public static final Type TYPE = new Type.Synonym("Type");
	public static final Type REF = new Type.Synonym("Ref");
	public static final Type INTMAP = new Type.Dictionary(Type.Int, VALUE);
	public static final Type FIELDMAP = new Type.Dictionary(FIELD, VALUE);
	public static final Type REFMAP = new Type.Dictionary(REF, VALUE);

	/**
	 * A "fake" tuple constructor. This is used to work around the
	 * <code>AbstractTranslator</code> which wants to turn a Wyil expression into a
	 * Boogie expression, but there are no tuples in Boogie! In fact, we don't need
	 * to implement arbitrary tuples in Boogie as, at this time, tuples in Whiley
	 * are quite limited.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class FauxTuple implements BoogieFile.Expr {
		private final List<Expr> items;

		public FauxTuple(List<Expr> items) {
			this.items = items;
		}

		public List<Expr> getItems() {
			return items;
		}
	}

	/**
	 * Construct a temporary variable associated with a given statement using a
	 * given identifier to distinguish different temporaries from the same
	 * statement.
	 *
	 * @param s
	 * @param id
	 * @return
	 */
	private static String TEMP(WyilFile.Stmt s, int id) {
		return "t" + s.getIndex() + "#" + id;
	}
}
