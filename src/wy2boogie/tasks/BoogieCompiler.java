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
package wy2boogie.tasks;

import java.util.List;

import wy2boogie.core.BoogieFile;
import wy2boogie.core.BoogieFile.Decl;
import wy2boogie.core.BoogieFile.Expr;
import wy2boogie.core.BoogieFile.Stmt;
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLambda(Lambda decl, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructAssert(Assert stmt, Expr condition) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructAssign(Assign stmt, List<Expr> lvals, List<Expr> rvals) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructAssume(Assume stmt, Expr condition) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructBlock(Block stmt, List<Stmt> stmts) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructDoWhile(DoWhile stmt, Stmt body, Expr condition, List<Expr> invariant) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructFail(Fail stmt) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructFor(For stmt, Pair<Expr, Expr> range, List<Expr> invariant, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructIfElse(IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructInitialiser(Initialiser stmt, Expr initialiser) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructNamedBlock(NamedBlock stmt, List<Stmt> stmts) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructReturn(Return stmt, Expr ret) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructSkip(Skip stmt) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructSwitch(Switch stmt, Expr condition, List<Pair<List<Expr>, Stmt>> cases) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt constructWhile(While stmt, Expr condition, List<Expr> invariant, Stmt body) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
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
	public Expr constructConstant(Constant expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerLessThan(IntegerLessThan expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerLessThanOrEqual(IntegerLessThanOrEqual expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerGreaterThan(IntegerGreaterThan expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerGreaterThanOrEqual(IntegerGreaterThanOrEqual expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerNegation(IntegerNegation expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerAddition(IntegerAddition expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerSubtraction(IntegerSubtraction expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerMultiplication(IntegerMultiplication expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerDivision(IntegerDivision expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIntegerRemainder(IntegerRemainder expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructIs(Is expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalAnd(LogicalAnd expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalImplication(LogicalImplication expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalIff(LogicalIff expr, Expr lhs, Expr rhs) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalNot(LogicalNot expr, Expr operand) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Expr constructLogicalOr(LogicalOr expr, List<Expr> operands) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}

	@Override
	public Stmt applyImplicitCoercion(wyil.lang.WyilFile.Type target, wyil.lang.WyilFile.Type source, Stmt expr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("implement me");
	}
}
