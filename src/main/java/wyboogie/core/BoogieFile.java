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
package wyboogie.core;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import wyboogie.io.BoogieFilePrinter;
import wyfs.lang.Content;
import wyfs.lang.Path;

public class BoogieFile {
	// =========================================================================
	// Content Type
	// =========================================================================

	/**
	 * Responsible for identifying and reading/writing WyilFiles. The normal
	 * extension is ".wyil" for WyilFiles.
	 */
	public static final Content.Type<BoogieFile> ContentType = new Content.Type<BoogieFile>() {
		public Path.Entry<BoogieFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<BoogieFile>) e;
			}
			return null;
		}

		@Override
		public BoogieFile read(Path.Entry<BoogieFile> e, InputStream input) throws IOException {
			// FIXME: this is a bit of a kludge for now.
			return new BoogieFile();
		}

		@Override
		public void write(OutputStream output, BoogieFile bf) throws IOException {
			new BoogieFilePrinter(output).write(bf);
		}

		@Override
		public String toString() {
			return "Content-Type: boogie";
		}

		@Override
		public String getSuffix() {
			return "bpl";
		}
	};

	/**
	 * The list of top-level declarations within this file.
	 */
	private List<Decl> declarations;

	public BoogieFile() {
		this.declarations = new ArrayList<>();
	}

	public List<Decl> getDeclarations() {
		return declarations;
	}

	public byte[] getBytes() {
		ByteArrayOutputStream output = new ByteArrayOutputStream();
		new BoogieFilePrinter(output).write(this);
		return output.toByteArray();
	}

	// =========================================================================
	// Declarations
	// =========================================================================

	public interface Decl {

		public static class Axiom {
			private final Expr operand;

			public Axiom(Expr operand) {
				this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		public static class Procedure implements Decl {
			private final String name;
			private final List<Parameter> parameters;
			private final List<Parameter> returns;
			private final List<Expr> requires;
			private final List<Expr> ensures;
			private final Stmt.Block body;

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr> requires, List<Expr> ensures, Stmt.Block body) {
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = new ArrayList<>(returns);
				this.requires = new ArrayList<>(requires);
				this.ensures = new ArrayList<>(ensures);
				this.body = body;
			}

			public String getName() {
				return name;
			}

			public List<Parameter> getParmeters() {
				return parameters;
			}

			public List<Parameter> getReturns() {
				return returns;
			}

			public List<Expr> getRequires() {
				return requires;
			}

			public List<Expr> getEnsures() {
				return ensures;
			}

			public Stmt.Block getBody() {
				return body;
			}
		}

		public static class Parameter {
			private final String name;
			private final Type type;

			public Parameter(String name, Type type) {
				this.name = name;
				this.type = type;
			}

			public String getName() {
				return name;
			}

			public Type getType() {
				return type;
			}
		}

	};

	// =========================================================================
	// Statements
	// =========================================================================

	public interface Stmt {
		public static class Block implements Stmt {
			private final List<Stmt> stmts;

			public Block(Collection<Stmt> stmts) {
				this.stmts = new ArrayList<>(stmts);
			}

			public int size() {
				return stmts.size();
			}

			public Stmt get(int i) {
				return stmts.get(i);
			}

			public List<Stmt> getAll() {
				return stmts;
			}
		}

		public static class Assert implements Stmt {
			private final Expr condition;

			public Assert(Expr condition) {
				this.condition = condition;
			}

			public Expr getCondition() {
				return condition;
			}
		}

		public static class Assume implements Stmt {
			private final Expr condition;

			public Assume(Expr condition) {
				this.condition = condition;
			}

			public Expr getCondition() {
				return condition;
			}
		}

		public static class Assignment implements Stmt {
			private final LVal lhs;
			private final Expr rhs;

			public Assignment(LVal lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public LVal getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class While implements Stmt {
			private final Expr condition;
			private final List<Expr> invariant;
			private final Stmt.Block body;

			public While(Expr condition, List<Expr> invariant, Stmt.Block body) {
				this.condition = condition;
				this.invariant = invariant;
				this.body = body;
			}

			public Expr getCondition() {
				return condition;
			}

			public List<Expr> getInvariant() {
				return invariant;
			}

			public Stmt.Block getBody() {
				return body;
			}
		}
		public static class Sequence implements Stmt {
			private final List<Stmt> stmts;

			public Sequence(Stmt... stmts) {
				this(Arrays.asList(stmts));
			}

			public Sequence(Collection<Stmt> stmts) {
				this.stmts = new ArrayList<>(stmts);
			}

			public int size() {
				return stmts.size();
			}

			public Stmt get(int i) {
				return stmts.get(i);
			}

			public List<Stmt> getAll() {
				return stmts;
			}
		}
		public static class VariableDeclarations implements Stmt {
			private final List<String> names;
			private final Type type;

			public VariableDeclarations(String name, Type type) {
				this(Arrays.asList(name),type);
			}

			public VariableDeclarations(List<String> names, Type type) {
				this.names = names;
				this.type = type;
			}

			public List<String> getNames() {
				return names;
			}

			public Type getType() {
				return type;
			}
		}
	}

	// =========================================================================
	// Expressions
	// =========================================================================

	public interface Expr extends Stmt {

		public static class Constant implements Expr {
			public final static Constant NULL = new Constant((String) null);
			public final static Constant TRUE = new Constant(true);
			public final static Constant FALSE = new Constant(false);

			private Object value;

			public Constant(boolean v) {
				this.value = v;
			}
			public Constant(byte v) {
				this.value = v;
			}
			public Constant(long v) {
				this.value = v;
			}
			public Constant(double v) {
				this.value = v;
			}
			public Constant(BigInteger v) {
				this.value = v;
			}
			public Constant(String v) {
				this.value = v;
			}

			public Object getValue() {
				return value;
			}
		}

		public static class BinaryOperator implements Expr {
			public enum Kind {
				EQ, NEQ, LT, LTEQ, GT, GTEQ, IFF, IF, ADD, SUB, MUL, DIV, REM
			}

			private Kind kind;
			private Expr lhs;
			private Expr rhs;

			public BinaryOperator(Kind kind, Expr lhs, Expr rhs) {
				this.kind = kind;
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Kind getKind() {
				return kind;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class UnaryOperator implements Expr {

		}

		public static class NaryOperator implements Expr {
			public enum Kind {
				AND, OR
			}

			private final Kind kind;
			private final  List<Expr> operands;

			public NaryOperator(Kind kind, List<Expr> operands) {
				this.kind = kind;
				this.operands = operands;
			}

			public Kind getKind() {
				return kind;
			}

			public List<Expr> getOperands() {
				return operands;
			}
		}

		public static class VariableAccess implements LVal {
			private final String variable;

			public VariableAccess(String var) {
				this.variable = var;
			}

			public String getVariable() {
				return variable;
			}
		}
	}

	public interface LVal extends Expr {

	}

	// =========================================================================
	// Types
	// =========================================================================

	public interface Type {
		public static final Type Bool = new Type() {};
		public static final Type Int = new Type() {};
		public static final Type Real = new Type() {};
	}
}
