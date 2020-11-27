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
import java.util.Collections;
import java.util.List;

import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Decl.Function;
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

		/**
		 * <p>
		 * Axioms are used to postulate properties of constants and functions, though
		 * cannot refer to global variables. <i>Care must be taken to ensure a given set
		 * of axioms are not inconsistent</i>. For example, <code>axiom false;</code> is
		 * the simplest inconsistent axiom. If this is included in a Boogie program then
		 * all asserts will verify regardless of whether they are correct or otherwise!
		 * For example, the following program verifies:
		 * </p>
		 *
		 * <pre>
		 * axiom false;
		 * procedure main() {
		 *   assert 1 < 0;
		 * }
		 * </pre>
		 *
		 * <p>
		 * Clearly, this does is not desirable!
		 * </p>
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Axiom implements Decl {
			private final Expr operand;

			public Axiom(Expr operand) {
				this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		/**
		 * Allows a line comment to be included in a <code>BoogieFile</code>. This is
		 * helpful for annotating generated declarations with helpful information about
		 * them.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LineComment implements Decl {
			private final String message;

			public LineComment(String message) {
				this.message = message;
			}

			public String getMessage() {
				return message;
			}
		}

		/**
		 * Represents a global (symbolic) constant value. Constants cannot overload, and
		 * the name of each must be distinct from the others and from any global
		 * variables. A constant can be marked <i>unique</i>, meaning it will not
		 * compare equal with any other unique constant. For example, we have the
		 * following:
		 *
		 * <pre>
		 * const unique X : int;
		 * const unique Y : int;
		 * const V : int;
		 *
		 * procedure main() {
		 *   assert X != Y;
		 *   assert X != V;
		 * }
		 * </pre>
		 *
		 * Here, the first assertion holds whilst the second does not.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Constant extends Parameter implements Decl {
			private final boolean unique;

			/**
			 * Construct a constant which is not unique.
			 *
			 * @param name Name of constant.
			 * @param type Type of constant.
			 */
			public Constant(String name, Type type) {
				super(name, type);
				this.unique = false;
			}

			/**
			 * Construct a constant which maybe unique.
			 *
			 * @param unique Flag to indicate whether constant is unique.
			 * @param name   Name of constant.
			 * @param type   Type of constant.
			 */
			public Constant(boolean unique, String name, Type type) {
				super(name, type);
				this.unique = unique;
			}

			/**
			 * Check whether a given constant is unique or not.
			 *
			 * @return
			 */
			public boolean isUnique() {
				return unique;
			}
		}

		public static class Function implements Decl {
			private final String name;
			private final List<String> attributes;
			private final List<Parameter> parameters;
			private final Type returns;
			private final Expr body;

			public Function(List<String> attributes, String name, List<Parameter> parameters, Type returns, Expr body) {
				this.attributes = attributes;
				this.name = name;
				this.parameters = parameters;
				this.returns = returns;
				this.body = body;
			}

			public String getName() {
				return name;
			}

			public List<String> getAttributes() {
				return attributes;
			}

			public List<Parameter> getParmeters() {
				return parameters;
			}

			public Type getReturns() {
				return returns;
			}

			public Expr getBody() {
				return body;
			}
		}

		public static class Procedure implements Decl {
			private final String name;
			private final List<Parameter> parameters;
			private final List<Parameter> returns;
			private final List<Expr> requires;
			private final List<Expr> ensures;
			private final List<Decl.Variable> locals;
			private final Stmt body;

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr> requires,
					List<Expr> ensures) {
				this(name, parameters, returns, requires, ensures, Collections.EMPTY_LIST, null);
			}

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr> requires,
					List<Expr> ensures, List<Decl.Variable> locals, Stmt body) {
				if (body == null && locals.size() > 0) {
					throw new IllegalArgumentException("Cannot specify local variables for procedure prototype");
				}
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = new ArrayList<>(returns);
				this.requires = new ArrayList<>(requires);
				this.ensures = new ArrayList<>(ensures);
				this.locals = locals;
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

			public List<Decl.Variable> getLocals() {
				return locals;
			}

			public Stmt getBody() {
				return body;
			}
		}

		/**
		 * an implementation declaration spells out a set of execution traces by giving
		 * a body of code.
		 *
		 * @author djp
		 *
		 */
		public static class Implementation implements Decl {
			private final String name;
			private final List<Parameter> parameters;
			private final List<Parameter> returns;
			private final List<Decl.Variable> locals;
			private final Stmt body;

			public Implementation(String name, List<Parameter> parameters, List<Parameter> returns,
					List<Decl.Variable> locals, Stmt body) {
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = new ArrayList<>(returns);
				this.locals = locals;
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

			public List<Decl.Variable> getLocals() {
				return locals;
			}

			public Stmt getBody() {
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

		public static class Sequence implements Decl {
			private final List<Decl> decls;

			public Sequence(Decl... decls) {
				this(Arrays.asList(decls));
			}

			public Sequence(Collection<Decl> decls) {
				this.decls = new ArrayList<>(decls);
			}

			public int size() {
				return decls.size();
			}

			public Decl get(int i) {
				return decls.get(i);
			}

			public List<Decl> getAll() {
				return decls;
			}
		}

		/**
		 * A type synonym is simply an abbreviation for the given type; any use of it,
		 * which syntactically looks like the use of a type constructor, is simply
		 * replaced by the right- hand side Type in which:
		 *
		 * @author djp
		 *
		 */
		public static class TypeSynonym implements Decl {
			private final String name;
			private final Type synonym;

			public TypeSynonym(String name, Type synonym) {
				this.name = name;
				this.synonym = synonym;
			}

			public String getName() {
				return name;
			}

			public Type getSynonym() {
				return synonym;
			}
		}

		public static class Variable extends Parameter implements Decl {
			private final Expr invariant;

			public Variable(String name, Type type) {
				this(name, type, null);
			}

			public Variable(String name, Type type, Expr initialiser) {
				super(name, type);
				this.invariant = initialiser;
			}

			public Expr getInvariant() {
				return invariant;
			}
		}
	};

	// =========================================================================
	// Statements
	// =========================================================================

	public interface Stmt {

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

		public static class Goto implements Stmt {
			private final List<String> labels;

			public Goto(String... labels) {
				this.labels = Arrays.asList(labels);
			}

			public int size() {
				return labels.size();
			}

			public String get(int i) {
				return labels.get(i);
			}

			public List<String> getLabels() {
				return labels;
			}
		}

		public static class Label implements Stmt {
			private final String label;

			public Label(String label) {
				this.label = label;
			}

			public String getLabel() {
				return label;
			}
		}

		public static class IfElse implements Stmt {
			private final Expr condition;
			private final Stmt trueBranch;
			private final Stmt falseBranch;

			public IfElse(Expr condition, Stmt trueBranch, Stmt falseBranch) {
				this.condition = condition;
				this.trueBranch = trueBranch;
				this.falseBranch = falseBranch;
			}

			public Expr getCondition() {
				return condition;
			}

			public Stmt getTrueBranch() {
				return trueBranch;
			}

			public Stmt getFalseBranch() {
				return falseBranch;
			}
		}

		public static class While implements Stmt {
			private final Expr condition;
			private final List<Expr> invariant;
			private final Stmt body;

			public While(Expr condition, List<Expr> invariant, Stmt body) {
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

			public Stmt getBody() {
				return body;
			}
		}

		public static class Return implements Stmt {

		}

		public static class Sequence implements Stmt {
			private final List<Stmt> stmts;

			public Sequence(Stmt... stmts) {
				this(Arrays.asList(stmts));
			}

			public Sequence(Collection<Stmt> stmts) {
				this.stmts = new ArrayList<>(stmts);
			}

			public Sequence(Collection<Stmt> stmts, Stmt stmt) {
				this.stmts = new ArrayList<>(stmts);
				this.stmts.add(stmt);
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
	}

	// =========================================================================
	// Expressions
	// =========================================================================

	public interface Expr extends Stmt {

		public static class BinaryOperator implements Expr {
			public enum Kind {
				EQ, NEQ, LT, LTEQ, GT, GTEQ, IFF, IF, ADD, SUB, MUL, IDIV, DIV, REM
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

		public static class Constant implements Expr {
			public final static Constant NULL = new Constant((String) null);
			public final static Constant TRUE = new Constant(true);
			public final static Constant FALSE = new Constant(false);

			private Object value;

			public Constant(boolean v) {
				this.value = v;
			}

			public Constant(byte[] vs) {
				this.value = vs;
			}

			public Constant(long v) {
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

		public static class DictionaryAccess implements LVal {
			private final Expr source;
			private final Expr index;

			public DictionaryAccess(Expr source, Expr index) {
				this.source = source;
				this.index = index;
			}

			public Expr getSource() {
				return source;
			}

			public Expr getIndex() {
				return index;
			}
		}

		public static class DictionaryUpdate implements LVal {
			private final Expr source;
			private final Expr index;
			private final Expr value;

			public DictionaryUpdate(Expr source, Expr index, Expr value) {
				this.source = source;
				this.index = index;
				this.value = value;
			}

			public Expr getSource() {
				return source;
			}

			public Expr getIndex() {
				return index;
			}

			public Expr getValue() {
				return value;
			}
		}

		public static class Invoke implements Expr {
			private final String name;
			private final List<Expr> arguments;

			public Invoke(String name, Expr... arguments) {
				this.name = name;
				this.arguments = Arrays.asList(arguments);
			}

			public Invoke(String name, Collection<Expr> arguments) {
				this.name = name;
				this.arguments = new ArrayList<>(arguments);
			}

			public String getName() {
				return name;
			}

			public List<Expr> getArguments() {
				return arguments;
			}
		}

		public static class UnaryOperator implements Expr {
			public enum Kind {
				NEG, NOT
			}

			private final Kind kind;
			private final Expr operand;

			public UnaryOperator(Kind kind, Expr operand) {
				this.kind = kind;
				this.operand = operand;
			}

			public Kind getKind() {
				return kind;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		public static class NaryOperator implements Expr {
			public enum Kind {
				AND, OR
			}

			private final Kind kind;
			private final List<Expr> operands;

			public NaryOperator(Kind kind, List<Expr> operands) {
				this.kind = kind;
				this.operands = operands;
			}

			public NaryOperator(Kind kind, Expr... operands) {
				this.kind = kind;
				this.operands = Arrays.asList(operands);
			}

			public Kind getKind() {
				return kind;
			}

			public List<Expr> getOperands() {
				return operands;
			}
		}

		public static class Quantifier implements Expr {
			private final boolean universal;
			private final List<Decl.Parameter> parameters;
			private final Expr body;

			public Quantifier(boolean universal, Expr body, Collection<Decl.Parameter> parameters) {
				this.universal = universal;
				this.parameters = new ArrayList<>(parameters);
				this.body = body;
			}

			public Quantifier(boolean universal, Expr body, Decl.Parameter... parameters) {
				this.universal = universal;
				this.parameters = Arrays.asList(parameters);
				this.body = body;
			}

			public boolean isUniversal() {
				return universal;
			}

			public List<Decl.Parameter> getParameters() {
				return parameters;
			}

			public Expr getBody() {
				return body;
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
		public static final Type Bool = new Type() {
		};
		public static final Type Int = new Type() {
		};
		public static final Type Real = new Type() {
		};
		public static final Type BitVector8 = new BitVector(8);

		public static class Synonym implements Type {
			private final String name;

			public Synonym(String name) {
				this.name = name;
			}

			public String getSynonym() {
				return name;
			}
		}

		public static class BitVector implements Type {
			private final int digits;

			public BitVector(int digits) {
				this.digits = digits;
			}

			public int getDigits() {
				return digits;
			}
		}

		public static class Dictionary implements Type {
			private final Type key;
			private final Type value;

			public Dictionary(Type key, Type value) {
				this.key = key;
				this.value = value;
			}

			public Type getKey() {
				return key;
			}

			public Type getValue() {
				return value;
			}
		}
	}

	// =======================================================
	// Constructor API (for convenience)
	// =======================================================

	// Declarations

	public static Decl.Function FUNCTION(String name, BoogieFile.Type parameter, BoogieFile.Type returns, String... attributes) {
		ArrayList<Decl.Parameter> parameters = new ArrayList<>();
		parameters.add(new Decl.Parameter(null, parameter));
		return new Decl.Function(Arrays.asList(attributes), name, parameters, returns, null);
	}

	public static Decl.Function FUNCTION(String name, BoogieFile.Type param1, BoogieFile.Type param2,
			BoogieFile.Type returns, String... attributes) {
		ArrayList<Decl.Parameter> parameters = new ArrayList<>();
		parameters.add(new Decl.Parameter(null, param1));
		parameters.add(new Decl.Parameter(null, param2));
		return new Decl.Function(Arrays.asList(attributes), name, parameters, returns, null);
	}

	public static Decl.Function FUNCTION(String name, List<Decl.Parameter> parameters,
			BoogieFile.Type returns) {
		return new Decl.Function(Collections.EMPTY_LIST,name,parameters,returns,null);
	}

	public static Decl.Function FUNCTION(String name, List<Decl.Parameter> parameters,
			BoogieFile.Type returns, Expr body) {
		return new Decl.Function(Collections.EMPTY_LIST,name,parameters,returns,body);
	}

	// Logical Operators

	public static Expr AND(List<Expr> operands) {
		if (operands.size() == 0) {
			return new Expr.Constant(true);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, operands);
		}
	}

	public static Expr AND(Expr... operands) {
		if (operands.length == 0) {
			return new Expr.Constant(true);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.AND, operands);
		}
	}

	public static Expr.Quantifier FORALL(String name, BoogieFile.Type type, Expr body) {
		return new Expr.Quantifier(true, body, new Decl.Parameter(name, type));
	}

	public static Expr.Quantifier FORALL(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,
			Expr body) {
		return new Expr.Quantifier(true, body, new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2));
	}

	public static Expr.Quantifier FORALL(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,
			String name3, BoogieFile.Type type3, Expr body) {
		return new Expr.Quantifier(true, body, new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2),
				new Decl.Parameter(name3, type3));
	}

	public static Expr.Quantifier FORALL(List<Decl.Parameter> parameters, Expr body) {
		return new Expr.Quantifier(true, body, parameters);
	}

	public static Expr.BinaryOperator IFF(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.IFF, lhs, rhs);
	}

	public static Expr.BinaryOperator IMPLIES(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.IF, lhs, rhs);
	}

	public static Expr.UnaryOperator NOT(Expr lhs) {
		// FIXME: could apply some simplification here.
		return new Expr.UnaryOperator(Expr.UnaryOperator.Kind.NOT, lhs);
	}

	public static Expr OR(List<Expr> operands) {
		if (operands.size() == 0) {
			return new Expr.Constant(false);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.OR, operands);
		}
	}

	public static Expr OR(Expr... operands) {
		if (operands.length == 0) {
			return new Expr.Constant(false);
		} else {
			return new Expr.NaryOperator(Expr.NaryOperator.Kind.OR, operands);
		}
	}

	// Relational Operators

	public static Expr.BinaryOperator EQ(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.EQ, lhs, rhs);
	}

	public static Expr.BinaryOperator NEQ(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.NEQ, lhs, rhs);
	}

	public static Expr.BinaryOperator GTEQ(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.GTEQ, lhs, rhs);
	}

	public static Expr.BinaryOperator GT(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.GT, lhs, rhs);
	}

	public static Expr.BinaryOperator LTEQ(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LTEQ, lhs, rhs);
	}

	public static Expr.BinaryOperator LT(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.LT, lhs, rhs);
	}

	// Arithmetic Operators
	public static Expr.BinaryOperator ADD(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.ADD, lhs, rhs);
	}

	public static Expr.UnaryOperator NEG(Expr lhs) {
		return new Expr.UnaryOperator(Expr.UnaryOperator.Kind.NEG, lhs);
	}

	public static Expr.BinaryOperator SUB(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.SUB, lhs, rhs);
	}

	public static Expr.BinaryOperator MUL(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.MUL, lhs, rhs);
	}

	public static Expr.BinaryOperator DIV(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.DIV, lhs, rhs);
	}

	public static Expr.BinaryOperator IDIV(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.IDIV, lhs, rhs);
	}

	public static Expr.BinaryOperator REM(Expr lhs, Expr rhs) {
		return new Expr.BinaryOperator(Expr.BinaryOperator.Kind.REM, lhs, rhs);
	}
	// Dictionaries

	public static Expr.DictionaryAccess GET(Expr src, Expr index) {
		return new Expr.DictionaryAccess(src, index);
	}

	public static Expr.DictionaryUpdate PUT(Expr src, Expr index, Expr value) {
		return new Expr.DictionaryUpdate(src, index, value);
	}

	// Misc
	public static Expr.Constant CONST(boolean b) {
		return new Expr.Constant(b);
	}

	public static Expr.Constant CONST(int i) {
		return new Expr.Constant(i);
	}

	public static Expr.Constant CONST(BigInteger i) {
		return new Expr.Constant(i);
	}

	public static Expr.Invoke CALL(String name, Expr... parameters) {
		return new Expr.Invoke(name, parameters);
	}

	public static Expr.Invoke CALL(String name, List<Expr> parameters) {
		return new Expr.Invoke(name, parameters);
	}

	public static Expr.VariableAccess VAR(String name) {
		return new Expr.VariableAccess(name);
	}
}
