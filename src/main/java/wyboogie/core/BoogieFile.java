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
				this.attributes = new ArrayList<>(attributes);
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
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
			private final List<Expr.Logical> requires;
			private final List<Expr.Logical> ensures;
			private final List<String> modifies;
			private final List<Decl.Variable> locals;
			private final Stmt body;

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr.Logical> requires,
					List<Expr.Logical> ensures, List<String> modifies) {
				this(name, parameters, returns, requires, ensures, Collections.EMPTY_LIST, modifies, null);
			}

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr.Logical> requires,
					List<Expr.Logical> ensures, List<Decl.Variable> locals, List<String> modifies, Stmt body) {
				if (body == null && locals.size() > 0) {
					throw new IllegalArgumentException("Cannot specify local variables for procedure prototype");
				}
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = new ArrayList<>(returns);
				this.requires = new ArrayList<>(requires);
				this.ensures = new ArrayList<>(ensures);
				this.modifies = new ArrayList<>(modifies);
				this.locals = new ArrayList<>(locals);
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

			public List<Expr.Logical> getRequires() {
				return requires;
			}

			public List<Expr.Logical> getEnsures() {
				return ensures;
			}

			public List<String> getModifies() {
				return modifies;
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
				this.locals = new ArrayList<>(locals);
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
			private final Expr.Logical condition;

			public Assert(Expr.Logical condition) {
				this.condition = condition;
			}

			public Expr.Logical getCondition() {
				return condition;
			}
		}

		public static class Assume implements Stmt {
			private final Expr.Logical condition;

			public Assume(Expr.Logical condition) {
				this.condition = condition;
			}

			public Expr.Logical getCondition() {
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

		public static class Call implements Stmt {
			private final String name;
			private final List<LVal> lvals;
			private final List<Expr> arguments;

			public Call(String name, List<LVal> lvals, Collection<Expr> arguments) {
				this.name = name;
				this.lvals = lvals;
				this.arguments = new ArrayList<>(arguments);
			}

			public String getName() {
				return name;
			}

			public List<LVal> getLVals() {
				return lvals;
			}

			public List<Expr> getArguments() {
				return arguments;
			}
		}

		public static class Goto implements Stmt {
			private final List<String> labels;

			public Goto(Collection<String> labels) {
				this.labels = new ArrayList<>(labels);
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
			private final List<Expr.Logical> invariant;
			private final Stmt body;

			public While(Expr condition, List<Expr.Logical> invariant, Stmt body) {
				this.condition = condition;
				this.invariant = new ArrayList<>(invariant);
				this.body = body;
			}

			public Expr getCondition() {
				return condition;
			}

			public List<Expr.Logical> getInvariant() {
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

			private Sequence(Collection<Stmt> stmts) {
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

	public interface Expr {

		public interface Logical extends Expr {

		}

		public interface Quantifier extends Logical {
			public List<Decl.Parameter> getParameters();

			public Expr.Logical getBody();
		}

		public interface UnaryOperator {
			Expr getOperand();
		}

		public interface BinaryOperator {
			Expr getLeftHandSide();
			Expr getRightHandSide();
		}

		public interface NaryOperator {
			List<? extends Expr> getOperands();
		}

		public static class Equals implements Logical, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private Equals(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class NotEquals implements Logical, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private NotEquals(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class LessThan implements Logical, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private LessThan(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class LessThanOrEqual implements Logical, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private LessThanOrEqual(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class GreaterThan implements Logical, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private GreaterThan(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class GreaterThanOrEqual implements Logical, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private GreaterThanOrEqual(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class Iff implements Logical, BinaryOperator {
			private final Logical lhs;
			private final Logical rhs;

			private Iff(Logical lhs, Logical rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Logical getLeftHandSide() {
				return lhs;
			}

			public Logical getRightHandSide() {
				return rhs;
			}
		}

		public static class Implies implements Logical, BinaryOperator {
			private final Logical lhs;
			private final Logical rhs;

			private Implies(Logical lhs, Logical rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Logical getLeftHandSide() {
				return lhs;
			}

			public Logical getRightHandSide() {
				return rhs;
			}
		}

		public static class Addition implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private Addition(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class Subtraction implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private  Subtraction(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class Multiplication implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private Multiplication(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class Division implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			public Division(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class IntegerDivision implements Expr, BinaryOperator {
			private Expr lhs;
			private Expr rhs;

			public IntegerDivision(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class Remainder implements Expr, BinaryOperator {
			private Expr lhs;
			private Expr rhs;

			private Remainder(Expr lhs, Expr rhs) {
				this.lhs = lhs;
				this.rhs = rhs;
			}

			public Expr getLeftHandSide() {
				return lhs;
			}

			public Expr getRightHandSide() {
				return rhs;
			}
		}

		public static class Boolean implements Logical {
			public final static Boolean TRUE = new Boolean(true);
			public final static Boolean FALSE = new Boolean(false);

			private final boolean value;

			private Boolean(boolean v) {
				this.value = v;
			}

			public boolean getValue() {
				return value;
			}
		}

		public static class Integer implements Expr {
			private final BigInteger value;

			private Integer(BigInteger v) {
				this.value = v;
			}

			public BigInteger getValue() {
				return value;
			}
		}

		public static class Bytes implements Expr {
			private final byte[] value;

			private Bytes(byte[] v) {
				this.value = v;
			}

			public byte[] getValue() {
				return value;
			}
		}

		public static class DictionaryAccess implements LVal {
			private final Expr source;
			private final Expr index;

			private DictionaryAccess(Expr source, Expr index) {
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

			private DictionaryUpdate(Expr source, Expr index, Expr value) {
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

		public static class Invoke implements Logical {
			private final String name;
			private final List<Expr> arguments;

			private Invoke(String name, Collection<Expr> arguments) {
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

		public static class Negation implements Expr, UnaryOperator {
			private final Expr operand;

			private Negation(Expr operand) {
				this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		public static class Old implements Expr, UnaryOperator {
			private final Expr operand;

			private Old(Expr operand) {
				this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		public static class LogicalNot implements Logical, UnaryOperator {
			private final Logical operand;

			private LogicalNot(Logical operand) {
				this.operand = operand;
			}

			public Logical getOperand() {
				return operand;
			}
		}

		public static class LogicalAnd implements Logical, NaryOperator {
			private final List<Logical> operands;

			private LogicalAnd(List<Logical> operands) {
				this.operands = new ArrayList<>(operands);
			}

			public List<Logical> getOperands() {
				return operands;
			}
		}

		public static class LogicalOr implements Logical, NaryOperator {
			private final List<Logical> operands;

			private LogicalOr(List<Logical> operands) {
				this.operands = new ArrayList<>(operands);
			}

			public List<Logical> getOperands() {
				return operands;
			}
		}

		public static class UniversalQuantifier implements Quantifier {
			private final List<Decl.Parameter> parameters;
			private final Logical body;

			private UniversalQuantifier(Collection<Decl.Parameter> parameters, Expr.Logical body) {
				this.parameters = new ArrayList<>(parameters);
				this.body = body;
			}

			public List<Decl.Parameter> getParameters() {
				return parameters;
			}

			public Logical getBody() {
				return body;
			}
		}

		public static class ExistentialQuantifier implements Quantifier {
			private final List<Decl.Parameter> parameters;
			private final Logical body;

			private ExistentialQuantifier(Collection<Decl.Parameter> parameters, Expr.Logical body) {
				this.parameters = new ArrayList<>(parameters);
				this.body = body;
			}

			public List<Decl.Parameter> getParameters() {
				return parameters;
			}

			public Logical getBody() {
				return body;
			}
		}

		public static class VariableAccess implements LVal, Logical {
			private final String variable;

			private VariableAccess(String var) {
				if(var == null) {
					throw new IllegalArgumentException();
				}
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

	public static Decl.Function FUNCTION(String name, Decl.Parameter parameter, BoogieFile.Type returns, Expr body) {
		ArrayList<Decl.Parameter> parameters = new ArrayList<>();
		parameters.add(parameter);
		return new Decl.Function(Collections.EMPTY_LIST, name, parameters, returns, body);
	}

	public static Decl.Function FUNCTION(String name, BoogieFile.Type param1, BoogieFile.Type param2,
			BoogieFile.Type returns, String... attributes) {
		ArrayList<Decl.Parameter> parameters = new ArrayList<>();
		parameters.add(new Decl.Parameter(null, param1));
		parameters.add(new Decl.Parameter(null, param2));
		return new Decl.Function(Arrays.asList(attributes), name, parameters, returns, null);
	}

	public static Decl.Function FUNCTION(String name, BoogieFile.Type param1, BoogieFile.Type param2, BoogieFile.Type param3,
										 BoogieFile.Type returns, String... attributes) {
		ArrayList<Decl.Parameter> parameters = new ArrayList<>();
		parameters.add(new Decl.Parameter(null, param1));
		parameters.add(new Decl.Parameter(null, param2));
		parameters.add(new Decl.Parameter(null, param3));
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

	public static Decl.Procedure PROCEDURE(String name, List<Decl.Parameter> parameters, List<Decl.Parameter> returns) {
		return new Decl.Procedure(name, parameters, returns, Collections.EMPTY_LIST, Collections.EMPTY_LIST, Collections.EMPTY_LIST);
	}

	public static Decl.Procedure PROCEDURE(String name, List<Decl.Parameter> parameters, List<Decl.Parameter> returns, List<Expr.Logical> requires, List<Expr.Logical> ensures) {
		return new Decl.Procedure(name, parameters, returns, requires, ensures, Collections.EMPTY_LIST);
	}

	public static Stmt ASSIGN(LVal lhs, Expr rhs) {
		return new Stmt.Assignment(lhs,rhs);
	}

	public static Stmt GOTO(List<String> labels) {
		return new Stmt.Goto(labels);
	}

	public static Stmt GOTO(String... labels) {
		return new Stmt.Goto(Arrays.asList(labels));
	}

	public static Stmt SEQUENCE(List<Stmt> stmts) {
		return new Stmt.Sequence(stmts);
	}

	public static Stmt SEQUENCE(List<Stmt> stmts, Stmt stmt) {
		ArrayList<Stmt> ss = new ArrayList<>(stmts);
		ss.add(stmt);
		return new Stmt.Sequence(ss);
	}

	public static Stmt SEQUENCE(Stmt... stmts) {
		return new Stmt.Sequence(Arrays.asList(stmts));
	}

	// Logical Operators

	public static Expr.Logical AND(List<Expr.Logical> operands) {
		if (operands.contains(Expr.Boolean.FALSE)) {
			return Expr.Boolean.FALSE;
		} else {
			operands = removeAll(Expr.Boolean.TRUE, operands);
			switch (operands.size()) {
				case 0:
					return Expr.Boolean.TRUE;
				case 1:
					return operands.get(0);
				default:
					return new Expr.LogicalAnd(operands);
			}
		}
	}

	public static Expr.Logical AND(Expr.Logical... operands) {
		return AND(Arrays.asList(operands));
	}

	public static Expr.UniversalQuantifier FORALL(String name, BoogieFile.Type type, Expr.Logical body) {
		return new Expr.UniversalQuantifier(Arrays.asList(new Decl.Parameter(name, type)),body);
	}

	public static Expr.UniversalQuantifier FORALL(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,
												  Expr.Logical body) {
		return new Expr.UniversalQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2)), body);
	}

	public static Expr.UniversalQuantifier FORALL(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,String name3, BoogieFile.Type type3,
												  Expr.Logical body) {
		return new Expr.UniversalQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2), new Decl.Parameter(name3, type3)), body);
	}

	public static Expr.UniversalQuantifier FORALL(List<Decl.Parameter> parameters, Expr.Logical body) {
		return new Expr.UniversalQuantifier(parameters, body);
	}


	public static Expr.ExistentialQuantifier EXISTS(String name, BoogieFile.Type type, Expr.Logical body) {
		return new Expr.ExistentialQuantifier(Arrays.asList(new Decl.Parameter(name, type)),body);
	}

	public static Expr.ExistentialQuantifier EXISTS(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,
												  Expr.Logical body) {
		return new Expr.ExistentialQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2)), body);
	}

	public static Expr.ExistentialQuantifier EXISTS(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,String name3, BoogieFile.Type type3,
												  Expr.Logical body) {
		return new Expr.ExistentialQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2), new Decl.Parameter(name3, type3)), body);
	}

	public static Expr.ExistentialQuantifier EXISTS(List<Decl.Parameter> parameters, Expr.Logical body) {
		return new Expr.ExistentialQuantifier(parameters, body);
	}


	public static Expr.Logical IFF(Expr.Logical lhs, Expr.Logical rhs) {
		if(lhs instanceof Expr.Boolean && rhs instanceof Expr.Boolean) {
			return (lhs == rhs) ? Expr.Boolean.TRUE : Expr.Boolean.FALSE;
		} else {
			return new Expr.Iff(lhs, rhs);
		}
	}

	public static Expr.Logical IMPLIES(Expr.Logical lhs, Expr.Logical rhs) {
		if(lhs == Expr.Boolean.FALSE || rhs == Expr.Boolean.TRUE) {
			return Expr.Boolean.TRUE;
		} else if(lhs == Expr.Boolean.TRUE) {
			return rhs;
		} else if(rhs == Expr.Boolean.FALSE) {
			return lhs;
		} else {
			return new Expr.Implies(lhs, rhs);
		}
	}

	public static Expr.LogicalNot NOT(Expr.Logical lhs) {
		// FIXME: could apply some simplification here.
		return new Expr.LogicalNot(lhs);
	}

	public static Expr.Logical OR(List<Expr.Logical> operands) {
		if (operands.contains(Expr.Boolean.TRUE)) {
			return Expr.Boolean.TRUE;
		} else {
			operands = removeAll(Expr.Boolean.FALSE, operands);
			switch (operands.size()) {
				case 0:
					return Expr.Boolean.FALSE;
				case 1:
					return operands.get(0);
				default:
					return new Expr.LogicalOr(operands);
			}
		}
	}

	public static Expr.Logical OR(Expr.Logical... operands) {
		return OR(Arrays.asList(operands));
	}

	// Relational Operators

	public static Expr.Equals EQ(Expr lhs, Expr rhs) {
		return new Expr.Equals(lhs, rhs);
	}

	public static Expr.NotEquals NEQ(Expr lhs, Expr rhs) {
		return new Expr.NotEquals(lhs, rhs);
	}

	public static Expr.GreaterThanOrEqual GTEQ(Expr lhs, Expr rhs) {
		return new Expr.GreaterThanOrEqual(lhs, rhs);
	}

	public static Expr.GreaterThan GT(Expr lhs, Expr rhs) {
		return new Expr.GreaterThan(lhs, rhs);
	}

	public static Expr.LessThanOrEqual LTEQ(Expr lhs, Expr rhs) {
		return new Expr.LessThanOrEqual(lhs, rhs);
	}

	public static Expr.LessThan LT(Expr lhs, Expr rhs) {
		return new Expr.LessThan(lhs, rhs);
	}

	// Arithmetic Operators
	public static Expr.Addition ADD(Expr lhs, Expr rhs) {
		return new Expr.Addition(lhs, rhs);
	}

	public static Expr.Negation NEG(Expr lhs) {
		return new Expr.Negation(lhs);
	}

	public static Expr.Subtraction SUB(Expr lhs, Expr rhs) {
		return new Expr.Subtraction(lhs, rhs);
	}

	public static Expr.Multiplication MUL(Expr lhs, Expr rhs) {
		return new Expr.Multiplication(lhs, rhs);
	}

	public static Expr.Division DIV(Expr lhs, Expr rhs) {
		return new Expr.Division(lhs, rhs);
	}

	public static Expr.IntegerDivision IDIV(Expr lhs, Expr rhs) {
		return new Expr.IntegerDivision(lhs, rhs);
	}

	public static Expr.Remainder REM(Expr lhs, Expr rhs) {
		return new Expr.Remainder(lhs, rhs);
	}
	// Dictionaries

	public static Expr.DictionaryAccess GET(Expr src, Expr index) {
		return new Expr.DictionaryAccess(src, index);
	}

	public static Expr.DictionaryUpdate PUT(Expr src, Expr index, Expr value) {
		return new Expr.DictionaryUpdate(src, index, value);
	}

	// Misc
	public static Expr.Logical CONST(boolean b) {
		return new Expr.Boolean(b);
	}

	public static Expr.Integer CONST(int i) {
		return new Expr.Integer(BigInteger.valueOf(i));
	}

	public static Expr.Integer CONST(BigInteger i) {
		return new Expr.Integer(i);
	}

	public static Expr.Bytes CONST(byte[] bytes) {
		return new Expr.Bytes(bytes);
	}

	public static Expr.Old OLD(Expr lhs) {
		return new Expr.Old(lhs);
	}
	public static Stmt.Call CALL(String name, Expr... parameters) {
		return new Stmt.Call(name, Collections.EMPTY_LIST, Arrays.asList(parameters));
	}
	public static Stmt.Call CALL(String name, List<Expr> parameters) {
		return new Stmt.Call(name, Collections.EMPTY_LIST, parameters);
	}
	public static Stmt.Call CALL(String name, LVal lhs, Expr... parameters) {
		return new Stmt.Call(name, Arrays.asList(lhs), Arrays.asList(parameters));
	}
	public static Stmt.Call CALL(String name, LVal lhs, List<Expr> parameters) {
		return new Stmt.Call(name, Arrays.asList(lhs), parameters);
	}
	public static Stmt.Call CALL(String name, List<LVal> lvals, Expr... parameters) {
		return new Stmt.Call(name, lvals, Arrays.asList(parameters));
	}
	public static Stmt.Call CALL(String name, List<LVal> lvals, List<Expr> parameters) {
		return new Stmt.Call(name, lvals, parameters);
	}
	public static Expr.Invoke INVOKE(String name, Expr... parameters) {
		return new Expr.Invoke(name, Arrays.asList(parameters));
	}

	public static Expr.Invoke INVOKE(String name, List<Expr> parameters) {
		return new Expr.Invoke(name, parameters);
	}

	public static Expr.VariableAccess VAR(String name) {
		return new Expr.VariableAccess(name);
	}

	private static <T extends Expr> List<T> removeAll(T item, List<T> items) {
		for(int i=0;i!=items.size();++i) {
			if(items.get(i).equals(item)) {
				ArrayList<T> nitems = new ArrayList<>();
				for(int j=0;j!=items.size();++j) {
					T jth = items.get(j);
					if(!jth.equals(item)) {
						nitems.add(jth);
					}
				}
				return nitems;
			}
		}
		// Nothing removed
		return items;
	}
}
