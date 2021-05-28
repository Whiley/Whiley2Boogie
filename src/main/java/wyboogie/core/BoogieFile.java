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

	// =========================================================================
	// Top-Level Item
	// =========================================================================

	public interface Item {
		/**
		 * Get a particular attribute associated with this item.
		 * @param kind
		 * @param <T>
		 * @return
		 */
		public <T> T getAttribute(Class<T> kind);

		/**
		 * Get all attributes within this item.
		 * @return
		 */
		public Attribute[] getAttributes();
	}

	public static class AbstractItem implements Item {
		private final Attribute[] attributes;

		public AbstractItem(Attribute[] attributes) {
			this.attributes = attributes;
		}

		@Override
		public <T> T getAttribute(Class<T> kind) {
			for(int i=0;i!=attributes.length;++i) {
				T ith = attributes[i].as(kind);
				if(ith != null) {
					return ith;
				}
			}
			return null;
		}

		public Attribute[] getAttributes() {
			return attributes;
		}

		public boolean isFalse() {
			return (this instanceof Expr.Boolean) && !((Expr.Boolean) this).getValue();
		}

		public boolean isTrue() {
			return (this instanceof Expr.Boolean) && ((Expr.Boolean) this).getValue();
		}
	}

	// =========================================================================
	// Declarations
	// =========================================================================

	public interface Decl extends Item {

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
		public static class Axiom extends AbstractItem implements Decl {
			private final Expr operand;

			public Axiom(Expr operand, Attribute... attributes) {
				super(attributes);
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
		public static class LineComment extends AbstractItem implements Decl {
			private final String message;

			public LineComment(String message, Attribute... attributes) {
				super(attributes);
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
			public Constant(String name, Type type, Attribute... attributes) {
				super(name, type, attributes);
				this.unique = false;
			}

			/**
			 * Construct a constant which maybe unique.
			 *
			 * @param unique Flag to indicate whether constant is unique.
			 * @param name   Name of constant.
			 * @param type   Type of constant.
			 */
			public Constant(boolean unique, String name, Type type, Attribute... attributes) {
				super(name, type, attributes);
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

		public static class Function extends AbstractItem implements Decl {
			private final String name;
			private final List<String> modifiers;
			private final List<Parameter> parameters;
			private final Type returns;
			private final Expr body;

			public Function(List<String> modifiers, String name, List<Parameter> parameters, Type returns, Expr body, Attribute... attributes) {
				super(attributes);
				this.modifiers = new ArrayList<>(modifiers);
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = returns;
				this.body = body;
			}

			public String getName() {
				return name;
			}

			public List<String> getModifiers() {
				return modifiers;
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

		public static class Procedure extends AbstractItem implements Decl {
			private final String name;
			private final List<Parameter> parameters;
			private final List<Parameter> returns;
			private final List<Expr.Logical> requires;
			private final List<Expr.Logical> freeRequires;
			private final List<Expr.Logical> ensures;
			private final List<Expr.Logical> freeEnsures;
			private final List<String> modifies;
			private final List<Decl.Variable> locals;
			private final Stmt body;

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr.Logical> requires,
					List<Expr.Logical> ensures, List<String> modifies, Attribute... attributes) {
				this(name, parameters, returns, requires, ensures, Collections.EMPTY_LIST, modifies, null, attributes);
			}

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr.Logical> requires,
							 List<Expr.Logical> ensures, List<Decl.Variable> locals, List<String> modifies, Stmt body, Attribute... attributes) {
				this(name, parameters, returns, requires, ensures, Collections.EMPTY_LIST, Collections.EMPTY_LIST, locals, modifies, body, attributes);
			}

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, List<Expr.Logical> requires,
					List<Expr.Logical> ensures, List<Expr.Logical> freeRequires, List<Expr.Logical> freeEnsures, List<Decl.Variable> locals, List<String> modifies, Stmt body, Attribute... attributes) {
				super(attributes);
				if (body == null && locals.size() > 0) {
					throw new IllegalArgumentException("Cannot specify local variables for procedure prototype");
				}
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = new ArrayList<>(returns);
				this.requires = new ArrayList<>(requires);
				this.ensures = new ArrayList<>(ensures);
				this.freeRequires = new ArrayList<>(freeRequires);
				this.freeEnsures = new ArrayList<>(freeEnsures);
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

			public List<Expr.Logical> getFreeRequires() {
				return freeRequires;
			}

			public List<Expr.Logical> getFreeEnsures() {
				return freeEnsures;
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
		public static class Implementation extends AbstractItem implements Decl {
			private final String name;
			private final List<Parameter> parameters;
			private final List<Parameter> returns;
			private final List<Decl.Variable> locals;
			private final Stmt body;

			public Implementation(String name, List<Parameter> parameters, List<Parameter> returns,
					List<Decl.Variable> locals, Stmt body, Attribute... attributes) {
				super(attributes);
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

		public static class Parameter extends AbstractItem implements Item {
			private final String name;
			private final Type type;

			public Parameter(String name, Type type, Attribute... attributes) {
				super(attributes);
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

		public static class Sequence extends AbstractItem implements Decl {
			private final List<Decl> decls;

			public Sequence(Decl... decls) {
				this(Arrays.asList(decls));
			}

			public Sequence(Collection<Decl> decls, Attribute... attributes) {
				super(attributes);
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
		public static class TypeSynonym extends AbstractItem implements Decl {
			private final String name;
			private final Type synonym;

			public TypeSynonym(String name, Type synonym, Attribute... attributes) {
				super(attributes);
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

			public Variable(String name, Type type, Expr initialiser, Attribute... attributes) {
				super(name, type, attributes);
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

	public interface Stmt extends Item {

		public static class Assert extends AbstractItem implements Stmt {
			private final Expr.Logical condition;

			private Assert(Expr.Logical condition, Attribute[] attributes) {
				super(attributes);
				this.condition = condition;
			}

			public Expr.Logical getCondition() {
				return condition;
			}
		}

		public static class Assume extends AbstractItem implements Stmt {
			private final Expr.Logical condition;

			private Assume(Expr.Logical condition, Attribute[] attributes) {
				super(attributes);
				this.condition = condition;
			}

			public Expr.Logical getCondition() {
				return condition;
			}
		}

		public static class Assignment extends AbstractItem implements Stmt {
			private final LVal lhs;
			private final Expr rhs;

			private Assignment(LVal lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Call extends AbstractItem implements Stmt {
			private final String name;
			private final List<LVal> lvals;
			private final List<Expr> arguments;

			private Call(String name, List<LVal> lvals, Collection<Expr> arguments, Attribute[] attributes) {
				super(attributes);
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

		public static class Goto extends AbstractItem implements Stmt {
			private final List<String> labels;

			private Goto(Collection<String> labels, Attribute[] attributes) {
				super(attributes);this.labels = new ArrayList<>(labels);
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

		public static class Label extends AbstractItem implements Stmt {
			private final String label;

			private Label(String label, Attribute[] attributes) {
				super(attributes);this.label = label;
			}

			public String getLabel() {
				return label;
			}
		}

		public static class IfElse extends AbstractItem implements Stmt {
			private final Expr condition;
			private final Stmt trueBranch;
			private final Stmt falseBranch;

			private IfElse(Expr condition, Stmt trueBranch, Stmt falseBranch, Attribute... attributes) {
				super(attributes);
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

		public static class While extends AbstractItem implements Stmt {
			private final Expr condition;
			private final List<Expr.Logical> invariant;
			private final Stmt body;

			private While(Expr condition, List<Expr.Logical> invariant, Stmt body, Attribute... attributes) {
				super(attributes);
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

		public static class Return extends AbstractItem implements Stmt {
			private Return(Attribute... attributes) {
				super(attributes);
			}
		}

		public static class Sequence extends AbstractItem implements Stmt {
			private final List<Stmt> stmts;

			private Sequence(Collection<Stmt> stmts, Attribute[] attributes) {
				super(attributes); this.stmts = new ArrayList<>(stmts);
			}

			public Sequence(Collection<Stmt> stmts, Stmt stmt, Attribute[] attributes) {
				super(attributes);
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

	public interface Expr extends Item {

		public interface Logical extends Expr {
			public boolean isFalse();
			public boolean isTrue();
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

		public static class Equals extends AbstractItem implements Logical,  BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private Equals(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class NotEquals extends AbstractItem implements Logical,  BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private NotEquals(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class LessThan extends AbstractItem implements Logical,  BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private LessThan(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class LessThanOrEqual extends AbstractItem implements Logical,  BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private LessThanOrEqual(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class GreaterThan extends AbstractItem implements Logical,  BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private GreaterThan(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class GreaterThanOrEqual extends AbstractItem implements Logical,  BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private GreaterThanOrEqual(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Iff extends AbstractItem implements Logical,  BinaryOperator {
			private final Logical lhs;
			private final Logical rhs;

			private Iff(Logical lhs, Logical rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Implies extends AbstractItem implements Logical,  BinaryOperator {
			private final Logical lhs;
			private final Logical rhs;

			private Implies(Logical lhs, Logical rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Addition extends AbstractItem implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private Addition(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Subtraction extends AbstractItem implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private  Subtraction(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Multiplication extends AbstractItem implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			private Multiplication(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Division extends AbstractItem implements Expr, BinaryOperator {
			private final Expr lhs;
			private final Expr rhs;

			public Division(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class IntegerDivision extends AbstractItem implements Expr, BinaryOperator {
			private Expr lhs;
			private Expr rhs;

			public IntegerDivision(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Remainder extends AbstractItem implements Expr, BinaryOperator {
			private Expr lhs;
			private Expr rhs;

			private Remainder(Expr lhs, Expr rhs, Attribute[] attributes) {
				super(attributes);
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

		public static class Boolean extends AbstractItem implements Logical {
			private final boolean value;

			private Boolean(boolean v, Attribute[] attributes) {
				super(attributes);
				this.value = v;
			}

			public boolean getValue() {
				return value;
			}
		}

		public static class Integer extends AbstractItem implements Expr {
			private final BigInteger value;

			private Integer(BigInteger v, Attribute[] attributes) {
				super(attributes);this.value = v;
			}

			public BigInteger getValue() {
				return value;
			}

			public String toString() {
				return "INT(" + value + ")";
			}
		}

		public static class Bytes extends AbstractItem implements Expr {
			private final byte[] value;

			private Bytes(byte[] v, Attribute[] attributes) {
				super(attributes);
				this.value = v;
			}

			public byte[] getValue() {
				return value;
			}
		}

		public static class DictionaryAccess extends AbstractItem implements LVal {
			private final Expr source;
			private final Expr index;

			private DictionaryAccess(Expr source, Expr index, Attribute[] attributes) {
				super(attributes);
				this.source = source;
				this.index = index;
			}

			public Expr getSource() {
				return source;
			}

			public Expr getIndex() {
				return index;
			}

			public String toString() {
				return "GET(" + source + ", " + index + ")";
			}
		}

		public static class DictionaryUpdate extends AbstractItem implements LVal {
			private final Expr source;
			private final Expr index;
			private final Expr value;

			private DictionaryUpdate(Expr source, Expr index, Expr value, Attribute[] attributes) {
				super(attributes);
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

			public String toString() {
				return "PUT(" + source + ", " + index + "," + value + ")";
			}
		}

		public static class Invoke extends AbstractItem implements Logical {
			private final String name;
			private final List<Expr> arguments;

			private Invoke(String name, Collection<Expr> arguments, Attribute[] attributes) {
				super(attributes);
				this.name = name;
				this.arguments = new ArrayList<>(arguments);
			}

			public String getName() {
				return name;
			}

			public List<Expr> getArguments() {
				return arguments;
			}

			public String toString() {
				return "FNCALL(" + name + "," + arguments.toString() + ")";
			}
		}

		public static class Negation extends AbstractItem implements Expr, UnaryOperator {
			private final Expr operand;

			private Negation(Expr operand, Attribute[] attributes) {
				super(attributes);this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		public static class Old extends AbstractItem implements Expr, UnaryOperator {
			private final Expr operand;

			private Old(Expr operand, Attribute[] attributes) {
				super(attributes);
				this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}

			public String toString() {
				return "OLD(" + operand + ")";
			}
		}

		public static class LogicalNot extends AbstractItem implements Logical,  UnaryOperator {
			private final Logical operand;

			private LogicalNot(Logical operand, Attribute[] attributes) {
				super(attributes); this.operand = operand;
			}

			public Logical getOperand() {
				return operand;
			}

			public String toString() {
				return "NOT(" + operand + ")";
			}
		}

		public static class LogicalAnd extends AbstractItem implements Logical,  NaryOperator {
			private final List<Logical> operands;

			private LogicalAnd(List<Logical> operands, Attribute[] attributes) {
				super(attributes);
				this.operands = new ArrayList<>(operands);
			}

			public List<Logical> getOperands() {
				return operands;
			}
		}

		public static class LogicalOr extends AbstractItem implements Logical,  NaryOperator {
			private final List<Logical> operands;

			private LogicalOr(List<Logical> operands, Attribute[] attributes) {
				super(attributes);
				this.operands = new ArrayList<>(operands);
			}

			public List<Logical> getOperands() {
				return operands;
			}
		}

		public static class UniversalQuantifier extends AbstractItem implements Logical,  Quantifier {
			private final List<Decl.Parameter> parameters;
			private final Logical body;

			private UniversalQuantifier(Collection<Decl.Parameter> parameters, Expr.Logical body, Attribute[] attributes) {
				super(attributes);
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

		public static class ExistentialQuantifier extends AbstractItem implements Logical,  Quantifier {
			private final List<Decl.Parameter> parameters;
			private final Logical body;

			private ExistentialQuantifier(Collection<Decl.Parameter> parameters, Expr.Logical body, Attribute[] attributes) {
				super(attributes);
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

		public static class VariableAccess extends AbstractItem implements Logical,  LVal {
			private final String variable;

			private VariableAccess(String var, Attribute[] attributes) {
				super(attributes);
				if(var == null) {
					throw new IllegalArgumentException();
				}
				this.variable = var;
			}

			public String getVariable() {
				return variable;
			}

			public String toString() {
				return "VAR(" + variable + ")";
			}
		}
	}

	public interface LVal extends Expr {

	}

	// =========================================================================
	// Types
	// =========================================================================

	public interface Type extends Item {
		public static final Type Bool = new Bool();
		public static final Type Int = new Int();
		public static final Type Real = new Real();
		public static final Type BitVector8 = new BitVector(8);

		public static class Bool extends AbstractItem implements Type {
			public Bool(Attribute... attributes) {
				super(attributes);
			}
		}

		public static class Int extends AbstractItem  implements Type {
			public Int(Attribute... attributes) {
				super(attributes);
			}
		}

		public static class Real extends AbstractItem  implements Type {
			public Real(Attribute... attributes) {
				super(attributes);
			}
		}

		public static class Synonym extends AbstractItem implements Type {
			private final String name;

			public Synonym(String name, Attribute... attributes) {
				super(attributes); this.name = name;
			}

			public String getSynonym() {
				return name;
			}
		}

		public static class BitVector extends AbstractItem implements Type {
			private final int digits;

			public BitVector(int digits, Attribute... attributes) {
				super(attributes); this.digits = digits;
			}

			public int getDigits() {
				return digits;
			}
		}

		public static class Dictionary extends AbstractItem implements Type {
			private final Type key;
			private final Type value;

			public Dictionary(Type key, Type value, Attribute... attributes) {
				super(attributes);
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

	// =========================================================================
	// Attributes
	// =========================================================================

	public interface Attribute {
		/**
		 * Get the contents of this attribute as a given kind.  If that doesn't match, then return <code>null</code>.
		 * @param kind
		 * @param <T>
		 * @return
		 */
		public <T> T as(Class<T> kind);
	}

	// =======================================================
	// Constructor API (for convenience)
	// =======================================================

	public static Attribute ATTRIBUTE(Object o) {
		return new Attribute() {
			@Override
			public <T> T as(Class<T> kind) {
				if(kind.isInstance(o)) {
					return (T) o;
				} else {
					return null;
				}
			}
			@Override
			public String toString() {
				return "ATTR(" + o + ")";
			}
		};
	}

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

	// Statement
	public static Stmt.Assert ASSERT(Expr.Logical condition, Attribute... attributes) {
		return new Stmt.Assert(condition,attributes);
	}
	public static Stmt.Assignment ASSIGN(LVal lhs, Expr rhs, Attribute... attributes) {
		return new Stmt.Assignment(lhs,rhs,attributes);
	}
	public static Stmt.Assume ASSUME(Expr.Logical condition, Attribute... attributes) {
		return new Stmt.Assume(condition,attributes);
	}
	public static Stmt.Call CALL(String name, Expr[] parameters, Attribute... attributes) {
		return new Stmt.Call(name, Collections.EMPTY_LIST, Arrays.asList(parameters),attributes);
	}
	public static Stmt.Call CALL(String name, List<Expr> parameters, Attribute... attributes) {
		return new Stmt.Call(name, Collections.EMPTY_LIST, parameters,attributes);
	}
	public static Stmt.Call CALL(String name, LVal lhs, Expr[] parameters, Attribute... attributes) {
		return new Stmt.Call(name, Arrays.asList(lhs), Arrays.asList(parameters),attributes);
	}
	public static Stmt.Call CALL(String name, LVal lhs, List<Expr> parameters, Attribute... attributes) {
		return new Stmt.Call(name, Arrays.asList(lhs), parameters,attributes);
	}
	public static Stmt.Call CALL(String name, List<LVal> lvals, Expr parameter, Attribute... attributes) {
		return new Stmt.Call(name, lvals, Arrays.asList(parameter),attributes);
	}
	public static Stmt.Call CALL(String name, List<LVal> lvals, Expr parameter1, Expr parameter2 , Attribute... attributes) {
		return new Stmt.Call(name, lvals, Arrays.asList(parameter1,parameter2),attributes);
	}
	public static Stmt.Call CALL(String name, List<LVal> lvals, List<Expr> parameters, Attribute... attributes) {
		return new Stmt.Call(name, lvals, parameters,attributes);
	}
	public static Stmt.IfElse IFELSE(Expr.Logical condition, Stmt trueBranch, Stmt falseBranch, Attribute... attributes) {
		return new Stmt.IfElse(condition, trueBranch, falseBranch, attributes);
	}
	public static Stmt.Label LABEL(String label, Attribute... attributes) {
		return new Stmt.Label(label,attributes);
	}
	public static Stmt.Goto GOTO(List<String> labels, Attribute... attributes) {
		return new Stmt.Goto(labels,attributes);
	}

	public static Stmt.Goto GOTO(String label, Attribute... attributes) {
		return new Stmt.Goto(Arrays.asList(label),attributes);
	}
	public static Stmt.While WHILE(Expr.Logical condition, List<Expr.Logical> invariant, Stmt body, Attribute... attributes) {
		return new Stmt.While(condition, invariant, body, attributes);
	}

	public static Stmt.Sequence SEQUENCE(List<Stmt> stmts, Attribute... attributes) {
		return new Stmt.Sequence(stmts,attributes);
	}

	public static Stmt.Sequence SEQUENCE(List<Stmt> stmts, Stmt stmt, Attribute... attributes) {
		ArrayList<Stmt> ss = new ArrayList<>(stmts);
		ss.add(stmt);
		return new Stmt.Sequence(ss,attributes);
	}
	public static Stmt.Sequence SEQUENCE(Attribute... attributes) {
		return new Stmt.Sequence(Collections.EMPTY_LIST,attributes);
	}
	public static Stmt.Sequence SEQUENCE(Stmt stmt, Attribute... attributes) {
		return new Stmt.Sequence(Arrays.asList(stmt),attributes);
	}
	public static Stmt.Sequence SEQUENCE(Stmt stmt1, Stmt stmt2, Attribute... attributes) {
		return new Stmt.Sequence(Arrays.asList(stmt1,stmt2),attributes);
	}
	public static Stmt.Return RETURN(Attribute... attributes) {
		return new Stmt.Return(attributes);
	}
	// Logical Operators
	public static Expr.Logical AND(List<Expr.Logical> operands, Attribute... attributes) {
		ArrayList<Expr.Logical> noperands = new ArrayList<>();
		for(int i=0;i!=operands.size();++i) {
			Expr.Logical ith = operands.get(i);
			if (ith.isFalse()) {
				return new Expr.Boolean(false, attributes);
			} else if (!ith.isTrue()) {
				noperands.add(ith);
			}
		}
		switch (noperands.size()) {
			case 0:
				return new Expr.Boolean(true,attributes);
			case 1:
				return noperands.get(0);
			default:
				return new Expr.LogicalAnd(noperands, attributes);
		}
	}

	public static Expr.Logical AND(Expr.Logical operand1, Expr.Logical operand2, Attribute... attributes) {
		return AND(Arrays.asList(operand1, operand2),attributes);
	}
	public static Expr.Logical AND(Expr.Logical operand1, Expr.Logical operand2, Expr.Logical operand3, Attribute... attributes) {
		return AND(Arrays.asList(operand1, operand2, operand3),attributes);
	}
	public static Expr.Logical AND(Expr.Logical[] operands, Attribute... attributes) {
		return AND(Arrays.asList(operands),attributes);
	}
	public static Expr.UniversalQuantifier FORALL(String name, BoogieFile.Type type, Expr.Logical body, Attribute... attributes) {
		return new Expr.UniversalQuantifier(Arrays.asList(new Decl.Parameter(name, type)),body, attributes);
	}

	public static Expr.UniversalQuantifier FORALL(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,
												  Expr.Logical body, Attribute... attributes) {
		return new Expr.UniversalQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2)), body, attributes);
	}

	public static Expr.UniversalQuantifier FORALL(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,String name3, BoogieFile.Type type3,
												  Expr.Logical body, Attribute... attributes) {
		return new Expr.UniversalQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2), new Decl.Parameter(name3, type3)), body, attributes);
	}

	public static Expr.UniversalQuantifier FORALL(List<Decl.Parameter> parameters, Expr.Logical body, Attribute... attributes) {
		return new Expr.UniversalQuantifier(parameters, body, attributes);
	}


	public static Expr.ExistentialQuantifier EXISTS(String name, BoogieFile.Type type, Expr.Logical body, Attribute... attributes) {
		return new Expr.ExistentialQuantifier(Arrays.asList(new Decl.Parameter(name, type)),body, attributes);
	}

	public static Expr.ExistentialQuantifier EXISTS(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,
												  Expr.Logical body, Attribute... attributes) {
		return new Expr.ExistentialQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2)), body, attributes);
	}

	public static Expr.ExistentialQuantifier EXISTS(String name1, BoogieFile.Type type1, String name2, BoogieFile.Type type2,String name3, BoogieFile.Type type3,
												  Expr.Logical body, Attribute... attributes) {
		return new Expr.ExistentialQuantifier(Arrays.asList(new Decl.Parameter(name1, type1), new Decl.Parameter(name2, type2), new Decl.Parameter(name3, type3)), body, attributes);
	}

	public static Expr.ExistentialQuantifier EXISTS(List<Decl.Parameter> parameters, Expr.Logical body, Attribute... attributes) {
		return new Expr.ExistentialQuantifier(parameters, body, attributes);
	}


	public static Expr.Logical IFF(Expr.Logical lhs, Expr.Logical rhs, Attribute... attributes) {
		if(lhs instanceof Expr.Boolean && rhs instanceof Expr.Boolean) {
			return (lhs == rhs) ? new Expr.Boolean(true,attributes) : new Expr.Boolean(false,attributes);
		} else {
			return new Expr.Iff(lhs, rhs, attributes);
		}
	}

	public static Expr.Logical IMPLIES(Expr.Logical lhs, Expr.Logical rhs, Attribute... attributes) {
		//
		if(lhs.isFalse() || rhs.isTrue()) {
			return new Expr.Boolean(true,attributes);
		} else if(lhs.isTrue()) {
			return rhs;
		} else if(rhs.isFalse()) {
			return lhs;
		} else {
			return new Expr.Implies(lhs, rhs, attributes);
		}
	}

	public static Expr.Logical NOT(Expr.Logical lhs, Attribute... attributes) {
		if(lhs.isFalse()) {
			return new Expr.Boolean(true,attributes);
		} else if(lhs.isTrue()) {
			return new Expr.Boolean(false,attributes);
		} else {
			return new Expr.LogicalNot(lhs, attributes);
		}
	}

	public static Expr.Logical OR(List<Expr.Logical> operands, Attribute... attributes) {
		ArrayList<Expr.Logical> noperands = new ArrayList<>();
		for(int i=0;i!=operands.size();++i) {
			Expr.Logical ith = operands.get(i);
			if(ith.isTrue()) {
				return new Expr.Boolean(true,attributes);
			} else if(!ith.isFalse()) {
				noperands.add(ith);
			}
		}
		switch (noperands.size()) {
			case 0:
				return new Expr.Boolean(false,attributes);
			case 1:
				return noperands.get(0);
			default:
				return new Expr.LogicalOr(noperands, attributes);
		}
	}

	public static Expr.Logical OR(Expr.Logical operand1, Expr.Logical operand2, Attribute... attributes) {
		return OR(new Expr.Logical[]{operand1, operand2}, attributes);
	}

	public static Expr.Logical OR(Expr.Logical operand1, Expr.Logical operand2, Expr.Logical operand3, Attribute... attributes) {
		return OR(new Expr.Logical[]{operand1, operand2, operand3}, attributes);
	}

	public static Expr.Logical OR(Expr.Logical operand1, Expr.Logical operand2, Expr.Logical operand3,  Expr.Logical operand4, Attribute... attributes) {
		return OR(new Expr.Logical[]{operand1, operand2, operand3, operand4}, attributes);
	}

	public static Expr.Logical OR(Expr.Logical operand1, Expr.Logical operand2, Expr.Logical operand3,  Expr.Logical operand4,  Expr.Logical operand5, Attribute... attributes) {
		return OR(new Expr.Logical[]{operand1, operand2, operand3, operand4, operand5}, attributes);
	}

	public static Expr.Logical OR(Expr.Logical[] operands, Attribute... attributes) {
		return OR(Arrays.asList(operands),attributes);
	}

	// Relational Operators

	public static Expr.Equals EQ(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.Equals(lhs, rhs,attributes);
	}

	public static Expr.NotEquals NEQ(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.NotEquals(lhs, rhs,attributes);
	}

	public static Expr.GreaterThanOrEqual GTEQ(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.GreaterThanOrEqual(lhs, rhs,attributes);
	}

	public static Expr.GreaterThan GT(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.GreaterThan(lhs, rhs,attributes);
	}

	public static Expr.LessThanOrEqual LTEQ(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.LessThanOrEqual(lhs, rhs,attributes);
	}

	public static Expr.LessThan LT(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.LessThan(lhs, rhs, attributes);
	}

	// Arithmetic Operators
	public static Expr.Addition ADD(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.Addition(lhs, rhs, attributes);
	}

	public static Expr.Negation NEG(Expr lhs, Attribute... attributes) {
		return new Expr.Negation(lhs, attributes);
	}

	public static Expr.Subtraction SUB(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.Subtraction(lhs, rhs, attributes);
	}
	public static Expr.Multiplication MUL(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.Multiplication(lhs, rhs, attributes);
	}
	public static Expr.Division DIV(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.Division(lhs, rhs, attributes);
	}

	public static Expr.IntegerDivision IDIV(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.IntegerDivision(lhs, rhs, attributes);
	}
	public static Expr.Remainder REM(Expr lhs, Expr rhs, Attribute... attributes) {
		return new Expr.Remainder(lhs, rhs, attributes);
	}
	// Dictionaries
	public static Expr.DictionaryAccess GET(Expr src, Expr index, Attribute... attributes) {
		return new Expr.DictionaryAccess(src, index, attributes);
	}
	public static Expr.DictionaryUpdate PUT(Expr src, Expr index, Expr value, Attribute... attributes) {
		return new Expr.DictionaryUpdate(src, index, value, attributes);
	}
	// Misc
	public static Expr.Logical CONST(boolean b, Attribute... attributes) {
		return new Expr.Boolean(b,attributes);
	}

	public static Expr.Integer CONST(int i, Attribute... attributes) {
		return new Expr.Integer(BigInteger.valueOf(i), attributes);
	}

	public static Expr.Integer CONST(BigInteger i, Attribute... attributes) {
		return new Expr.Integer(i, attributes);
	}

	public static Expr.Bytes CONST(byte[] bytes, Attribute... attributes) {
		return new Expr.Bytes(bytes, attributes);
	}

	public static Expr.Old OLD(Expr lhs, Attribute... attributes) {
		return new Expr.Old(lhs, attributes);
	}

	public static Expr.Invoke INVOKE(String name, Expr[] parameters, Attribute... attributes) {
		return new Expr.Invoke(name, Arrays.asList(parameters),attributes);
	}
	public static Expr.Invoke INVOKE(String name, Attribute... attributes) {
		return new Expr.Invoke(name, Collections.EMPTY_LIST,attributes);
	}
	public static Expr.Invoke INVOKE(String name, Expr parameter, Attribute... attributes) {
		return new Expr.Invoke(name, Arrays.asList(parameter),attributes);
	}
	public static Expr.Invoke INVOKE(String name, Expr parameter1, Expr parameter2, Attribute... attributes) {
		return new Expr.Invoke(name, Arrays.asList(parameter1,parameter2),attributes);
	}
	public static Expr.Invoke INVOKE(String name, Expr parameter1, Expr parameter2, Expr parameter3, Attribute... attributes) {
		return new Expr.Invoke(name, Arrays.asList(parameter1,parameter2,parameter3),attributes);
	}
	public static Expr.Invoke INVOKE(String name, List<Expr> parameters, Attribute... attributes) {
		return new Expr.Invoke(name, parameters,attributes);
	}
	public static Expr.VariableAccess VAR(String name, Attribute... attributes) {
		return new Expr.VariableAccess(name,attributes);
	}
}
