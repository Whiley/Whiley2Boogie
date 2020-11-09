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

		public static class Axiom implements Decl {
			private final Expr operand;

			public Axiom(Expr operand) {
				this.operand = operand;
			}

			public Expr getOperand() {
				return operand;
			}
		}

		public static class LineComment implements Decl {
			private final String message;

			public LineComment(String message) {
				this.message = message;
			}

			public String getMessage() {
				return message;
			}
		}
		
		public static class Constant extends Parameter implements Decl {
			private final boolean unique;
			
			public Constant(String name, Type type) {
				super(name, type);
				this.unique = false;
			}
			public Constant(boolean unique, String name, Type type) {
				super(name, type);
				this.unique = unique;
			}			
			public boolean isUnique() {
				return unique;
			}
		}

		public static class Function implements Decl {
			private final String name;
			private final List<Parameter> parameters;
			private final Type returns;
			private final Expr body;

			public Function(String name, Parameter parameter, Type returns) {
				this(name, Arrays.asList(parameter), returns, null);
			}
			
			public Function(String name, Parameter parameter, Type returns, Expr body) {
				this(name,Arrays.asList(parameter),returns,body);
			}
			
			public Function(String name, List<Parameter> parameters, Type returns, Expr body) {
				this.name = name;
				this.parameters = parameters;
				this.returns = returns;
				this.body = body;
			}


			public String getName() {
				return name;
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
			private final Stmt.Block trueBranch;
			private final Stmt.Block falseBranch;

			public IfElse(Expr condition, Stmt.Block trueBranch, Stmt.Block falseBranch) {
				this.condition = condition;
				this.trueBranch = trueBranch;
				this.falseBranch = falseBranch;
			}

			public Expr getCondition() {
				return condition;
			}

			public Stmt.Block getTrueBranch() {
				return trueBranch;
			}

			public Stmt.Block getFalseBranch() {
				return falseBranch;
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
				NEG
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
		public static final Type Bool = new Type() {};
		public static final Type Int = new Type() {};
		public static final Type Real = new Type() {};

		public static class Synonym implements Type {
			private final String name;

			public Synonym(String name) {
				this.name = name;
			}

			public String getSynonym() {
				return name;
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
}
