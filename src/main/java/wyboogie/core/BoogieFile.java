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
			private final Stmt.Block body;

			public Procedure(String name, List<Parameter> parameters, List<Parameter> returns, Stmt.Block body) {
				this.name = name;
				this.parameters = new ArrayList<>(parameters);
				this.returns = new ArrayList<>(parameters);
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

			public Stmt.Block getBody() {
				return body;
			}
		}

		public static class Parameter {
			private final String name;

			public Parameter(String name) {
				this.name = name;
			}

			public String getName() {
				return name;
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
	}
}
