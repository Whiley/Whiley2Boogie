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
package wyboogie.io;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.List;

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;

public class BoogieFilePrinter {
	private final PrintWriter out;

	public BoogieFilePrinter(OutputStream output) {
		this.out = new PrintWriter(output);
	}

	public void write(BoogieFile file) {
		for(Decl d : file.getDeclarations()) {
			writeDecl(0, d);
		}
		out.flush();
	}

	private void writeDecl(int indent, Decl d) {
		if(d instanceof Decl.Axiom) {
			writeAxiom(indent, (Decl.Axiom) d);
		} else if(d instanceof Decl.Procedure) {
			writeProcedure(indent,(Decl.Procedure) d);
		} else {
			throw new IllegalArgumentException("unknown declaration encountered (" + d.getClass().getName() + ")");
		}
	}

	private void writeAxiom(int indent, Decl.Axiom d) {
		tab(indent);
		out.print("axiom ");
		writeExpr(d.getOperand());
		out.println(";");
	}

	private void writeProcedure(int indent, Decl.Procedure d) {
		tab(indent);
		out.print("procedure ");
		out.print(d.getName());
		writeParameters(d.getParmeters());
		if(!d.getReturns().isEmpty()) {
			out.print(" returns ");
			writeParameters(d.getReturns());
		}
		writeBlock(indent,d.getBody());
	}

	private void writeParameters(List<Decl.Parameter> parameters) {
		out.print("(");
		for(int i=0;i!=parameters.size();++i) {
			if(i != 0) {
				out.print(", ");
			}
			writeParameter(parameters.get(i));
		}
		out.print(")");
	}

	private void writeParameter(Decl.Parameter parameter) {
		out.print(parameter.getName());
		out.print(" : ");
	}

	private void writeStmt(int indent, Stmt s) {
		if(s instanceof Stmt.Assert) {
			writeAssert(indent,(Stmt.Assert) s);
		} else if(s instanceof Stmt.Block) {
			writeBlock(indent,(Stmt.Block)s);
		} else {
			throw new IllegalArgumentException("unknown statement encountered (" + s.getClass().getName() + ")");
		}
	}

	private void writeBlock(int indent, Stmt.Block s) {
		out.println("{");
		indent = indent + 1;
		for(int i=0;i!=s.size();++i) {
			writeStmt(indent,s.get(i));
		}
		out.println("}");
	}
	private void writeAssert(int indent, Stmt.Assert s) {
		tab(indent);
		out.print("assert ");
		writeExpr(s.getCondition());
		out.println(";");
	}

	private void writeExpr(Expr e) {
		if(e instanceof Expr.Constant) {
			writeConstant((Expr.Constant) e);
		} else {
			throw new IllegalArgumentException("unknown expression encountered (" + e.getClass().getName() + ")");
		}
	}

	private void writeConstant(Expr.Constant e) {
		out.write(e.getValue().toString());
	}

	private void tab(int indent) {
		for (int i = 0; i != indent; ++i) {
			out.print("   ");
		}
	}
}
