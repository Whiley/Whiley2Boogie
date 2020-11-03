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
import wyboogie.core.BoogieFile.Type;

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
		writeExpression(d.getOperand());
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
		out.println();
		List<Expr> requires = d.getRequires();
		List<Expr> ensures = d.getEnsures();
		for(int i=0;i!=requires.size();++i) {
			out.print("requires ");
			writeExpression(requires.get(i));
			out.println(";");
		}
		for(int i=0;i!=ensures.size();++i) {
			out.print("ensures ");
			writeExpression(ensures.get(i));
			out.println(";");
		}
		writeBlock(indent, d.getBody(), false);
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
		writeType(parameter.getType());
	}

	private void writeStmt(int indent, Stmt s) {
		if(s instanceof Stmt.Assignment) {
			writeAssignment(indent,(Stmt.Assignment) s);
		} else if(s instanceof Stmt.Assert) {
			writeAssert(indent,(Stmt.Assert) s);
		} else if(s instanceof Stmt.Assume) {
			writeAssume(indent,(Stmt.Assume) s);
		} else if(s instanceof Stmt.Goto) {
			writeGoto(indent,(Stmt.Goto)s);
		} else if(s instanceof Stmt.Label) {
			writeLabel(indent,(Stmt.Label)s);
		} else if(s instanceof Stmt.Block) {
			writeBlock(indent, (Stmt.Block) s, false);
		} else if(s instanceof Stmt.IfElse) {
			writeIfElse(indent,(Stmt.IfElse)s);
		} else if(s instanceof Stmt.Return) {
			writeReturn(indent,(Stmt.Return)s);
		} else if(s instanceof Stmt.Sequence) {
			writeSequence(indent,(Stmt.Sequence)s);
		} else if(s instanceof Stmt.VariableDeclarations) {
			writeVariableDeclarations(indent,(Stmt.VariableDeclarations)s);
		} else if(s instanceof Stmt.While) {
			writeWhile(indent,(Stmt.While)s);
		} else {
			throw new IllegalArgumentException("unknown statement encountered (" + s.getClass().getName() + ")");
		}
	}
	private void writeAssignment(int indent, Stmt.Assignment s) {
		tab(indent);
		writeExpression(s.getLeftHandSide());
		out.print(" := ");
		writeExpression(s.getRightHandSide());
		out.println(";");
	}
	private void writeAssert(int indent, Stmt.Assert s) {
		tab(indent);
		out.print("assert ");
		writeExpression(s.getCondition());
		out.println(";");
	}
	private void writeAssume(int indent, Stmt.Assume s) {
		tab(indent);
		out.print("assume ");
		writeExpression(s.getCondition());
		out.println(";");
	}
	private void writeBlock(int indent, Stmt.Block s, boolean inline) {
		if(!inline) {
			tab(indent);
		}
		out.println("{");
		indent = indent + 1;
		for(int i=0;i!=s.size();++i) {
			writeStmt(indent,s.get(i));
		}
		tab(indent - 1);
		out.println("}");
	}
	private void writeGoto(int indent, Stmt.Goto s) {
		tab(indent);
		out.print("goto ");
		out.print(s.getLabel());
		out.println(";");
	}
	private void writeLabel(int indent, Stmt.Label s) {
		tab(indent);
		out.print(s.getLabel());
		out.println(":");
	}
	private void writeIfElse(int indent, Stmt.IfElse s) {
		tab(indent);
		out.print("if(");
		writeExpression(s.getCondition());
		out.print(") ");
		writeBlock(indent,s.getTrueBranch(),true);
		if(s.getFalseBranch() != null) {
			out.print(" else ");
			writeBlock(indent,s.getFalseBranch(),true);
		}
	}
	private void writeReturn(int indent, Stmt.Return s) {
		tab(indent);
		out.println("return;");
	}
	private void writeSequence(int indent, Stmt.Sequence s) {
		for(int i=0;i!=s.size();++i) {
			writeStmt(indent,s.get(i));
		}
	}
	private void writeWhile(int indent, Stmt.While s) {
		tab(indent);
		out.print("while(");
		writeExpression(s.getCondition());
		out.println(")");
		List<Expr> invariant = s.getInvariant();
		for(int i=0;i!=invariant.size();++i) {
			tab(indent);
			out.print("invariant ");
			writeExpression(invariant.get(i));
			out.println(";");
		}
		writeBlock(indent, s.getBody(), false);
	}
	private void writeVariableDeclarations(int indent, Stmt.VariableDeclarations s) {
		tab(indent);
		out.print("var ");
		List<String> names = s.getNames();
		for(int i=0;i!=names.size();++i) {
			if(i != 0) {
				out.print(", ");
			}
			out.print(names.get(i));
		}
		out.print(" : ");
		writeType(s.getType());
		out.println(";");
	}
	private void writeExpressionWithBraces(Expr e) {
		if (e instanceof Expr.UnaryOperator || e instanceof Expr.BinaryOperator || e instanceof Expr.NaryOperator) {
			out.print("(");
			writeExpression(e);
			out.print(")");
		} else {
			writeExpression(e);
		}
	}

	private void writeExpression(Expr e) {
		if(e instanceof Expr.BinaryOperator) {
			writeBinaryOperator((Expr.BinaryOperator) e);
		} else if(e instanceof Expr.Constant) {
			writeConstant((Expr.Constant) e);
		} else if(e instanceof Expr.NaryOperator) {
			writeNaryOperator((Expr.NaryOperator) e);
		} else if(e instanceof Expr.VariableAccess) {
			writeVariableAccess((Expr.VariableAccess) e);
		} else {
			throw new IllegalArgumentException("unknown expression encountered (" + e.getClass().getName() + ")");
		}
	}

	private void writeBinaryOperator(Expr.BinaryOperator e) {
		writeExpressionWithBraces(e.getLeftHandSide());
		writeBinaryOperatorKind(e.getKind());
		writeExpressionWithBraces(e.getRightHandSide());
	}

	private void writeConstant(Expr.Constant e) {
		out.write(e.getValue().toString());
	}
	private void writeNaryOperator(Expr.NaryOperator e) {
		List<Expr> operands = e.getOperands();
		//
		for(int i=0;i!=operands.size();++i) {
			if(i != 0) {
				writeNaryOperatorKind(e.getKind());
			}
			writeExpressionWithBraces(operands.get(i));
		}
	}
	private void writeVariableAccess(Expr.VariableAccess e) {
		out.write(e.getVariable());
	}

	private void writeType(Type t) {
		if(t == Type.Bool) {
			out.print("bool");
		} else if(t == Type.Int) {
			out.print("int");
		} else {
			throw new IllegalArgumentException("unknown type encountered (" + t.getClass().getName() + ")");
		}
	}

	private void writeBinaryOperatorKind(Expr.BinaryOperator.Kind k) {
		switch(k) {
		case EQ:
			out.print(" == ");
			break;
		case NEQ:
			out.print(" != ");
			break;
		case LT:
			out.print(" < ");
			break;
		case LTEQ:
			out.print(" <= ");
			break;
		case GT:
			out.print(" > ");
			break;
		case GTEQ:
			out.print(" >= ");
			break;
		case IFF:
			out.print(" <==> ");
			break;
		case IF:
			out.print(" ==> ");
			break;
		case ADD:
			out.print(" + ");
			break;
		case SUB:
			out.print(" - ");
			break;
		case MUL:
			out.print(" * ");
			break;
		case DIV:
			out.print(" / ");
			break;
		case REM:
			out.print(" % ");
			break;
		default:
			throw new IllegalArgumentException("unknown binary operator kind encountered (" + k + ")");
		}
	}

	private void writeNaryOperatorKind(Expr.NaryOperator.Kind k) {
		switch(k) {
		case AND:
			out.print(" && ");
			break;
		case OR:
			out.print(" || ");
			break;
		default:
			throw new IllegalArgumentException("unknown nary operator kind encountered (" + k + ")");
		}
	}


	private void tab(int indent) {
		for (int i = 0; i != indent; ++i) {
			out.print("   ");
		}
	}
}
