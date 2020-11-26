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
import java.util.Objects;

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
		} else if(d instanceof Decl.Constant) {
			writeConstant(indent,(Decl.Constant) d);
		} else if(d instanceof Decl.Function) {
			writeFunction(indent,(Decl.Function) d);
		} else if(d instanceof Decl.Implementation) {
			writeImplementation(indent,(Decl.Implementation) d);
		} else if(d instanceof Decl.LineComment) {
			writeLineComment(indent,(Decl.LineComment) d);
		} else if(d instanceof Decl.Procedure) {
			writeProcedure(indent,(Decl.Procedure) d);
		} else if(d instanceof Decl.Sequence) {
			writeSequence(indent,(Decl.Sequence) d);
		} else if(d instanceof Decl.TypeSynonym) {
			writeTypeSynonym(indent,(Decl.TypeSynonym) d);
		} else if(d instanceof Decl.Variable) {
			writeVariable(indent,(Decl.Variable) d);
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

	private void writeConstant(int indent, Decl.Constant d) {
		tab(indent);
		out.print("const ");
		if(d.isUnique()) {
			out.print("unique ");
		}
		out.print(d.getName());
		out.print(" : ");
		writeType(d.getType());
		out.println(";");
	}

	private void writeImplementation(int indent, Decl.Implementation d) {
		tab(indent);
		out.print("implementation ");
		out.print(d.getName());
		writeParameters(d.getParmeters());
		if(!d.getReturns().isEmpty()) {
			out.print(" returns ");
			writeParameters(d.getReturns());
		}
		if(d.getBody() == null) {
			out.println(";");
		} else {
			out.println();
		}
		tab(indent);
		out.println("{");
		List<Decl.Variable> locals = d.getLocals();
		for(int i=0;i!=locals.size();++i) {
			writeVariable(indent + 1, locals.get(i));
		}
		writeStmt(indent + 1, d.getBody());
		tab(indent);
		out.println("}");
	}

	private void writeFunction(int indent, Decl.Function d) {
		tab(indent);
		out.print("function ");
		out.print(d.getName());
		writeParameters(d.getParmeters());
		out.print(" returns (");
		writeType(d.getReturns());
		out.print(")");
		if(d.getBody() != null) {
			out.println(" {");
			tab(indent+1);
			writeExpression(d.getBody());
			out.println();
			tab(indent);
			out.println("}");
		} else {
			out.println(";");
		}
	}

	private void writeLineComment(int indent, Decl.LineComment d) {
		tab(indent);
		out.println("// " + d.getMessage());
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
		if(d.getBody() == null) {
			out.println(";");
		} else {
			out.println();
		}
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
		tab(indent);
		if(d.getBody() != null) {
			out.println("{");
			List<Decl.Variable> locals = d.getLocals();
			for(int i=0;i!=locals.size();++i) {
				writeVariable(indent + 1, locals.get(i));
			}
			writeStmt(indent + 1, d.getBody());
			tab(indent);
			out.println("}");
		}
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
		if (parameter.getName() != null) {
			out.print(parameter.getName());
			out.print(" : ");
		}
		writeType(parameter.getType());
	}
	private void writeSequence(int indent, Decl.Sequence s) {
		for(int i=0;i!=s.size();++i) {
			writeDecl(indent,s.get(i));
		}
	}
	private void writeTypeSynonym(int indent, Decl.TypeSynonym d) {
		tab(indent);
		out.print("type ");
		out.print(d.getName());
		if(d.getSynonym() != null) {
			out.print(" = ");
			writeType(d.getSynonym());
		}
		out.println(";");
	}
	private void writeVariable(int indent, Decl.Variable d) {
		tab(indent);
		out.print("var ");
		out.print(d.getName());
		out.print(" : ");
		writeType(d.getType());
		if(d.getInvariant() != null) {
			out.print(" where ");
			writeExpression(d.getInvariant());
		}
		out.println(";");
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
		} else if(s instanceof Stmt.IfElse) {
			writeIfElse(indent,(Stmt.IfElse)s);
		} else if(s instanceof Stmt.Return) {
			writeReturn(indent,(Stmt.Return)s);
		} else if(s instanceof Stmt.Sequence) {
			writeSequence(indent,(Stmt.Sequence)s);
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
	private void writeGoto(int indent, Stmt.Goto s) {
		tab(indent);
		out.print("goto ");
		for(int i=0;i!=s.size();++i) {
			if(i != 0) {
				out.print(", ");
			}
			out.print(s.get(i));
		}
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
		out.print(") {");
		writeStmt(indent + 1, s.getTrueBranch());
		if(s.getFalseBranch() != null) {
			out.println("} else {");
			writeStmt(indent + 1, s.getFalseBranch());
		}
		out.println("}");
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
		tab(indent);
		out.println("{");
		writeStmt(indent + 1, s.getBody());
		out.println("}");
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
		if(e instanceof Expr.DictionaryAccess) {
			writeDictionaryAccess((Expr.DictionaryAccess) e);
		} else if(e instanceof Expr.DictionaryUpdate) {
			writeDictionaryUpdate((Expr.DictionaryUpdate) e);
		} else if(e instanceof Expr.BinaryOperator) {
			writeBinaryOperator((Expr.BinaryOperator) e);
		} else if(e instanceof Expr.Constant) {
			writeConstant((Expr.Constant) e);
		} else if(e instanceof Expr.NaryOperator) {
			writeNaryOperator((Expr.NaryOperator) e);
		} else if(e instanceof Expr.Quantifier) {
			writeQuantifier((Expr.Quantifier) e);
		} else if(e instanceof Expr.Invoke) {
			writeInvoke((Expr.Invoke) e);
		} else if(e instanceof Expr.UnaryOperator) {
			writeUnaryOperator((Expr.UnaryOperator) e);
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
		// NOTE: have to handle possibility of null here
		out.write(Objects.toString(e.getValue()));
	}

	private void writeDictionaryAccess(Expr.DictionaryAccess e) {
		writeExpression(e.getSource());
		out.print("[");
		writeExpression(e.getIndex());
		out.print("]");
	}

	private void writeDictionaryUpdate(Expr.DictionaryUpdate e) {
		writeExpression(e.getSource());
		out.print("[");
		writeExpression(e.getIndex());
		out.print(":=");
		writeExpression(e.getValue());
		out.print("]");
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
	private void writeInvoke(Expr.Invoke e) {
		out.print(e.getName());
		out.print("(");
		boolean firstTime = true;
		for(Expr a : e.getArguments()) {
			if(!firstTime) {
				out.print(",");
			}
			firstTime = false;
			writeExpression(a);
		}
		out.print(")");
	}
	private void writeQuantifier(Expr.Quantifier e) {
		out.print("(");
		List<Decl.Parameter> params = e.getParameters();
		if(e.isUniversal()) {
			out.print("forall ");
		} else {
			out.print("exists ");
		}
		for(int i=0;i!=params.size();++i) {
			Decl.Parameter ith = params.get(i);
			if(i != 0) {
				out.print(",");
			}
			out.print(ith.getName());
			out.print(":");
			writeType(ith.getType());
		}
		out.print(" :: ");
		writeExpression(e.getBody());
		out.print(")");
	}

	private void writeUnaryOperator(Expr.UnaryOperator e) {
		switch(e.getKind()) {
		case NEG:
			out.print("-");
			writeExpression(e.getOperand());
			break;
		case NOT:
			out.print("!");
			writeExpression(e.getOperand());
			break;
		default:
			throw new IllegalArgumentException("unknown unary operator encountered (" + e.getClass().getName() + ")");
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
		} else if(t instanceof Type.Synonym) {
			Type.Synonym s = (Type.Synonym) t;
			out.print(s.getSynonym());
		} else if(t instanceof Type.Dictionary) {
			Type.Dictionary m = (Type.Dictionary) t;
			out.print("[");
			writeType(m.getKey());
			out.print("]");
			writeType(m.getValue());
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
		case IDIV:
			out.print(" div ");
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
