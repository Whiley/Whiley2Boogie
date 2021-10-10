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
package wyboogie.util;

import java.util.ArrayList;
import java.util.List;
import jbfs.util.Pair;
import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Expr;


public abstract class AbstractExpressionTransform<S> extends AbstractExpressionVisitor<Pair<S, Expr>, Pair<S, Expr>> {

    public abstract S join(S lhs, S rhs);

    public abstract S join(List<S> operands);

    // Integers
    @Override
	protected Pair<S,Expr> constructInteger(Expr.Integer expr) {
        return new Pair<>(null, expr);
    }

    @Override
    protected Pair<S,Expr> constructNegation(Expr.Negation expr, Pair<S,Expr> operand) {
        if(expr.getOperand() == operand.second()) {
            return new Pair<>(operand.first(), expr);
        } else {
            return new Pair<>(operand.first(), BoogieFile.NEG(operand.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructAddition(Expr.Addition expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.ADD(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructSubtraction(Expr.Subtraction expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.SUB(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructMultiplication(Expr.Multiplication expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.MUL(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructDivision(Expr.Division expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.DIV(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructIntegerDivision(Expr.IntegerDivision expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.IDIV(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructRemainder(Expr.Remainder expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.REM(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructLessThan(Expr.LessThan expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.LT(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructLessThanOrEqual(Expr.LessThanOrEqual expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.LTEQ(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructGreaterThan(Expr.GreaterThan expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.GT(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructGreaterThanOrEqual(Expr.GreaterThanOrEqual expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.GTEQ(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }

    // Logical
    @Override
	protected Pair<S,Expr> constructBoolean(Expr.Boolean expr) {
        return new Pair<>(null, expr);
    }

    @Override
    protected Pair<S,Expr> constructLogicalAnd(Expr.LogicalAnd expr, List<Pair<S,Expr>> states) {
        S state = join(extractFirst(states));
        if(equals(expr.getOperands(),states)) {
            return new Pair<>(state, expr);
        } else {
            List operands = extractSecond(states);
            return new Pair<>(state,BoogieFile.AND(operands, expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructLogicalImplication(Expr.Implies expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.IMPLIES((Expr.Logical) lhs.second(), (Expr.Logical) rhs.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructLogicalIff(Expr.Iff expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.IFF((Expr.Logical) lhs.second(), (Expr.Logical) rhs.second(), expr.getAttributes()));
        }
    }

    @Override
    protected Pair<S, Expr> constructLogicalNot(Expr.LogicalNot expr, Pair<S, Expr> operand) {
        if (expr.getOperand() == operand.second()) {
            return new Pair<>(operand.first(), expr);
        } else {
            return new Pair<>(operand.first(), BoogieFile.NOT((Expr.Logical) operand.second(), expr.getAttributes()));
        }
    }

    @Override
    protected Pair<S,Expr> constructLogicalOr(Expr.LogicalOr expr, List<Pair<S,Expr>> states) {
        S state = join(extractFirst(states));
        if(equals(expr.getOperands(),states)) {
            return new Pair<>(state, expr);
        } else {
            List operands = extractSecond(states);
            return new Pair<>(state,BoogieFile.OR(operands, expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S,Expr> constructExistentialQuantifier(Expr.ExistentialQuantifier expr, Pair<S,Expr> body) {
        if(body.second() == expr.getBody()) {
            return new Pair<>(body.first(), expr);
        } else {
            return new Pair<>(body.first(), BoogieFile.EXISTS(expr.getParameters(), (Expr.Logical) body.second(), expr.getAttributes()));
        }
    }
    @Override
    protected Pair<S, Expr> constructUniversalQuantifier(Expr.UniversalQuantifier expr, Pair<S, Expr> body) {
        if (body.second() == expr.getBody()) {
            return new Pair<>(body.first(), expr);
        } else {
            return new Pair<>(body.first(), BoogieFile.FORALL(expr.getParameters(), (Expr.Logical) body.second(), expr.getAttributes()));
        }
    }

    // Dictionaries

    @Override
    protected Pair<S, Expr> constructDictionaryAccess(Expr.DictionaryAccess expr, Pair<S, Expr> source, Pair<S, Expr> index) {
        S s = join(source.first(), index.first());
        if (expr.getSource() == source.second() && expr.getIndex() == index.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.GET(source.second(), index.second(), expr.getAttributes()));
        }
    }

    @Override
    protected Pair<S,Expr> constructDictionaryUpdate(Expr.DictionaryUpdate expr, Pair<S, Expr> source, Pair<S, Expr> index, Pair<S, Expr> value) {
        S s = join(source.first(), join(index.first(), value.first()));
        if (expr.getSource() == source.second() && expr.getIndex() == index.second() && expr.getValue() == value.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.PUT(source.second(), index.second(), value.second(), expr.getAttributes()));
        }
    }

    // Other

    @Override
    protected Pair<S,Expr> constructBytes(Expr.Bytes expr) {
        return new Pair<>(null, expr);
    }

    @Override
    protected Pair<S,Expr> constructEquals(Expr.Equals expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.EQ(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }

    @Override
    protected Pair<S,Expr> constructNotEquals(Expr.NotEquals expr, Pair<S,Expr> lhs, Pair<S,Expr> rhs) {
        S s = join(lhs.first(), rhs.first());
        if (expr.getLeftHandSide() == lhs.second() && expr.getRightHandSide() == rhs.second()) {
            return new Pair<>(s, expr);
        } else {
            return new Pair<>(s, BoogieFile.NEQ(lhs.second(), rhs.second(), expr.getAttributes()));
        }
    }

    @Override
    protected Pair<S,Expr> constructVariableAccess(Expr.VariableAccess expr) {
        return new Pair<>(null, expr);
    }

    @Override
    protected Pair<S,Expr> constructInvoke(Expr.Invoke expr, List<Pair<S,Expr>> states) {
        S state = join(extractFirst(states));
        if (equals(expr.getArguments(), states)) {
            return new Pair<>(state, expr);
        } else {
            List operands = extractSecond(states);
            return new Pair<>(state, BoogieFile.INVOKE(expr.getName(), operands, expr.getAttributes()));
        }
    }

    protected boolean equals(List<? extends Expr> lhs, List<Pair<S,Expr>> rhs) {
        if(lhs.size() == rhs.size()) {
            for(int i=0;i!=lhs.size();++i) {
                Expr l = lhs.get(i);
                Expr r = rhs.get(i).second();
                if(l != r) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    protected List<S> extractFirst(List<Pair<S,Expr>> items) {
        ArrayList<S> states = new ArrayList<>();
        for(Pair<S,Expr> p : items) {
            states.add(p.first());
        }
        return states;
    }
    protected List<Expr> extractSecond(List<Pair<S,Expr>> items) {
        ArrayList<Expr> states = new ArrayList<>();
        for(Pair<S,Expr> p : items) {
            states.add(p.second());
        }
        return states;
    }
}
