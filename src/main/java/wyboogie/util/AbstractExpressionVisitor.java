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

import wyboogie.core.BoogieFile.Expr;

import java.util.ArrayList;
import java.util.List;

public abstract class AbstractExpressionVisitor<E,L extends E> {

    public E visitExpression(Expr expr) {
        if(expr instanceof Expr.Integer) {
            return constructInteger((Expr.Integer) expr);
        } else if(expr instanceof Expr.Bytes) {
            return constructBytes((Expr.Bytes) expr);
        } else if(expr instanceof Expr.Negation) {
            return visitNegation((Expr.Negation) expr);
        } else if(expr instanceof Expr.Addition) {
            return visitAddition((Expr.Addition) expr);
        } else if(expr instanceof Expr.Subtraction) {
            return visitSubtraction((Expr.Subtraction) expr);
        } else if(expr instanceof Expr.Multiplication) {
            return visitMultiplication((Expr.Multiplication) expr);
        } else if(expr instanceof Expr.Division) {
            return visitDivision((Expr.Division) expr);
        } else if(expr instanceof Expr.IntegerDivision) {
            return visitIntegerDivision((Expr.IntegerDivision) expr);
        } else if(expr instanceof Expr.Remainder) {
            return visitRemainder((Expr.Remainder) expr);
        } else if(expr instanceof Expr.DictionaryAccess) {
            return visitDictionaryAccess((Expr.DictionaryAccess) expr);
        } else if(expr instanceof Expr.DictionaryUpdate) {
            return visitDictionaryUpdate((Expr.DictionaryUpdate) expr);
        } else {
            return visitLogical((Expr.Logical) expr);
        }
    }

    protected List<E> visitExpressions(List<Expr> exprs) {
        List<E> results = new ArrayList<>();
        for (int i = 0; i != exprs.size(); ++i) {
            results.add(visitExpression(exprs.get(i)));
        }
        return results;
    }

    public L visitLogical(Expr expr) {
        //
        if(expr instanceof Expr.Boolean) {
            return constructBoolean((Expr.Boolean) expr);
        } else if(expr instanceof Expr.VariableAccess) {
            return constructVariableAccess((Expr.VariableAccess) expr);
        } else if(expr instanceof Expr.Invoke) {
            return visitInvoke((Expr.Invoke) expr);
        } else if(expr instanceof Expr.Equals) {
            return visitEquals((Expr.Equals) expr);
        } else if(expr instanceof Expr.NotEquals) {
            return visitNotEquals((Expr.NotEquals) expr);
        } else if(expr instanceof Expr.LessThan) {
            return visitLessThan((Expr.LessThan) expr);
        } else if(expr instanceof Expr.LessThanOrEqual) {
            return visitLessThanOrEqual((Expr.LessThanOrEqual) expr);
        } else if(expr instanceof Expr.GreaterThan) {
            return visitGreaterThan((Expr.GreaterThan) expr);
        } else if(expr instanceof Expr.GreaterThanOrEqual) {
            return visitGreaterThanOrEqual((Expr.GreaterThanOrEqual) expr);
        } else if(expr instanceof Expr.LogicalAnd) {
            return visitLogicalAnd((Expr.LogicalAnd) expr);
        } else if(expr instanceof Expr.LogicalOr) {
            return visitLogicalOr((Expr.LogicalOr) expr);
        } else if(expr instanceof Expr.Implies) {
            return visitLogicalImplication((Expr.Implies) expr);
        } else if(expr instanceof Expr.Iff) {
            return visitLogicalIff((Expr.Iff) expr);
        } else if(expr instanceof Expr.LogicalNot) {
            return visitLogicalNot((Expr.LogicalNot) expr);
        } else if(expr instanceof Expr.Old) {
            return visitOld((Expr.Old) expr);
        } else if(expr instanceof Expr.ExistentialQuantifier){
            return visitExistentialQuantifier((Expr.ExistentialQuantifier) expr);
        } else {
            return visitUniversalQuantifier((Expr.UniversalQuantifier) expr);
        }
    }

    protected List<L> visitLogicals(List<Expr.Logical> exprs) {
        List<L> results = new ArrayList<>();
        for (int i = 0; i != exprs.size(); ++i) {
            results.add(visitLogical(exprs.get(i)));
        }
        return results;
    }


    protected E visitDictionaryAccess(Expr.DictionaryAccess expr) {
        E source = visitExpression(expr.getSource());
        E index = visitExpression(expr.getIndex());
        return constructDictionaryAccess(expr, source, index);
    }

    protected E visitDictionaryUpdate(Expr.DictionaryUpdate expr) {
        E source = visitExpression(expr.getSource());
        E index = visitExpression(expr.getIndex());
        E value = visitExpression(expr.getValue());
        return constructDictionaryUpdate(expr, source, index, value);
    }

    protected L visitEquals(Expr.Equals expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructEquals(expr,lhs,rhs);
    }

    protected L visitLessThan(Expr.LessThan expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructLessThan(expr,lhs,rhs);
    }

    protected L visitLessThanOrEqual(Expr.LessThanOrEqual expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructLessThanOrEqual(expr,lhs,rhs);
    }

    protected L visitGreaterThan(Expr.GreaterThan expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructGreaterThan(expr,lhs,rhs);
    }

    protected L visitGreaterThanOrEqual(Expr.GreaterThanOrEqual expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructGreaterThanOrEqual(expr,lhs,rhs);
    }

    protected E visitNegation(Expr.Negation expr) {
        E operand = visitExpression(expr.getOperand());
        return constructNegation(expr,operand);
    }

    protected E visitAddition(Expr.Addition expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructAddition(expr,lhs,rhs);
    }

    protected E visitSubtraction(Expr.Subtraction expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructSubtraction(expr,lhs,rhs);
    }

    protected E visitMultiplication(Expr.Multiplication expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructMultiplication(expr,lhs,rhs);
    }

    protected E visitDivision(Expr.Division expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructDivision(expr,lhs,rhs);
    }

    protected E visitIntegerDivision(Expr.IntegerDivision expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructIntegerDivision(expr,lhs,rhs);
    }

    protected E visitRemainder(Expr.Remainder expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructRemainder(expr,lhs,rhs);
    }

    protected L visitLogicalAnd(Expr.LogicalAnd expr) {
        List<L> operands = visitLogicals(expr.getOperands());
        return constructLogicalAnd(expr,operands);
    }

    protected L visitLogicalImplication(Expr.Implies expr) {
        L lhs = visitLogical(expr.getLeftHandSide());
        L rhs = visitLogical(expr.getRightHandSide());
        return constructLogicalImplication(expr,lhs,rhs);
    }

    protected L visitLogicalIff(Expr.Iff expr) {
        L lhs = visitLogical(expr.getLeftHandSide());
        L rhs = visitLogical(expr.getRightHandSide());
        return constructLogicalIff(expr,lhs,rhs);
    }

    protected L visitLogicalNot(Expr.LogicalNot expr) {
        L source = visitLogical(expr.getOperand());
        return constructLogicalNot(expr,source);
    }

    protected L visitLogicalOr(Expr.LogicalOr expr) {
        List<L> operands = visitLogicals(expr.getOperands());
        return constructLogicalOr(expr,operands);
    }

    protected L visitExistentialQuantifier(Expr.ExistentialQuantifier expr) {
        L body = visitLogical(expr.getBody());
        return constructExistentialQuantifier(expr,body);
    }

    protected L visitUniversalQuantifier(Expr.UniversalQuantifier expr) {
        L body = visitLogical(expr.getBody());
        return constructUniversalQuantifier(expr,body);
    }

    protected L visitInvoke(Expr.Invoke expr) {
        List<E> args = visitExpressions(expr.getArguments());
        return constructInvoke(expr,args);
    }

    protected L visitNotEquals(Expr.NotEquals expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructNotEquals(expr,lhs,rhs);
    }

    protected L visitOld(Expr.Old expr) {
        E operand = visitExpression(expr.getOperand());
        return constructOld(expr,operand);
    }

    protected abstract E constructInteger(Expr.Integer expr);
    protected abstract E constructBytes(Expr.Bytes expr);
    protected abstract E constructDictionaryAccess(Expr.DictionaryAccess expr, E source, E index);
    protected abstract E constructDictionaryUpdate(Expr.DictionaryUpdate expr, E source, E index, E value);
    protected abstract E constructNegation(Expr.Negation expr, E operand);
    protected abstract E constructAddition(Expr.Addition expr, E lhs, E rhs);
    protected abstract E constructSubtraction(Expr.Subtraction expr, E lhs, E rhs);
    protected abstract E constructMultiplication(Expr.Multiplication expr, E lhs, E rhs);
    protected abstract E constructDivision(Expr.Division expr, E lhs, E rhs);
    protected abstract E constructIntegerDivision(Expr.IntegerDivision expr, E lhs, E rhs);
    protected abstract E constructRemainder(Expr.Remainder expr, E lhs, E rhs);
    // logicals
    protected abstract L constructBoolean(Expr.Boolean expr);
    protected abstract L constructGreaterThan(Expr.GreaterThan expr, E lhs, E rhs);
    protected abstract L constructGreaterThanOrEqual(Expr.GreaterThanOrEqual expr, E lhs, E rhs);
    protected abstract L constructEquals(Expr.Equals expr, E lhs, E rhs);
    protected abstract L constructLessThan(Expr.LessThan expr, E lhs, E rhs);
    protected abstract L constructLessThanOrEqual(Expr.LessThanOrEqual expr, E lhs, E rhs);
    protected abstract L constructLogicalAnd(Expr.LogicalAnd expr, List<L> operands);
    protected abstract L constructLogicalImplication(Expr.Implies expr, L lhs, L rhs);
    protected abstract L constructLogicalIff(Expr.Iff expr, L lhs, L rhs);
    protected abstract L constructLogicalNot(Expr.LogicalNot expr, L source);
    protected abstract L constructLogicalOr(Expr.LogicalOr expr, List<L> operands);
    protected abstract L constructExistentialQuantifier(Expr.ExistentialQuantifier expr, L body);
    protected abstract L constructUniversalQuantifier(Expr.UniversalQuantifier expr, L body);
    protected abstract L constructInvoke(Expr.Invoke expr, List<E> operands);
    protected abstract L constructNotEquals(Expr.NotEquals expr, E lhs, E rhs);
    protected abstract L constructOld(Expr.Old expr, E operandexpr);
    protected abstract L constructVariableAccess(Expr.VariableAccess expr);
}
