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
import java.util.Collections;
import java.util.List;

public abstract class AbstractExpressionProducer<E> {

    public E visitExpression(Expr expr) {
        //
        if(expr instanceof Expr.Integer) {
            return constructInteger((Expr.Integer) expr);
        } else if(expr instanceof Expr.Boolean) {
            return constructBoolean((Expr.Boolean) expr);
        } else if(expr instanceof Expr.Bytes) {
            return constructBytes((Expr.Bytes) expr);
        } else if(expr instanceof Expr.VariableAccess) {
            return constructVariableAccess((Expr.VariableAccess) expr);
        } else if(expr instanceof Expr.Invoke) {
            return visitInvoke((Expr.Invoke) expr);
        } else if(expr instanceof Expr.DictionaryAccess) {
            return visitDictionaryAccess((Expr.DictionaryAccess) expr);
        } else if(expr instanceof Expr.Equals) {
            return visitEquals((Expr.Equals) expr);
        } else if(expr instanceof Expr.LessThan) {
            return visitLessThan((Expr.LessThan) expr);
        } else if(expr instanceof Expr.LessThanOrEqual) {
            return visitLessThanOrEqual((Expr.LessThanOrEqual) expr);
        } else if(expr instanceof Expr.GreaterThan) {
            return visitGreaterThan((Expr.GreaterThan) expr);
        } else if(expr instanceof Expr.GreaterThanOrEqual) {
            return visitGreaterThanOrEqual((Expr.GreaterThanOrEqual) expr);
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
        } else if(expr instanceof Expr.LogicalAnd) {
            return visitLogicalAnd((Expr.LogicalAnd) expr);
        } else if(expr instanceof Expr.LogicalOr) {
            return visitLogicalOr((Expr.LogicalOr) expr);
        } else if(expr instanceof Expr.Implies) {
            return visitLogicalImplication((Expr.Implies) expr);
        } else if(expr instanceof Expr.Iff) {
            return visitLogicalIff((Expr.Iff) expr);
        } else {
            return visitLogicalNot((Expr.LogicalNot) expr);
        }
    }

    protected List<E> visitExpressions(List<? extends Expr> exprs) {
        List<E> results = new ArrayList<>();
        for (int i = 0; i != exprs.size(); ++i) {
            results.add(visitExpression(exprs.get(i)));
        }
        return results;
    }

    protected E visitDictionaryAccess(Expr.DictionaryAccess expr) {
        E source = visitExpression(expr.getSource());
        E index = visitExpression(expr.getIndex());
        return constructDictionaryAccess(expr, source, index);
    }

    protected E visitEquals(Expr.Equals expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructEquals(expr,lhs,rhs);
    }

    protected E visitLessThan(Expr.LessThan expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructLessThan(expr,lhs,rhs);
    }

    protected E visitLessThanOrEqual(Expr.LessThanOrEqual expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructLessThanOrEqual(expr,lhs,rhs);
    }

    protected E visitGreaterThan(Expr.GreaterThan expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructGreaterThan(expr,lhs,rhs);
    }

    protected E visitGreaterThanOrEqual(Expr.GreaterThanOrEqual expr) {
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

    protected E visitLogicalAnd(Expr.LogicalAnd expr) {
        List<E> operands = visitExpressions(expr.getOperands());
        return constructLogicalAnd(expr,operands);
    }

    protected E visitLogicalImplication(Expr.Implies expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructLogicalImplication(expr,lhs,rhs);
    }

    protected E visitLogicalIff(Expr.Iff expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructLogicalIff(expr,lhs,rhs);
    }

    protected E visitLogicalNot(Expr.LogicalNot expr) {
        E source = visitExpression(expr.getOperand());
        return constructLogicalNot(expr,source);
    }

    protected E visitLogicalOr(Expr.LogicalOr expr) {
        List<E> operands = visitExpressions(expr.getOperands());
        return constructLogicalOr(expr,operands);
    }
//
//    protected E visitExistentialQuantifier(Expr.ExistentialQuantifier expr) {
//        Tuple<Decl.StaticVariable> parameters = expr.getParameters();
//        List<E> ranges = new ArrayList<>();
//        for (int i = 0; i != parameters.size(); ++i) {
//            Decl.StaticVariable parameter = parameters.get(i);
//            // NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
//            // be deprecated.
//            Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
//            ranges.add(visitExpression(range.getFirstOperand()));
//            ranges.add(visitExpression(range.getSecondOperand()));
//        }
//        E body = visitExpression(expr.getOperand());
//        return constructExistentialQuantifier(expr,ranges,body);
//    }
//
//    protected E visitUniversalQuantifier(Expr.UniversalQuantifier expr) {
//        Tuple<Decl.StaticVariable> parameters = expr.getParameters();
//        List<E> ranges = new ArrayList<>();
//        for (int i = 0; i != parameters.size(); ++i) {
//            Decl.StaticVariable parameter = parameters.get(i);
//            // NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
//            // be deprecated.
//            Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
//            ranges.add(visitExpression(range.getFirstOperand()));
//            ranges.add(visitExpression(range.getSecondOperand()));
//        }
//        E body = visitExpression(expr.getOperand());
//        return constructUniversalQuantifier(expr,ranges,body);
//    }

    protected E visitInvoke(Expr.Invoke expr) {
        List<E> args = visitExpressions(expr.getArguments());
        return constructInvoke(expr,args);
    }

    protected E visitNotEquals(Expr.NotEquals expr) {
        E lhs = visitExpression(expr.getLeftHandSide());
        E rhs = visitExpression(expr.getRightHandSide());
        return constructNotEquals(expr,lhs,rhs);
    }

    protected E constructInteger(Expr.Integer expr) {
        return BOTTOM();
    }

    protected E constructBoolean(Expr.Boolean expr) {
        return BOTTOM();
    }

    protected E constructBytes(Expr.Bytes expr) {
        return BOTTOM();
    }

    protected E constructDictionaryAccess(Expr.DictionaryAccess expr, E source, E index) {
        return join(source,index);
    }
    protected E constructEquals(Expr.Equals expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructLessThan(Expr.LessThan expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructLessThanOrEqual(Expr.LessThanOrEqual expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructGreaterThan(Expr.GreaterThan expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructGreaterThanOrEqual(Expr.GreaterThanOrEqual expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructNegation(Expr.Negation expr, E operand) {
        return operand;
    }
    protected E constructAddition(Expr.Addition expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructSubtraction(Expr.Subtraction expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructMultiplication(Expr.Multiplication expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructDivision(Expr.Division expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerDivision(Expr.IntegerDivision expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructRemainder(Expr.Remainder expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructLogicalAnd(Expr.LogicalAnd expr, List<E> operands) {
        return join(operands);
    }
    protected E constructLogicalImplication(Expr.Implies expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructLogicalIff(Expr.Iff expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructLogicalNot(Expr.LogicalNot expr, E source) {
        return source;
    }
    protected E constructLogicalOr(Expr.LogicalOr expr, List<E> operands) {
        return join(operands);
    }
    protected E constructExistentialQuantifier(Expr.ExistentialQuantifier expr, List<E> ranges, E body) {
        return join(join(ranges),body);
    }
    protected E constructUniversalQuantifier(Expr.UniversalQuantifier expr, List<E> ranges, E body) {
        return join(join(ranges),body);
    }
    protected E constructInvoke(Expr.Invoke expr, List<E> operands) {
        return join(operands);
    }
    protected E constructNotEquals(Expr.NotEquals expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }

    protected E constructVariableAccess(Expr.VariableAccess expr) {
        return BOTTOM();
    }

    protected abstract E BOTTOM();

    protected abstract E join(E lhs, E rhs);

    protected abstract E join(List<E> operands);
}
