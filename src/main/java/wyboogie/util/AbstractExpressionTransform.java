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

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Expr;

import java.util.ArrayList;
import java.util.List;

public abstract class AbstractExpressionTransform extends AbstractExpressionVisitor<Expr, Expr.Logical> {
    protected Expr constructInteger(Expr.Integer expr) {
        return expr;
    }
    protected Expr constructBytes(Expr.Bytes expr) {
        return expr;
    }
    @Override
    protected Expr constructDictionaryAccess(Expr.DictionaryAccess expr, Expr source, Expr index) {
        return BoogieFile.GET(source, index, expr.getAttributes());
    }
    @Override
    protected Expr constructNegation(Expr.Negation expr, Expr operand) {
        return BoogieFile.NEG(operand, expr.getAttributes());
    }
    @Override
    protected Expr constructAddition(Expr.Addition expr, Expr lhs, Expr rhs) {
        return BoogieFile.ADD(lhs,rhs,expr.getAttributes());
    }
    @Override
    protected Expr constructSubtraction(Expr.Subtraction expr, Expr lhs, Expr rhs) {
        return BoogieFile.SUB(lhs,rhs,expr.getAttributes());
    }
    @Override
    protected Expr constructMultiplication(Expr.Multiplication expr, Expr lhs, Expr rhs) {
        return BoogieFile.MUL(lhs,rhs,expr.getAttributes());
    }
    @Override
    protected Expr constructDivision(Expr.Division expr, Expr lhs, Expr rhs) {
        return BoogieFile.DIV(lhs,rhs,expr.getAttributes());
    }
    @Override
    protected Expr constructIntegerDivision(Expr.IntegerDivision expr, Expr lhs, Expr rhs) {
        return BoogieFile.IDIV(lhs,rhs,expr.getAttributes());
    }
    @Override
    protected Expr constructRemainder(Expr.Remainder expr, Expr lhs, Expr rhs) {
        return BoogieFile.REM(lhs,rhs,expr.getAttributes());
    }
    protected Expr.Logical constructBoolean(Expr.Boolean expr) {
        return expr;
    }
    @Override
    protected Expr.Logical constructEquals(Expr.Equals expr, Expr lhs, Expr rhs) {
        return BoogieFile.EQ(lhs, rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLessThan(Expr.LessThan expr, Expr lhs, Expr rhs) {
        return BoogieFile.LT(lhs, rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLessThanOrEqual(Expr.LessThanOrEqual expr, Expr lhs, Expr rhs) {
        return BoogieFile.LTEQ(lhs, rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructGreaterThan(Expr.GreaterThan expr, Expr lhs, Expr rhs) {
        return BoogieFile.GT(lhs, rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructGreaterThanOrEqual(Expr.GreaterThanOrEqual expr, Expr lhs, Expr rhs) {
        return BoogieFile.GTEQ(lhs, rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLogicalAnd(Expr.LogicalAnd expr, List<Expr.Logical> operands) {
        return BoogieFile.AND(operands,expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLogicalImplication(Expr.Implies expr, Expr.Logical lhs, Expr.Logical rhs) {
        return BoogieFile.IMPLIES(lhs,rhs,expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLogicalIff(Expr.Iff expr, Expr.Logical lhs, Expr.Logical rhs) {
        return BoogieFile.IFF((Expr.Logical) lhs, (Expr.Logical) rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLogicalNot(Expr.LogicalNot expr, Expr.Logical operand) {
        return BoogieFile.NOT((Expr.Logical)operand,expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructLogicalOr(Expr.LogicalOr expr, List<Expr.Logical> operands) {
        return BoogieFile.OR(operands,expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructExistentialQuantifier(Expr.ExistentialQuantifier expr, Expr.Logical body) {
        return BoogieFile.EXISTS(expr.getParameters(), (Expr.Logical) body, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructUniversalQuantifier(Expr.UniversalQuantifier expr, Expr.Logical body) {
        return BoogieFile.FORALL(expr.getParameters(), (Expr.Logical) body, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructInvoke(Expr.Invoke expr, List<Expr> operands) {
        return BoogieFile.INVOKE(expr.getName(),operands,expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructNotEquals(Expr.NotEquals expr, Expr lhs, Expr rhs) {
        return BoogieFile.NEQ(lhs, rhs, expr.getAttributes());
    }
    @Override
    protected Expr.Logical constructVariableAccess(Expr.VariableAccess expr) {
        return expr;
    }
}
