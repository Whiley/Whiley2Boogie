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

public abstract class AbstractExpressionFold<E> extends AbstractExpressionVisitor<E,E> {

    @Override
    protected E constructInteger(Expr.Integer expr) {
        return BOTTOM();
    }

    @Override
    protected E constructBoolean(Expr.Boolean expr) {
        return BOTTOM();
    }

    @Override
    protected E constructBytes(Expr.Bytes expr) {
        return BOTTOM();
    }

    @Override
    protected E constructDictionaryAccess(Expr.DictionaryAccess expr, E source, E index) { return join(source, index); }

    @Override
    protected E constructDictionaryUpdate(Expr.DictionaryUpdate expr, E source, E index, E value) {
        return join(source, join(index, value));
    }

    @Override
    protected E constructEquals(Expr.Equals expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructLessThan(Expr.LessThan expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructLessThanOrEqual(Expr.LessThanOrEqual expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructGreaterThan(Expr.GreaterThan expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructGreaterThanOrEqual(Expr.GreaterThanOrEqual expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructNegation(Expr.Negation expr, E operand) {
        return operand;
    }

    @Override
    protected E constructAddition(Expr.Addition expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructSubtraction(Expr.Subtraction expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructMultiplication(Expr.Multiplication expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructDivision(Expr.Division expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructIntegerDivision(Expr.IntegerDivision expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructRemainder(Expr.Remainder expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructLogicalAnd(Expr.LogicalAnd expr, List<E> operands) {
        return join(operands);
    }

    @Override
    protected E constructLogicalImplication(Expr.Implies expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructLogicalIff(Expr.Iff expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructLogicalNot(Expr.LogicalNot expr, E source) {
        return source;
    }

    @Override
    protected E constructLogicalOr(Expr.LogicalOr expr, List<E> operands) {
        return join(operands);
    }

    @Override
    protected E constructExistentialQuantifier(Expr.ExistentialQuantifier expr, E body) {
        return body;
    }

    @Override
    protected E constructUniversalQuantifier(Expr.UniversalQuantifier expr, E body) {
        return body;
    }

    @Override
    protected E constructInvoke(Expr.Invoke expr, List<E> operands) {
        return join(operands);
    }

    @Override
    protected E constructNotEquals(Expr.NotEquals expr, E lhs, E rhs) {
        return join(lhs, rhs);
    }

    @Override
    protected E constructVariableAccess(Expr.VariableAccess expr) {
        return BOTTOM();
    }

    protected abstract E BOTTOM();

    protected abstract E join(E lhs, E rhs);

    protected abstract E join(List<E> operands);
}
