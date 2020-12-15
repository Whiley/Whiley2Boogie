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

import wybs.util.AbstractCompilationUnit;
import wyil.lang.WyilFile;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static wyil.lang.WyilFile.*;

public abstract class AbstractExpressionProducer<E> {

    public E visitExpression(WyilFile.Expr expr) {
        //
        switch (expr.getOpcode()) {
            // Terminals
            case EXPR_constant:
                return constructConstant((WyilFile.Expr.Constant) expr);
            case EXPR_indirectinvoke:
                return visitIndirectInvoke((WyilFile.Expr.IndirectInvoke) expr);
            case EXPR_lambdaaccess:
                return constructLambdaAccess((Expr.LambdaAccess) expr);
            case DECL_lambda:
                return visitLambda((WyilFile.Decl.Lambda) expr);
            case EXPR_staticvariable:
                return constructStaticVariableAccess((Expr.StaticVariableAccess) expr);
            case EXPR_variablecopy:
            case EXPR_variablemove:
                return constructVariableAccess((Expr.VariableAccess) expr);
            // Unary Operators
            case EXPR_cast:
            case EXPR_integernegation:
            case EXPR_is:
            case EXPR_logicalnot:
            case EXPR_logicalexistential:
            case EXPR_logicaluniversal:
            case EXPR_bitwisenot:
            case EXPR_dereference:
            case EXPR_fielddereference:
            case EXPR_new:
            case EXPR_recordaccess:
            case EXPR_recordborrow:
            case EXPR_arraylength:
                return visitUnaryOperator((Expr.UnaryOperator) expr);
            // Binary Operators
            case EXPR_logicalimplication:
            case EXPR_logicaliff:
            case EXPR_equal:
            case EXPR_notequal:
            case EXPR_integerlessthan:
            case EXPR_integerlessequal:
            case EXPR_integergreaterthan:
            case EXPR_integergreaterequal:
            case EXPR_integeraddition:
            case EXPR_integersubtraction:
            case EXPR_integermultiplication:
            case EXPR_integerdivision:
            case EXPR_integerremainder:
            case EXPR_bitwiseshl:
            case EXPR_bitwiseshr:
            case EXPR_arrayaccess:
            case EXPR_arrayborrow:
            case EXPR_arrayrange:
            case EXPR_recordupdate:
            case EXPR_arraygenerator:
                return visitBinaryOperator((Expr.BinaryOperator) expr);
            // Nary Operators
            case EXPR_logicaland:
            case EXPR_logicalor:
            case EXPR_invoke:
            case EXPR_bitwiseand:
            case EXPR_bitwiseor:
            case EXPR_bitwisexor:
            case EXPR_arrayinitialiser:
            case EXPR_recordinitialiser:
            case EXPR_tupleinitialiser:
                return visitNaryOperator((Expr.NaryOperator) expr);
            // Ternary Operators
            case EXPR_arrayupdate:
                return visitTernaryOperator((Expr.TernaryOperator) expr);
            default:
                throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
        }
    }

    protected List<E> visitExpressions(Tuple<Expr> exprs) {
        List<E> results = new ArrayList<>();
        for (int i = 0; i != exprs.size(); ++i) {
            results.add(visitExpression(exprs.get(i)));
        }
        return results;
    }


    protected E visitUnaryOperator(Expr.UnaryOperator expr) {
        switch (expr.getOpcode()) {
            // Unary Operators
            case EXPR_cast:
                return visitCast((Expr.Cast) expr);
            case EXPR_integernegation: {
                return visitIntegerNegation((Expr.IntegerNegation) expr);
            }
            case EXPR_is:
                return visitIs((Expr.Is) expr);
            case EXPR_logicalnot:
                return visitLogicalNot((Expr.LogicalNot) expr);
            case EXPR_logicalexistential:
                return visitExistentialQuantifier((Expr.ExistentialQuantifier) expr);
            case EXPR_logicaluniversal:
                return visitUniversalQuantifier((Expr.UniversalQuantifier) expr);
            case EXPR_bitwisenot:
                return visitBitwiseComplement((Expr.BitwiseComplement) expr);
            case EXPR_dereference:
                return visitDereference((Expr.Dereference) expr);
            case EXPR_fielddereference:
                return visitFieldDereference((Expr.FieldDereference) expr);
            case EXPR_new: {
                return visitNew((Expr.New) expr);
            }
            case EXPR_recordaccess:
            case EXPR_recordborrow:
                return visitRecordAccess((Expr.RecordAccess) expr);
            case EXPR_arraylength: {
                return visitArrayLength((Expr.ArrayLength) expr);
            }
            default:
                throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
        }
    }

    protected E visitBinaryOperator(Expr.BinaryOperator expr) {
        switch (expr.getOpcode()) {
            // Binary Operators
            case EXPR_equal:
                return visitEqual((Expr.Equal) expr);
            case EXPR_notequal:
                return visitNotEqual((Expr.NotEqual) expr);
            case EXPR_logicalimplication:
                return visitLogicalImplication((Expr.LogicalImplication) expr);
            case EXPR_logicaliff:
                return visitLogicalIff((Expr.LogicalIff) expr);
            case EXPR_integerlessthan:
                return visitIntegerLessThan((Expr.IntegerLessThan) expr);
            case EXPR_integerlessequal:
                return visitIntegerLessThanOrEqual((Expr.IntegerLessThanOrEqual) expr);
            case EXPR_integergreaterthan:
                return visitIntegerGreaterThan((Expr.IntegerGreaterThan) expr);
            case EXPR_integergreaterequal:
                return visitIntegerGreaterThanOrEqual((Expr.IntegerGreaterThanOrEqual) expr);
            case EXPR_integeraddition:
                return visitIntegerAddition((Expr.IntegerAddition) expr);
            case EXPR_integersubtraction:
                return visitIntegerSubtraction((Expr.IntegerSubtraction) expr);
            case EXPR_integermultiplication:
                return visitIntegerMultiplication((Expr.IntegerMultiplication) expr);
            case EXPR_integerdivision:
                return visitIntegerDivision((Expr.IntegerDivision) expr);
            case EXPR_integerremainder:
                return visitIntegerRemainder((Expr.IntegerRemainder) expr);
            case EXPR_bitwiseshl:
                return visitBitwiseShiftLeft((Expr.BitwiseShiftLeft) expr);
            case EXPR_bitwiseshr:
                return visitBitwiseShiftRight((Expr.BitwiseShiftRight) expr);
            case EXPR_arraygenerator:
                return visitArrayGenerator((Expr.ArrayGenerator) expr);
            case EXPR_arrayaccess:
            case EXPR_arrayborrow:
                return visitArrayAccess((Expr.ArrayAccess) expr);
            case EXPR_arrayrange:
                return visitArrayRange((Expr.ArrayRange) expr);
            case EXPR_recordupdate:
                return visitRecordUpdate((Expr.RecordUpdate) expr);
            default:
                throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
        }
    }

    protected E visitTernaryOperator(Expr.TernaryOperator expr) {
        switch (expr.getOpcode()) {
            // Ternary Operators
            case EXPR_arrayupdate:
                return visitArrayUpdate((Expr.ArrayUpdate) expr);
            default:
                throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
        }
    }

    protected E visitNaryOperator(Expr.NaryOperator expr) {
        switch (expr.getOpcode()) {
            // Nary Operators
            case EXPR_arrayinitialiser:
                return visitArrayInitialiser((Expr.ArrayInitialiser) expr);
            case EXPR_bitwiseand:
                return visitBitwiseAnd((Expr.BitwiseAnd) expr);
            case EXPR_bitwiseor:
                return visitBitwiseOr((Expr.BitwiseOr) expr);
            case EXPR_bitwisexor:
                return visitBitwiseXor((Expr.BitwiseXor) expr);
            case EXPR_invoke:
                return visitInvoke((Expr.Invoke) expr);
            case EXPR_logicaland:
                return visitLogicalAnd((Expr.LogicalAnd) expr);
            case EXPR_logicalor:
                return visitLogicalOr((Expr.LogicalOr) expr);
            case EXPR_recordinitialiser:
                return visitRecordInitialiser((Expr.RecordInitialiser) expr);
            case EXPR_tupleinitialiser:
                return visitTupleInitialiser((Expr.TupleInitialiser) expr);
            default:
                throw new IllegalArgumentException("unknown expression encountered (" + expr.getClass().getName() + ")");
        }
    }

    protected E visitArrayAccess(Expr.ArrayAccess expr) {
        E source = visitExpression(expr.getFirstOperand());
        E index = visitExpression(expr.getSecondOperand());
        return constructArrayAccess(expr, source, index);
    }

    protected E visitArrayLength(Expr.ArrayLength expr) {
        E source = visitExpression(expr.getOperand());
        return constructArrayLength(expr, source);
    }

    protected E visitArrayGenerator(Expr.ArrayGenerator expr) {
        E value = visitExpression(expr.getFirstOperand());
        E length = visitExpression(expr.getSecondOperand());
        return constructArrayGenerator(expr, value, length);
    }

    protected E visitArrayInitialiser(Expr.ArrayInitialiser expr) {
        List<E> rs = visitExpressions(expr.getOperands());
        return constructArrayInitialiser(expr,rs);
    }

    protected E visitArrayRange(Expr.ArrayRange expr) {
        E start = visitExpression(expr.getFirstOperand());
        E end = visitExpression(expr.getSecondOperand());
        return constructArrayRange(expr, start, end);
    }

    protected E visitArrayUpdate(Expr.ArrayUpdate expr) {
        throw new UnsupportedOperationException();
    }

    protected E visitBitwiseComplement(Expr.BitwiseComplement expr) {
        E operand = visitExpression(expr.getOperand());
        return constructBitwiseComplement(expr,operand);
    }

    protected E visitBitwiseAnd(Expr.BitwiseAnd expr) {
        List<E> operands = visitExpressions(expr.getOperands());
        return constructBitwiseAnd(expr,operands);
    }

    protected E visitBitwiseOr(Expr.BitwiseOr expr) {
        List<E> operands = visitExpressions(expr.getOperands());
        return constructBitwiseOr(expr,operands);
    }

    protected E visitBitwiseXor(Expr.BitwiseXor expr) {
        List<E> operands = visitExpressions(expr.getOperands());
        return constructBitwiseXor(expr,operands);
    }

    protected E visitBitwiseShiftLeft(Expr.BitwiseShiftLeft expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructBitwiseShiftLeft(expr,lhs,rhs);
    }

    protected E visitBitwiseShiftRight(Expr.BitwiseShiftRight expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructBitwiseShiftRight(expr,lhs,rhs);
    }

    protected E visitCast(Expr.Cast expr) {
        E lhs = visitExpression(expr.getOperand());
        return constructCast(expr,lhs);
    }

    protected E visitDereference(Expr.Dereference expr) {
        E operand = visitExpression(expr.getOperand());
        return constructDereference(expr,operand);
    }

    protected E visitFieldDereference(Expr.FieldDereference expr) {
        E operand = visitExpression(expr.getOperand());
        return constructFieldDereference(expr,operand);
    }

    protected E visitEqual(Expr.Equal expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructEqual(expr,lhs,rhs);
    }

    protected E visitIntegerLessThan(Expr.IntegerLessThan expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerLessThan(expr,lhs,rhs);
    }

    protected E visitIntegerLessThanOrEqual(Expr.IntegerLessThanOrEqual expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerLessThanOrEqual(expr,lhs,rhs);
    }

    protected E visitIntegerGreaterThan(Expr.IntegerGreaterThan expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerGreaterThan(expr,lhs,rhs);
    }

    protected E visitIntegerGreaterThanOrEqual(Expr.IntegerGreaterThanOrEqual expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerGreaterThanOrEqual(expr,lhs,rhs);
    }

    protected E visitIntegerNegation(Expr.IntegerNegation expr) {
        E operand = visitExpression(expr.getOperand());
        return constructIntegerNegation(expr,operand);
    }

    protected E visitIntegerAddition(Expr.IntegerAddition expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerAddition(expr,lhs,rhs);
    }

    protected E visitIntegerSubtraction(Expr.IntegerSubtraction expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerSubtraction(expr,lhs,rhs);
    }

    protected E visitIntegerMultiplication(Expr.IntegerMultiplication expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerMultiplication(expr,lhs,rhs);
    }

    protected E visitIntegerDivision(Expr.IntegerDivision expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerDivision(expr,lhs,rhs);
    }

    protected E visitIntegerRemainder(Expr.IntegerRemainder expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructIntegerRemainder(expr,lhs,rhs);
    }

    protected E visitIs(Expr.Is expr) {
        E source = visitExpression(expr.getOperand());
        return constructIs(expr,source);
    }

    protected E visitLambda(Decl.Lambda expr) {
        E source = visitExpression(expr.getBody());
        return constructLambda(expr,source);
    }

    protected E visitLogicalAnd(Expr.LogicalAnd expr) {
        List<E> operands = visitExpressions(expr.getOperands());
        return constructLogicalAnd(expr,operands);
    }

    protected E visitLogicalImplication(Expr.LogicalImplication expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructLogicalImplication(expr,lhs,rhs);
    }

    protected E visitLogicalIff(Expr.LogicalIff expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
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

    protected E visitExistentialQuantifier(Expr.ExistentialQuantifier expr) {
        Tuple<Decl.StaticVariable> parameters = expr.getParameters();
        List<E> ranges = new ArrayList<>();
        for (int i = 0; i != parameters.size(); ++i) {
            Decl.StaticVariable parameter = parameters.get(i);
            // NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
            // be deprecated.
            Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
            ranges.add(visitExpression(range.getFirstOperand()));
            ranges.add(visitExpression(range.getSecondOperand()));
        }
        E body = visitExpression(expr.getOperand());
        return constructExistentialQuantifier(expr,ranges,body);
    }

    protected E visitUniversalQuantifier(Expr.UniversalQuantifier expr) {
        Tuple<Decl.StaticVariable> parameters = expr.getParameters();
        List<E> ranges = new ArrayList<>();
        for (int i = 0; i != parameters.size(); ++i) {
            Decl.StaticVariable parameter = parameters.get(i);
            // NOTE: Currently ranges can only appear in quantifiers. Eventually, this will
            // be deprecated.
            Expr.ArrayRange range = (Expr.ArrayRange) parameter.getInitialiser();
            ranges.add(visitExpression(range.getFirstOperand()));
            ranges.add(visitExpression(range.getSecondOperand()));
        }
        E body = visitExpression(expr.getOperand());
        return constructUniversalQuantifier(expr,ranges,body);
    }

    protected E visitInvoke(Expr.Invoke expr) {
        List<E> args = visitExpressions(expr.getOperands());
        return constructInvoke(expr,args);
    }

    protected E visitIndirectInvoke(Expr.IndirectInvoke expr) {
        E source = visitExpression(expr.getSource());
        List<E> args = visitExpressions(expr.getArguments());
        return constructIndirectInvoke(expr,source,args);
    }

    protected E visitNew(Expr.New expr) {
        E operand = visitExpression(expr.getOperand());
        return constructNew(expr,operand);
    }

    protected E visitNotEqual(Expr.NotEqual expr) {
        E lhs = visitExpression(expr.getFirstOperand());
        E rhs = visitExpression(expr.getSecondOperand());
        return constructNotEqual(expr,lhs,rhs);
    }


    protected E visitRecordAccess(Expr.RecordAccess expr) {
        return visitExpression(expr.getOperand());
    }

    protected E visitRecordInitialiser(Expr.RecordInitialiser expr) {
        Tuple<AbstractCompilationUnit.Identifier> fields = expr.getFields();
        Tuple<Expr> operands = expr.getOperands();
        List<E> args = new ArrayList<>();
        for (int i = 0; i != fields.size(); ++i) {
            Expr operand = operands.get(i);
            args.add(visitExpression(operand));
        }
        return constructRecordInitialiser(expr,args);
    }

    protected E visitRecordUpdate(Expr.RecordUpdate expr) {
        E src = visitExpression(expr.getFirstOperand());
        E val = visitExpression(expr.getSecondOperand());
        return constructRecordUpdate(expr,src,val);
    }

    protected E visitTupleInitialiser(Expr.TupleInitialiser expr) {
        Tuple<Expr> operands = expr.getOperands();
        List<E> args = new ArrayList<>();
        for (int i = 0; i != operands.size(); ++i) {
            Expr operand = operands.get(i);
            args.add(visitExpression(operand));
        }
        return constructTupleInitialiser(expr,args);
    }

    protected E constructArrayAccess(Expr.ArrayAccess expr, E source, E index) {
        return join(source,index);
    }
    protected E constructArrayLength(Expr.ArrayLength expr, E source) {
        return source;
    }
    protected E constructArrayGenerator(Expr.ArrayGenerator expr, E value, E length) {
        return join(value,length);
    }
    protected E constructArrayInitialiser(Expr.ArrayInitialiser expr, List<E> operands) {
        return join(operands);
    }
    protected E constructArrayRange(Expr.ArrayRange expr, E start, E end) {
        return join(start,end);
    }
    protected E constructBitwiseComplement(Expr.BitwiseComplement expr, E operand) {
        return operand;
    }
    protected E constructBitwiseAnd(Expr.BitwiseAnd expr, List<E> operands) {
        return join(operands);
    }
    protected E constructBitwiseOr(Expr.BitwiseOr expr, List<E> operands) {
        return join(operands);
    }
    protected E constructBitwiseXor(Expr.BitwiseXor expr, List<E> operands) {
        return join(operands);
    }
    protected E constructBitwiseShiftLeft(Expr.BitwiseShiftLeft expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructBitwiseShiftRight(Expr.BitwiseShiftRight expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructCast(Expr.Cast expr, E operand) {
        return operand;
    }
    protected E constructConstant(Expr.Constant expr) {
        return BOTTOM();
    }
    protected E constructDereference(Expr.Dereference expr, E operand) {
        return operand;
    }
    protected E constructFieldDereference(Expr.FieldDereference expr, E operand) {
        return operand;
    }
    protected E constructEqual(Expr.Equal expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerLessThan(Expr.IntegerLessThan expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerLessThanOrEqual(Expr.IntegerLessThanOrEqual expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerGreaterThan(Expr.IntegerGreaterThan expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerGreaterThanOrEqual(Expr.IntegerGreaterThanOrEqual expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerNegation(Expr.IntegerNegation expr, E operand) {
        return operand;
    }
    protected E constructIntegerAddition(Expr.IntegerAddition expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerSubtraction(Expr.IntegerSubtraction expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerMultiplication(Expr.IntegerMultiplication expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerDivision(Expr.IntegerDivision expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIntegerRemainder(Expr.IntegerRemainder expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructIs(Expr.Is expr, E operand) {
        return operand;
    }
    protected E constructLogicalAnd(Expr.LogicalAnd expr, List<E> operands) {
        return join(operands);
    }
    protected E constructLogicalImplication(Expr.LogicalImplication expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructLogicalIff(Expr.LogicalIff expr, E lhs, E rhs) {
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
    protected E constructIndirectInvoke(Expr.IndirectInvoke expr, E source, List<E> operands) {
        return join(source,join(operands));
    }
    protected E constructLambda(Decl.Lambda expr, E body) {
        return body;
    }
    protected E constructLambdaAccess(Expr.LambdaAccess expr) {
        return BOTTOM();
    }
    protected E constructNew(Expr.New expr, E operand) {
        return operand;
    }
    protected E constructNotEqual(Expr.NotEqual expr, E lhs, E rhs) {
        return join(lhs,rhs);
    }
    protected E constructRecordInitialiser(Expr.RecordInitialiser expr, List<E> operands) {
        return join(operands);
    }
    protected E constructRecordUpdate(Expr.RecordUpdate expr, E source, E value) {
        return join(source,value);
    }
    protected E constructTupleInitialiser(Expr.TupleInitialiser expr, List<E> operands) {
        return join(operands);
    }

    protected E constructStaticVariableAccess(Expr.StaticVariableAccess expr) {
        return BOTTOM();
    }

    protected E constructVariableAccess(Expr.VariableAccess expr) {
        return BOTTOM();
    }

    protected abstract E BOTTOM();

    protected abstract E join(E lhs, E rhs);

    protected abstract E join(List<E> operands);
}
