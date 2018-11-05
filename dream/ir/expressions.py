# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from z3 import *


class Expression(object):
    def __init__(self):
        self.is_signed = False

    def __eq__(self, other):
        pass

    def replace_child_expr(self, old_expr, new_expr):
        pass

    def deep_copy(self):
        pass

    def elements(self):
        return [self]

    @staticmethod
    def is_simple_expr():
        return False

    @staticmethod
    def is_overwritable():
        return False

    @staticmethod
    def is_break_node():
        return False

    @staticmethod
    def is_pure_break():
        return False

    #TODO handle this properly
    def getLeafNodes(self):
        return [self]

    def simplify(self):
        return self

    def to_symbolic(self):
        raise NotImplementedError('{0}: This method is not implemented yet'.format(type(self)))


class LocalVariable(Expression):
    def __init__(self, name, type_=None, show_type=False):
        self.name = name
        self.type = type_
        self.show_type = show_type

    def __str__(self):
        type_str = str(self.type) + " " if self.type is not None or str(self.type)[0] == "#" else 'int '
        return '{0}{1}'.format(type_str if self.show_type else "", str(self.name))

    def __eq__(self, other):
        return isinstance(other, LocalVariable) and self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def deep_copy(self):
        v_copy = LocalVariable(self.name, self.type)
        v_copy.show_type = self.show_type
        return v_copy

    @staticmethod
    def is_simple_expr():
        return True

    @staticmethod
    def is_overwritable():
        return True

    def to_symbolic(self):
        if self.type == 'bool':
            return BitVec(self.name, 1)
        elif self.type == 'char':
            return BitVec(self.name, 8)
        return BitVec(self.name, 32)#Int(self.name)


class GlobalVariable(Expression):
    def __init__(self, name, address):
        self.name = name
        self.address = address

    def __str__(self):
        return str(self.name)

    def __eq__(self, other):
        return isinstance(other, GlobalVariable) and self.name == other.name

    def deep_copy(self):
        return GlobalVariable(self.name, self.address)

    @staticmethod
    def is_simple_expr():
        return True

    @staticmethod
    def is_overwritable():
        return True

    def to_symbolic(self):
        return BitVec(self.name, 32)#Int(self.name)


class Pointer(Expression):
    def __init__(self, address, size_in_bytes=4):
        self.address = address
        self.size_in_bytes = size_in_bytes

    def __str__(self):
        return '*' + parenthesize_unless_simple(self.address)
        '''return "*(" + str(self.address) + ")"
        result = self.array_str()
        result = None
        return result if result is not None else "*(" + str(self.address) + ")"
        '''

    def __eq__(self, other):
        return isinstance(other, Pointer) and self.address == other.address

    def replace_child_expr(self, old_expr, new_expr):
        if self.address == old_expr:
            self.address = new_expr

    def deep_copy(self):
        return Pointer(self.address.deep_copy())

    @staticmethod
    def is_simple_expr():
        return True

    def elements(self):
        return [self] + self.address.elements()

    @staticmethod
    def is_overwritable():
        return True

    def array_str(self):
        if isinstance(self.address, AdditionExpression) and len(self.address.operands) == 2:
            ops = self.address.operands
            if isinstance(ops[0], NumericConstant) and ops[0].value < 100:
                return '{0}[{1}]'.format(str(ops[1]), str(ops[0]))
            elif isinstance(ops[1], NumericConstant) and ops[1].value < 100:
                return '{0}[{1}]'.format(str(ops[0]), str(ops[1]))
        return None


class StringLiteral(Expression):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        if self.value[0] in ["\"", "\'"]:
            return self.value
        return "\"" + self.value + "\""

    def __eq__(self, other):
        return isinstance(other, StringLiteral) and self.value == other.value

    def deep_copy(self):
        return StringLiteral(self.value)

    @staticmethod
    def is_simple_expr():
        return True


class Call(Expression):
    def __init__(self, function_pointer, parameters):
        self.function_pointer = function_pointer
        self.parameters = parameters

    def __str__(self):
        return str(self.function_pointer) + ("(" + self.list_to_str(self.parameters) + ")" if self.parameters else "()")

    def __eq__(self, other):
        if isinstance(other, Call) and len(other.parameters) == len(self.parameters):
            for i in range(0, len(self.parameters)):
                if not (other.parameters[i] == self.parameters[i]):
                    return False
            return True
        return False

    @staticmethod
    def list_to_str(l):
        list_str = ""
        for x in l:
            list_str += str(x) + ", "
        return list_str[:-2]

    def replace_child_expr(self, old_expr, new_expr):
        for idx in range(0, len(self.parameters)):
            if self.parameters[idx] == old_expr:
                self.parameters[idx] = new_expr
                break

    def deep_copy(self):
        return Call(self.function_pointer.deep_copy(), [param.deep_copy() for param in self.parameters])

    def elements(self):
        result = []
        for param in self.parameters:
            result.extend(param.elements())
        return result

    def get_func_name(self):
        return str(self.function_pointer)


class TernaryExpression(Expression):
    def __init__(self, first_operand, second_operand, third_operand):
        self.first_operand = first_operand
        self.second_operand = second_operand
        self.third_operand = third_operand

    def __str__(self):
        return str(self.first_operand) + " ? " + str(self.second_operand) + " : " + str(self.third_operand)

    def __eq__(self, other):
        return isinstance(other, TernaryExpression) and self.first_operand == other.first_operand \
            and self.second_operand == other.second_operand and self.third_operand == other.third_operand

    def replace_child_expr(self, old_expr, new_expr):
        if self.first_operand == old_expr:
            self.first_operand = new_expr
        elif self.second_operand == old_expr:
            self.second_operand = new_expr
        elif self.third_operand == old_expr:
            self.third_operand = new_expr

    def deep_copy(self):
        return TernaryExpression(self.first_operand.deep_copy(),
                                 self.second_operand.deep_copy(),
                                 self.third_operand.deep_copy())

    def elements(self):
        return self.first_operand.elements() + self.second_operand.elements() + self.third_operand.elements()


class UnaryExpression(Expression):
    def __init__(self, operand):
        self.operand = operand

    def replace_child_expr(self, old_expr, new_expr):
        if self.operand == old_expr:
            self.operand = new_expr

    def elements(self):
        return self.operand.elements()


class AddressExpression(UnaryExpression):
    def __init__(self, operand):
        UnaryExpression.__init__(self, operand)

    def __str__(self):
        return '&' + parenthesize_unless_simple(self.operand)

    def __eq__(self, other):
        return isinstance(other, AddressExpression) and self.operand == other.operand

    def deep_copy(self):
        return AddressExpression(self.operand.deep_copy())


class LogicalNotExpression(UnaryExpression):
    def __init__(self, operand):
        UnaryExpression.__init__(self, operand)

    def __str__(self):
        return '!' + parenthesize_unless_simple(self.operand)

    def __eq__(self, other):
        return isinstance(other, LogicalNotExpression) and self.operand == other.operand

    def deep_copy(self):
        return LogicalNotExpression(self.operand.deep_copy())


class BitwiseNOT(UnaryExpression):
    def __init__(self, operand):
        UnaryExpression.__init__(self, operand)

    def __str__(self):
        return '~' + parenthesize_unless_simple(self.operand)

    def __eq__(self, other):
        return isinstance(other, BitwiseNOT) and self.operand == other.operand

    def deep_copy(self):
        return BitwiseNOT(self.operand.deep_copy())


class NegationExpression(UnaryExpression):
    def __init__(self, operand):
        UnaryExpression.__init__(self, operand)

    def __str__(self):
        return '-' + parenthesize_unless_simple(self.operand)

    def __eq__(self, other):
        return isinstance(other, NegationExpression) and self.operand == other.operand

    def deep_copy(self):
        return NegationExpression(self.operand.deep_copy())

    def to_symbolic(self):
        return -1 * self.operand.to_symbolic()


class NumericConstant(Expression):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return hex(self.value) if (type(self.value) == int or type(self.value) == long) and abs(self.value) > 5000 else str(self.value)

    def __eq__(self, other):
        return isinstance(other, NumericConstant) and self.value == other.value

    def __invert__(self):
        return NumericConstant(~self.value)

    def deep_copy(self):
        return NumericConstant(self.value)

    @staticmethod
    def is_simple_expr():
        return True

    def to_symbolic(self):
        return self.value


class HighLevelCondition(Expression):
    def __init__(self, lhs_expression, comparison_string, rhs_expression, is_signed=False):
        if type(lhs_expression) == NumericConstant and type(rhs_expression) != NumericConstant:
            self.lhsExpression = rhs_expression
            self.comparisonString = self.switched_op(comparison_string)
            self.rhsExpression = lhs_expression
        else:
            self.lhsExpression = lhs_expression
            self.comparisonString = comparison_string
            self.rhsExpression = rhs_expression
        self.is_signed = is_signed

    def __str__(self):
        if isinstance(self.rhsExpression, NumericConstant) and self.rhsExpression.value == 0:
            if self.comparisonString == '==' and hasattr(self.lhsExpression, 'type') and self.lhsExpression.type == 'bool':
                return '!{0}'.format(str(self.lhsExpression))
            elif self.comparisonString == '!=' and hasattr(self.lhsExpression, 'type') and self.lhsExpression.type == 'bool':
                return '{0}'.format(str(self.lhsExpression))
        return str(self.lhsExpression) + ' ' + self.comparisonString + ' ' + str(self.rhsExpression)

    def __eq__(self, other):
        if not isinstance(other, HighLevelCondition):
            return False
        return (
                   self.comparisonString == other.comparisonString and
                   self.lhsExpression == other.lhsExpression and
                   self.rhsExpression == other.rhsExpression
               ) or (
                   self.comparisonString == self.switched_op(other.comparisonString) and
                   self.lhsExpression == other.rhsExpression and
                   self.rhsExpression == other.lhsExpression
               )

    def __invert__(self):
        neg_cond = self.deep_copy()
        neg_cond.negate()
        return neg_cond

    def equals_negated(self, other):
        result = False
        if isinstance(other, HighLevelCondition):
            other.negate()
            result = self.__eq__(other)
            other.negate()
        return result

    def does_test_equality_with_scalar(self, testedVariableName=""):
        return self.comparisonString == "==" and isinstance(self.rhsExpression, NumericConstant) \
            and (testedVariableName == str(self.lhsExpression) if testedVariableName != "" else True)

    def does_test_larger_than_scalar(self, testedVariableName=""):
        return (self.comparisonString == ">=" or self.comparisonString == ">") and isinstance(self.rhsExpression, NumericConstant)\
            and (testedVariableName == str(self.lhsExpression) if testedVariableName != "" else True)

    def does_test_smaller_than_scalar(self, testedVariableName=""):
        return (self.comparisonString == "<=" or self.comparisonString == "<") and isinstance(self.rhsExpression, NumericConstant)\
            and (testedVariableName == str(self.lhsExpression) if testedVariableName != "" else True)

    def does_test_equality_with_value(self, tested_variable_name, tested_value):
        return self.comparisonString == "==" and isinstance(self.rhsExpression, NumericConstant)\
            and self.rhsExpression.value == tested_value and str(self.lhsExpression) == tested_variable_name

    def negate(self):
        if self.comparisonString == "==":
            self.comparisonString = "!="
        elif self.comparisonString == "!=":
            self.comparisonString = "=="
        elif self.comparisonString == ">":
            self.comparisonString = "<="
        elif self.comparisonString == ">=":
            self.comparisonString = "<"
        elif self.comparisonString == "<":
            self.comparisonString = ">="
        elif self.comparisonString == "<=":
            self.comparisonString = ">"

    @staticmethod
    def switched_op(op):
        if op == '>':
            return '<'
        elif op == '>=':
            return '<='
        elif op == '<':
            return '>'
        elif op == '<=':
            return '>='
        else:
            return op

    def replace_child_expr(self, old_expr, new_expr):
        if self.lhsExpression == old_expr:
            self.lhsExpression = new_expr
        elif self.rhsExpression == old_expr:
            self.rhsExpression = new_expr

    def deep_copy(self):
        return HighLevelCondition(self.lhsExpression.deep_copy(), self.comparisonString,
                                  self.rhsExpression.deep_copy(), self.is_signed)

    def elements(self):
        return self.lhsExpression.elements() + self.rhsExpression.elements()

    def simplify(self):
        if type(self.rhsExpression) == NumericConstant:
            if type(self.lhsExpression) == AdditionExpression:
                constants = [op.value for op in self.lhsExpression.operands if type(op) == NumericConstant]
                if constants:
                    remaining_ops = [op for op in self.lhsExpression.operands if type(op) != NumericConstant]
                    self.rhsExpression.value -= sum(constants)
                    if len(remaining_ops) > 1:
                        self.lhsExpression.operands = remaining_ops
                    elif len(remaining_ops) == 1:
                        self.lhsExpression = remaining_ops[0]
                    else:
                        return NumericConstant(1 if self.rhsExpression.value == 0 else 1)
        return self

    def to_symbolic(self):
        sym_lhs = self.lhsExpression.to_symbolic()
        sym_rhs = self.rhsExpression.to_symbolic()
        if self.comparisonString == '==':
            return sym_lhs == sym_rhs
        elif self.comparisonString == '!=':
            return sym_lhs != sym_rhs
        elif self.comparisonString == '<':
            return sym_lhs < sym_rhs if self.is_signed else ULT(sym_lhs, sym_rhs)
        elif self.comparisonString == '<=':
            return sym_lhs <= sym_rhs if self.is_signed else ULE(sym_lhs, sym_rhs)
        elif self.comparisonString == '>':
            return sym_lhs > sym_rhs if self.is_signed else UGT(sym_lhs, sym_rhs)
        elif self.comparisonString == '>=':
            return sym_lhs >= sym_rhs if self.is_signed else UGE(sym_lhs, sym_rhs)


class CastExpression(Expression):
    def __init__(self, cast_target, cast_expression):
        self.cast_target = cast_target
        self.cast_expression = cast_expression

    def __str__(self):
        return '(' + self.cast_target + ')' + parenthesize_unless_simple(self.cast_expression)

    def __eq__(self, other):
        return isinstance(other, CastExpression) and self.cast_target == other.cast_target \
            and self.cast_expression == other.cast_expression

    def deep_copy(self):
        return CastExpression(self.cast_target, self.cast_expression.deep_copy())

    def elements(self):
        return self.cast_expression.elements()

    def replace_child_expr(self, old_expr, new_expr):
        if self.cast_expression == old_expr:
            self.cast_expression = new_expr


class NoncommutativeBinaryExpression(Expression):
    def __init__(self, first_operand, second_operand, is_signed=False):
        self.first_operand = first_operand
        self.second_operand = second_operand
        self.is_signed = is_signed

    def replace_child_expr(self, old_expr, new_expr):
        if self.first_operand == old_expr:
            self.first_operand = new_expr
        elif self.second_operand == old_expr:
            self.second_operand = new_expr

    def elements(self):
        return self.first_operand.elements() + self.second_operand.elements()

    def get_operator(self):
        pass


class RemainderExpression(NoncommutativeBinaryExpression):
    def __init__(self, first_operand, second_operand, is_signed=False):
        NoncommutativeBinaryExpression.__init__(self, first_operand, second_operand, is_signed)

    def __str__(self):
        return parenthesize_unless_simple(self.first_operand) + " % " + parenthesize_unless_simple(self.second_operand)

    def __eq__(self, other):
        return isinstance(other, RemainderExpression) and self.first_operand == other.first_operand \
            and self.second_operand == other.second_operand

    def deep_copy(self):
        return RemainderExpression(self.first_operand.deep_copy(), self.second_operand.deep_copy(), self.is_signed)

    def get_operator(self):
        return '%'

    def to_symbolic(self):
        if type(self.second_operand) == NumericConstant and self.second_operand.value == 2:
            return Extract(0, 0, self.first_operand.to_symbolic())

        sym_op1, sym_op2 = self.first_operand.to_symbolic(), self.second_operand.to_symbolic()
        if self.is_signed:
            return sym_op1 % sym_op2
        else:
            return URem(sym_op1, sym_op2)


class ExponentiationExpression(NoncommutativeBinaryExpression):
    def __init__(self, first_operand, second_operand):
        NoncommutativeBinaryExpression.__init__(self, first_operand, second_operand)

    def __str__(self):
        return str(self.first_operand) + " ^ " + str(self.second_operand)

    def __eq__(self, other):
        return isinstance(other, ExponentiationExpression) and self.first_operand == other.first_operand \
            and self.second_operand == other.second_operand

    def deep_copy(self):
        return ExponentiationExpression(self.first_operand.deep_copy(), self.second_operand.deep_copy())


class DivisionExpression(NoncommutativeBinaryExpression):
    def __init__(self, first_operand, second_operand, is_signed=False):
        NoncommutativeBinaryExpression.__init__(self, first_operand, second_operand, is_signed)

    def __str__(self):
        return parenthesize_unless_simple(self.first_operand) + ' / ' + parenthesize_unless_simple(self.second_operand)

    def __eq__(self, other):
        return isinstance(other, DivisionExpression) and self.first_operand == other.first_operand \
            and self.second_operand == other.second_operand

    def deep_copy(self):
        return DivisionExpression(self.first_operand.deep_copy(), self.second_operand.deep_copy(), self.is_signed)

    def get_operator(self):
        return '/'

    def to_symbolic(self):
        sym_op1, sym_op2 = self.first_operand.to_symbolic(), self.second_operand.to_symbolic()
        if self.is_signed:
            return sym_op1 / sym_op2
        else:
            return UDiv(sym_op1, sym_op2)


class ShiftExpression(NoncommutativeBinaryExpression):
    def __init__(self, first_operand, second_operand, shift_operator, is_signed=False):
        NoncommutativeBinaryExpression.__init__(self, first_operand, second_operand, is_signed)
        self.shift_operator = shift_operator

    def __str__(self):
        return parenthesize_unless_simple(self.first_operand) + " {0} ".format(self.shift_operator) \
               + parenthesize_unless_simple(self.second_operand)

    def __eq__(self, other):
        return isinstance(other, ShiftExpression) and self.first_operand == other.first_operand \
            and self.second_operand == other.second_operand and self.shift_operator == other.shift_operator

    def deep_copy(self):
        return ShiftExpression(self.first_operand.deep_copy(), self.second_operand.deep_copy(), self.shift_operator, self.is_signed)

    def get_operator(self):
        return self.shift_operator

    def to_symbolic(self):
        sym_op1, sym_op2 = self.first_operand.to_symbolic(), self.second_operand.to_symbolic()
        print sym_op1, sym_op2
        if self.shift_operator == '>>':
            if self.is_signed:
                return sym_op1 >> sym_op2
            else:
                return LShR(sym_op1, sym_op2)
        else:
            assert self.shift_operator == '<<'
            return sym_op1 << sym_op2


class CommutativeAssociativeExpression(Expression):
    def __init__(self, operands):
        self.operands = operands

    def equal_operands(self, other_operands):
        if len(self.operands) != len(other_operands):
            return False
        other_ops_copy = [op.deep_copy() for op in other_operands]
        for op in self.operands:
            if op in other_ops_copy:
                other_ops_copy.remove(op)
            else:
                break
        return len(other_ops_copy) == 0

    def replace_child_expr(self, old_expr, new_expr):
        index = None
        for idx in range(0, len(self.operands)):
            if self.operands[idx] == old_expr:
                index = idx
                break
        if index is not None:
            if type(new_expr) == type(self):
                del self.operands[index]
                self.operands = self.operands[:index] + new_expr.operands + self.operands[index:]
            else:
                self.operands[index] = new_expr

    def operands_copy(self):
        return [op.deep_copy() for op in self.operands]

    def elements(self):
        result = []
        for op in self.operands:
            result.extend(op.elements())
        return result

    def get_operator(self):
        pass


class AdditionExpression(CommutativeAssociativeExpression):
    def __init__(self, operands):
        CommutativeAssociativeExpression.__init__(self, operands)

    def __str__(self):
        exp_str = ''
        for op in self.operands:
            if isinstance(op, NegationExpression):
                exp_str += ' - ' + parenthesize_unless_simple(op.operand)
            elif isinstance(op, NumericConstant) and op.value < 0:
                neg_op = NumericConstant(-1 * op.value)
                exp_str += ' - ' + str(neg_op)
            else:
                exp_str += ' + ' + parenthesize_unless_simple_or_same_type(op, AdditionExpression)
        return exp_str[3:]

    def __eq__(self, other):
        return isinstance(other, AdditionExpression) and self.equal_operands(other.operands)

    def deep_copy(self):
        return AdditionExpression(self.operands_copy())

    def get_operator(self):
        return '+'

    def to_symbolic(self):
        sym_ops = [op.to_symbolic() for op in self.operands]
        result = sym_ops[0]
        for op in sym_ops[1:]:
            result = result + op
        return result


class MultiplicationExpression(CommutativeAssociativeExpression):
    def __init__(self, operands, is_signed=False):
        CommutativeAssociativeExpression.__init__(self, operands)
        self.is_signed = is_signed

    def __str__(self):
        exp_str = ''
        for op in self.operands:
            exp_str += parenthesize_unless_simple(op) + ' * '
        return exp_str[:-3]

    def __eq__(self, other):
        return isinstance(other, MultiplicationExpression) and self.equal_operands(other.operands)

    def deep_copy(self):
        return MultiplicationExpression(self.operands_copy(), self.is_signed)

    def get_operator(self):
        return '*'


class CommutativeAssociativeLogicExpression(CommutativeAssociativeExpression):
    def __init__(self, operands):
        CommutativeAssociativeExpression.__init__(self, operands)

    def get_unique_operands(self):
        unique_operands = []
        for op in self.operands:
            if op not in unique_operands:
                unique_operands.append(op)
        return unique_operands

    def simplify_operands(self):
        self.operands = [op.simplify() for op in self.operands]

    def simplify_condition(self, other_identity, other_cls):
        try:
            sym = self.to_symbolic()

        except NotImplementedError, e:
            print e.message



        assert type(self) == ORExpression or type(self) == ANDExpression

        self.simplify_operands()
        unique_ops = self.get_unique_operands()
        if len(unique_ops) == 1:
            return unique_ops[0]
        else:
            self.operands = unique_ops

        if any(type(op) == NumericConstant and op.value == other_identity for op in self.operands):
            return NumericConstant(other_identity)
        if any(~op in self.operands for op in self.operands):
            return NumericConstant(other_identity)

        new_ops = [op for op in self.operands if type(op) != NumericConstant]
        if len(new_ops) != len(self.operands):
            if len(new_ops) == 1:
                return new_ops[0]
            else:
                self.operands = new_ops

        if all(type(op) == other_cls for op in self.operands):
            common_ops = [x for x in self.operands[0].operands if all(x in op.operands for op in self.operands[1:])]
            if common_ops:
                common_exp = common_ops[0] if len(common_ops) == 1 else other_cls(common_ops, is_condition=True).simplify()
                remaining_ops = []
                for op in self.operands:
                    sub_ops = [x for x in op.operands if x not in common_ops]
                    remaining_ops.append(sub_ops[0] if len(sub_ops) == 1
                                         else other_cls(sub_ops, is_condition=True).simplify())
                return other_cls([common_exp, self.__class__(remaining_ops, is_condition=True).simplify()],
                                 is_condition=True).simplify()

        return self


class ANDExpression(CommutativeAssociativeLogicExpression):
    def __init__(self, operands, is_condition=False):
        CommutativeAssociativeLogicExpression.__init__(self, operands)
        self.is_condition = is_condition

    def __str__(self):
        exp_str = ''
        for op in self.operands:
            exp_str += parenthesize_unless_simple_or_same_type(op, HighLevelCondition)
            exp_str += ' && ' if self.is_condition else ' & '
        return exp_str[:-4 if self.is_condition else -3]

    def __eq__(self, other):
        return isinstance(other, ANDExpression) and self.equal_operands(other.operands)

    def __invert__(self):
        return ORExpression([~op for op in self.operands], is_condition=self.is_condition)

    def deep_copy(self):
        return ANDExpression(self.operands_copy(), self.is_condition)

    def get_operator(self):
        return '&&' if self.is_condition else '&'

    def simplify(self):
        if not self.is_condition:
            return self

        return self.simplify_condition(0, ORExpression)

        self.simplify_operands()
        unique_ops = self.get_unique_operands()
        if len(unique_ops) == 1:
            return unique_ops[0]
        else:
            self.operands = unique_ops

        if any(type(op) == NumericConstant and op.value == 0 for op in self.operands):
            return NumericConstant(0)
        if any(~op in self.operands for op in self.operands):
            return NumericConstant(0)

        new_ops = [op for op in self.operands if type(op) != NumericConstant]
        if len(new_ops) != len(self.operands):
            return ANDExpression(new_ops, is_condition=True) if len(new_ops) > 1 else new_ops[0]

        if all(type(op) == ORExpression for op in self.operands):
            common_ops = [x for x in self.operands[0].operands if all(x in op.operands for op in self.operands[1:])]
            if common_ops:
                common_exp = common_ops[0] if len(common_ops) == 1 else ORExpression(common_ops, is_condition=True).simplify()
                remaining_ops = []
                for op in self.operands:
                    sub_ops = [x for x in op.operands if x not in common_ops]
                    remaining_ops.append(sub_ops[0] if len(sub_ops) == 1 else ORExpression(sub_ops, is_condition=True).simplify())
                return ORExpression([common_exp, ANDExpression(remaining_ops, is_condition=True).simplify()], is_condition=True).simplify()

        return self

    def to_symbolic(self):
        if self.is_condition:
            return And([op.to_symbolic() for op in self.operands])
        else:
            sym_ops = [op.to_symbolic() for op in self.operands]
            result = sym_ops[0]
            for op in sym_ops[1:]:
                result = result & op
            return result


class ORExpression(CommutativeAssociativeLogicExpression):
    def __init__(self, operands, is_condition=False):
        CommutativeAssociativeLogicExpression.__init__(self, operands)
        self.is_condition = is_condition

    def __str__(self):
        exp_str = ''
        for op in self.operands:
            exp_str += parenthesize_unless_simple_or_same_type(op, HighLevelCondition)
            exp_str += ' || ' if self.is_condition else ' | '
        return exp_str[:-4 if self.is_condition else -3]

    def __eq__(self, other):
        return isinstance(other, ORExpression) and self.equal_operands(other.operands)

    def __invert__(self):
        return ANDExpression([~op for op in self.operands], is_condition=self.is_condition)

    def deep_copy(self):
        return ORExpression(self.operands_copy(), self.is_condition)

    def get_operator(self):
        return '||' if self.is_condition else '|'

    def simplify(self):
        if not self.is_condition:
            return self

        return self.simplify_condition(1, ANDExpression)

        self.operands = [op.simplify() for op in self.operands]
        if any(type(op) == NumericConstant and op.value != 0 for op in self.operands):
            return NumericConstant(1)
        if any(~op in self.operands for op in self.operands):
            return NumericConstant(1)
        new_ops = [op for op in self.operands if type(op) != NumericConstant]
        if len(new_ops) != len(self.operands):
            return ORExpression(new_ops, is_condition=True) if len(new_ops) > 1 else new_ops[0]

        if all(type(op) == ANDExpression for op in self.operands):
            common_ops = [x for x in self.operands[0].operands if all(x in op.operands for op in self.operands[1:])]
            if common_ops:
                common_exp = common_ops[0] if len(common_ops) == 1 else ANDExpression(common_ops, is_condition=True).simplify()
                remaining_ops = []
                for op in self.operands:
                    sub_ops = [x for x in op.operands if x not in common_ops]
                    remaining_ops.append(sub_ops[0] if len(sub_ops) == 1 else ANDExpression(sub_ops, is_condition=True).simplify())
                return ANDExpression([common_exp, ORExpression(remaining_ops, is_condition=True).simplify()], is_condition=True).simplify()
        return self

    def to_symbolic(self):
        if self.is_condition:
            return Or([op.to_symbolic() for op in self.operands])
        else:
            sym_ops = [op.to_symbolic() for op in self.operands]
            result = sym_ops[0]
            for op in sym_ops[1:]:
                result = result | op
            return result


class XORExpression(CommutativeAssociativeLogicExpression):
    def __init__(self, operands):
        CommutativeAssociativeLogicExpression.__init__(self, operands)

    def __str__(self):
        exp_str = ''
        for op in self.operands:
            exp_str += parenthesize_unless_simple(op) + ' ^ '
        return exp_str[:-3]

    def __eq__(self, other):
        return isinstance(other, XORExpression) and self.equal_operands(other.operands)

    def deep_copy(self):
        return XORExpression(self.operands_copy())

    def get_operator(self):
        return '^'


class ArrayIndexing(Expression):
    def __init__(self, array, index):
        self.array = array
        self.index = index

    def __eq__(self, other):
        return isinstance(other, ArrayIndexing) and self.array == other.array and self.index == other.index

    def __str__(self):
        return "%s[%s]" % (str(self.array), str(self.index))

    def replace_child_expr(self, old_expr, new_expr):
        if self.array == old_expr:
            self.array = new_expr
        elif self.index == old_expr:
            self.index = new_expr

    def deep_copy(self):
        return ArrayIndexing(self.array.deep_copy(), self.index.deep_copy())

    def elements(self):
        return self.array.elements() + self.index.elements()

    @staticmethod
    def is_overwritable():
        return True


class MemberAccess(Expression):
    def __init__(self, struct, field, access_operator):
        self.struct = struct
        self.field = field
        self.access_operator = access_operator

    def __eq__(self, other):
        return isinstance(other, MemberAccess) and self.struct == other.struct and self.field == other.field \
            and self.access_operator == other.access_operator

    def __str__(self):
        return "%s%s%s" % (str(self.struct), self.access_operator, str(self.field))

    def replace_child_expr(self, old_expr, new_expr):
        if self.struct == old_expr:
            self.struct = new_expr
        elif self.field == old_expr:
            self.field = new_expr

    def deep_copy(self):
        return MemberAccess(self.struct.deep_copy(), self.field.deep_copy(), self.access_operator)

    def elements(self):
        return self.struct.elements() + self.field.elements()

    @staticmethod
    def is_overwritable():
        return True


class InitializerList(Expression):
    def __init__(self, init_elements):
        self.init_elements = init_elements

    def __str__(self):
        exp_str = "{"
        for e in self.init_elements:
            exp_str += "%s, " % str(e)
        return exp_str[:-2] + "}"

    def elements(self):
        result = []
        for e in self.init_elements:
            result.extend(e.elements())
        return result

    def deep_copy(self):
        return InitializerList([e.deep_copy() for e in self.init_elements])


def parenthesize_unless_simple(expr):
    if expr.is_simple_expr():
        return str(expr)
    else:
        return '(' + str(expr) + ')'


def parenthesize_unless_simple_or_same_type(expr, typ):
    if expr.is_simple_expr() or type(expr) == typ:
        return str(expr)
    else:
        return '(' + str(expr) + ')'