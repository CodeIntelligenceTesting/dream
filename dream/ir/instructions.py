# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from dream.ir.expressions import AdditionExpression, NumericConstant, Pointer, CommutativeAssociativeExpression, NoncommutativeBinaryExpression, NegationExpression, LocalVariable


class Instruction(object):
    def __init__(self):
        pass

    def replace_child_stmt(self, old_stmt, new_stmt):
        pass

    def deep_copy(self):
        pass

    def defs(self):
        return []

    def uses(self):
        return []

    def elements(self):
        return [self] + self.defs() + self.uses()

    def is_break_node(self):
        return False

    @staticmethod
    def is_pure_break():
        return False

    #TODO handle this properly
    def getLeafNodes(self):
        return [self]


class Assignment(Instruction):
    def __init__(self, lhs_operand, rhs_operand):
        self.lhs_operand = lhs_operand
        self.rhs_operand = rhs_operand

    def __str__(self):
        lhs_str = str(self.lhs_operand)
        if isinstance(self.rhs_operand, CommutativeAssociativeExpression) \
                and self.lhs_operand in self.rhs_operand.operands:
            ops_copy = self.rhs_operand.operands[:]
            ops_copy.remove(self.lhs_operand)
            if len(ops_copy) == 1:
                if isinstance(self.rhs_operand, AdditionExpression):
                    if isinstance(ops_copy[0], NumericConstant):
                        if ops_copy[0].value == 1:
                            return lhs_str + '++'
                        elif ops_copy[0].value == -1:
                            return lhs_str + '--'
                        elif ops_copy[0].value > 0:
                            return lhs_str + ' += ' + str(ops_copy[0])
                        else:
                            return lhs_str + ' -= ' + str(-1 * ops_copy[0].value)
                    elif isinstance(ops_copy[0], NegationExpression):
                        return lhs_str + ' -= ' + str(ops_copy[0].operand)

                return lhs_str + ' {0}= '.format(self.rhs_operand.get_operator()) + str(ops_copy[0])

            rhs_copy = self.rhs_operand.deep_copy()
            rhs_copy.operands = ops_copy
            return lhs_str + ' {0}= '.format(rhs_copy.get_operator()) + str(rhs_copy)
        elif isinstance(self.rhs_operand, NoncommutativeBinaryExpression) \
                and self.lhs_operand == self.rhs_operand.first_operand:
            return lhs_str + ' {0}= '.format(self.rhs_operand.get_operator()) + str(self.rhs_operand.second_operand)
        return lhs_str + " = " + str(self.rhs_operand)

    @staticmethod
    def unary_assignment_str(var, const):
        if const == 1:
            return str(var) + "++"
        elif const == -1:
            return str(var) + "--"
        elif const > 0:
            return str(var) + " += " + str(const)
        else:
            return str(var) + " -= " + str(-1 * const)

    def replace_child_stmt(self, old_stmt, new_stmt):
        if self.lhs_operand == old_stmt:
            self.lhs_operand = new_stmt
        elif self.rhs_operand == old_stmt:
            self.rhs_operand = new_stmt

    def deep_copy(self):
        return Assignment(self.lhs_operand.deep_copy(), self.rhs_operand.deep_copy())

    def defs(self):
        return [self.lhs_operand]

    def uses(self):
        result = self.rhs_operand.elements()
        if isinstance(self.lhs_operand, Pointer):
            result.extend(self.lhs_operand.address.elements())
        return result

    def does_define(self, expr):
        return expr in self.defs()


class Return(Instruction):
    def __init__(self, operand):
        self.operand = operand

    def __str__(self):
        op_str = " " + str(self.operand) if self.operand is not None else ""
        return "return" + op_str

    def replace_child_stmt(self, old_stmt, new_stmt):
        if self.operand == old_stmt:
            self.operand = new_stmt

    def deep_copy(self):
        return Return(self.operand.deep_copy() if self.operand is not None else None)

    def uses(self):
        return self.operand.elements() if self.operand is not None else []


class Break(Instruction):
    def __str__(self):
        return 'break'

    def deep_copy(self):
        return Break()

    def is_break_node(self):
        return True


class VariableDeclaration(Instruction):
    def __init__(self, variable, initial_value=None):
        assert isinstance(variable, LocalVariable)
        self.variable = variable
        self.variable.show_type = True
        self.initial_value = initial_value

    def __str__(self):
        init_str = ''
        if self.initial_value is None and self.variable.type == 'bool':
            init_str = ' = false'
        else:
            if self.variable.type == 'bool' and isinstance(self.initial_value, NumericConstant):
                if self.initial_value.value == 0:
                    init_str = ' = false'
                else:
                    init_str = ' = true'
            elif self.initial_value is not None:
                init_str = ' = ' + hex(self.initial_value)
        return '{0}{1}'.format(str(self.variable), init_str)


class ClassDefinition(Instruction):
    def __init__(self, def_str):
        self.def_str = def_str

    def __str__(self):
        return self.def_str

    def deep_copy(self):
        return ClassDefinition(self.def_str)