# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import logging

from z3 import *

from dream.ir.expressions import ANDExpression, ORExpression, HighLevelCondition, NumericConstant, \
    AdditionExpression, NegationExpression, RemainderExpression

l = logging.getLogger("dream.z3_transformer")


class Z3Simplifier(object):
    def __init__(self):
        self.variable_map = {}

    def construct_var_map(self, expr):
        self.variable_map = {var.name: var for var in expr.elements() if hasattr(var, 'name')}

    def simplify(self, expr):
        try:
            z3_expr = expr.to_symbolic()
            if z3_expr is True:
                return NumericConstant(1)
            self.construct_var_map(expr)
            result = Then('simplify', 'propagate-values', 'ctx-solver-simplify', 'simplify')(z3_expr)
            return self.z3_to_expr(result.as_expr())
        except NotImplementedError, e:
            print e.message
            return expr
        except Exception, e:
            print e.message
            return expr

    def z3_to_expr(self, z3_expr):
        op_kind = z3_expr.decl().kind()
        if is_app_of(z3_expr, Z3_OP_AND):
            return ANDExpression([self.z3_to_expr(op) for op in z3_expr.children()], is_condition=True)
        elif is_app_of(z3_expr, Z3_OP_OR):
            return ORExpression([self.z3_to_expr(op) for op in z3_expr.children()], is_condition=True)
        elif is_app_of(z3_expr, Z3_OP_BADD):
            return AdditionExpression(self.z3add_args(z3_expr))
        elif is_app_of(z3_expr, Z3_OP_BMUL):
            assert is_int_value(z3_expr.arg(0)) and z3_expr.arg(0).as_long() == -1
            return NegationExpression(self.z3_to_expr(z3_expr.arg(1)))
        elif is_app_of(z3_expr, Z3_OP_EXTRACT):
            return self.z3extract_to_expr(z3_expr)
        elif is_app_of(z3_expr, Z3_OP_BSMOD) or z3_expr.decl().name() == 'bvsmod_i':
            return RemainderExpression(self.z3_to_expr(z3_expr.arg(0)), self.z3_to_expr(z3_expr.arg(1)))
        elif is_distinct(z3_expr):
            return HighLevelCondition(self.z3_to_expr(z3_expr.arg(0)), '!=', self.z3_to_expr(z3_expr.arg(1)))
        elif is_eq(z3_expr):
            return HighLevelCondition(self.z3_to_expr(z3_expr.arg(0)), '==', self.z3_to_expr(z3_expr.arg(1)))
        elif self.is_z3_cmp(z3_expr):
            return self.z3cmp_to_expr(z3_expr)
        elif is_not(z3_expr):
            return ~self.z3_to_expr(z3_expr.arg(0))
        elif is_bv_value(z3_expr):
            return NumericConstant(z3_expr.as_long())
        elif self.is_bv_variable(z3_expr):
            return self.variable_map[z3_expr.decl().name()].deep_copy()
        else:
            l.warning(z3_expr, z3_expr.decl().name(), op_kind)
            raise NotImplementedError('Transformation from z3 to DREAM IR is not implemented')

    def z3add_args(self, z3add):
        return self.z3add_arg(z3add.arg(0)) + self.z3add_arg(z3add.arg(1))

    def z3add_arg(self, z3add_arg):
        args = []
        if is_add(z3add_arg):
            args.extend(self.z3add_args(z3add_arg))
        else:
            args.append(self.z3_to_expr(z3add_arg))
        return args

    def z3extract_to_expr(self, z3_extract):
        high = Z3_get_decl_int_parameter(z3_extract.ctx.ref(), z3_extract.decl().ast, 0)
        low = Z3_get_decl_int_parameter(z3_extract.ctx.ref(), z3_extract.decl().ast, 1)
        if high == 0 and low == 0:
            return RemainderExpression(self.z3_to_expr(z3_extract.arg(0)), NumericConstant(2))
        elif high == 31 and low == 31:
            return HighLevelCondition(self.z3_to_expr(z3_extract.arg(0)), '<', NumericConstant(0))
        else:
            print z3_extract
            raise NotImplementedError('Transformation from z3 to DREAM IR is not implemented')

    def z3cmp_to_expr(self, z3_cmp):
        if self.compares_offset_expr_to_const(z3_cmp):
            decl = z3_cmp.decl().kind()
            if decl == Z3_OP_UGT:
                if is_bv_value(z3_cmp.arg(0)):
                    return self.z3cmp_to_expr(ULT(z3_cmp.arg(1), z3_cmp.arg(0)))
                else:
                    return ~self.z3cmp_to_expr(ULE(z3_cmp.arg(0), z3_cmp.arg(1)))
            elif decl == Z3_OP_UGEQ:
                if is_bv_value(z3_cmp.arg(0)):
                    return self.z3cmp_to_expr(ULE(z3_cmp.arg(1), z3_cmp.arg(0)))
                else:
                    return ~self.z3cmp_to_expr(ULT(z3_cmp.arg(0), z3_cmp.arg(1)))
            elif decl == Z3_OP_ULT:
                if is_bv_value(z3_cmp.arg(0)):
                    return ~self.z3cmp_to_expr(ULE(z3_cmp.arg(1), z3_cmp.arg(0)))
                else:
                    return self.z3cmp_offset(z3_cmp)
            elif decl == Z3_OP_ULEQ:
                if is_bv_value(z3_cmp.arg(0)):
                    return ~self.z3cmp_to_expr(ULT(z3_cmp.arg(1), z3_cmp.arg(0)))
                else:
                    return self.z3cmp_offset(z3_cmp)
            elif decl == Z3_OP_SGT:
                if is_bv_value(z3_cmp.arg(0)):
                    return self.z3cmp_to_expr(z3_cmp.arg(1) < z3_cmp.arg(0))
                else:
                    return ~self.z3cmp_to_expr(z3_cmp.arg(0) <= z3_cmp.arg(1))
            elif decl == Z3_OP_SGEQ:
                if is_bv_value(z3_cmp.arg(0)):
                    return self.z3cmp_to_expr(z3_cmp.arg(1) <= z3_cmp.arg(0))
                else:
                    return ~self.z3cmp_to_expr(z3_cmp.arg(0) < z3_cmp.arg(1))
            elif decl == Z3_OP_SLT:
                if is_bv_value(z3_cmp.arg(0)):
                    return ~self.z3cmp_to_expr(z3_cmp.arg(1) <= z3_cmp.arg(0))
                else:
                    return self.z3cmp_offset(z3_cmp)
            elif decl == Z3_OP_SLEQ:
                if is_bv_value(z3_cmp.arg(0)):
                    return ~self.z3cmp_to_expr(z3_cmp.arg(1) < z3_cmp.arg(0))
                else:
                    return self.z3cmp_offset(z3_cmp)
            else:
                assert False
        else:
            return self.z3_cmp_to_condition(z3_cmp)

    def z3cmp_offset(self, z3_less):
        decl = z3_less.decl().kind()
        z3_add = z3_less.arg(0)
        var, alpha = (z3_add.arg(0), z3_add.arg(1)) if is_bv_value(z3_add.arg(1)) else (z3_add.arg(1), z3_add.arg(0))
        beta = z3_less.arg(1)
        max_val = 1 << alpha.size() if self.is_unsigned_cmp(z3_less) else (1 << (alpha.size() - 1))
        high = BitVecVal(beta.as_long() - alpha.as_long(), alpha.size())
        low = BitVecVal(max_val - alpha.as_long(), alpha.size())

        simplified_expr = None
        if high.as_long() > low.as_long():
            if decl == Z3_OP_ULT:
                simplified_expr = And(UGE(var, low), ULT(var, high))
            elif decl == Z3_OP_ULEQ:
                simplified_expr = And(UGE(var, low), ULE(var, high))
            elif decl == Z3_OP_SLT:
                simplified_expr = And(var >= low, var < high)
            elif decl == Z3_OP_SLEQ:
                simplified_expr = And(var >= low, var <= high)
        else:
            if decl == Z3_OP_ULT:
                simplified_expr = Or(UGE(var, low), ULT(var, high))
            elif decl == Z3_OP_ULEQ:
                simplified_expr = Or(UGE(var, low), ULE(var, high))
            elif decl == Z3_OP_SLT:
                simplified_expr = Or(var >= low, var < high)
            elif decl == Z3_OP_SLEQ:
                simplified_expr = Or(var >= low, var <= high)
        if simplified_expr is not None and self.z3_equivalent(z3_less, simplified_expr):
            return self.z3_to_expr(simplified_expr)
        else:
            return self.z3_cmp_to_condition(z3_less)

    def z3_cmp_to_condition(self, z3cmp_expr):
        expr1 = self.z3_to_expr(z3cmp_expr.arg(0))
        expr2 = self.z3_to_expr(z3cmp_expr.arg(1))
        decl = z3cmp_expr.decl().kind()
        if decl == Z3_OP_UGT:
            return HighLevelCondition(expr1, '>', expr2)
        elif decl == Z3_OP_SGT:
            return HighLevelCondition(expr1, '>', expr2, is_signed=True)
        elif decl == Z3_OP_UGEQ:
            return HighLevelCondition(expr1, '>=', expr2)
        elif decl == Z3_OP_SGEQ:
            return HighLevelCondition(expr1, '>=', expr2, is_signed=True)
        elif decl == Z3_OP_ULT:
            return HighLevelCondition(expr1, '<', expr2)
        elif decl == Z3_OP_SLT:
            return HighLevelCondition(expr1, '<', expr2, is_signed=True)
        elif decl == Z3_OP_ULEQ:
            return HighLevelCondition(expr1, '<=', expr2)
        elif decl == Z3_OP_SLEQ:
            return HighLevelCondition(expr1, '<=', expr2, is_signed=True)
        else:
            assert False

    @staticmethod
    def is_z3_cmp(z3_expr):
        decl = z3_expr.decl().kind()
        return decl == Z3_OP_UGT or decl == Z3_OP_SGT or decl == Z3_OP_UGEQ or decl == Z3_OP_SGEQ or \
               decl == Z3_OP_ULT or decl == Z3_OP_SLT or decl == Z3_OP_ULEQ or decl == Z3_OP_SLEQ

    @staticmethod
    def is_unsigned_cmp(z3_cmp):
        decl = z3_cmp.decl().kind()
        return decl == Z3_OP_UGT or decl == Z3_OP_UGEQ or decl == Z3_OP_ULT or decl == Z3_OP_ULEQ

    @staticmethod
    def z3_equivalent(z3_expr1, z3_expr2):
        s = Solver()
        s.add(z3_expr1 != z3_expr2)
        return s.check() == unsat

    def compares_offset_expr_to_const(self, z3_expr):
        return (is_bv_value(z3_expr.arg(0)) and self.is_offset_expr(z3_expr.arg(1))) or\
               (is_bv_value(z3_expr.arg(1)) and self.is_offset_expr(z3_expr.arg(0)))

    def is_offset_expr(self, z3_expr):
        return z3_expr.decl().kind() == Z3_OP_BADD and\
               ((is_bv_value(z3_expr.arg(0)) and self.is_bv_variable(z3_expr.arg(1))) or
                (is_bv_value(z3_expr.arg(1)) and self.is_bv_variable(z3_expr.arg(0))))

    def is_bv_variable(self, z3_expr):
        return is_bv(z3_expr) and z3_expr.num_args() == 0 and z3_expr.decl().name() in self.variable_map

    def equivalent(self, e1, e2):
        try:
            z3_e1, z3_e2 = e1.to_symbolic(), e2.to_symbolic()
            return self.z3_equivalent(z3_e1, z3_e2)
        except NotImplementedError:
            return False