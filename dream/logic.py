# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from sympy import And, Or, Not, Symbol, true, false
from sympy.logic.boolalg import to_cnf, bool_map, simplify_logic
from ir.expressions import ORExpression, ANDExpression, HighLevelCondition, NumericConstant, LocalVariable, LogicalNotExpression, Call


def get_AND_remaining_term(cond_inner, cond_outer):
    """conditions must be in CNF form"""
    args_inner = list(cond_inner.args) if type(cond_inner) == And else [cond_inner]
    args_outer = list(cond_outer.args) if type(cond_outer) == And else [cond_outer]

    if len(args_inner) <= len(args_outer):
        args_outer_str = [str(a) for a in args_outer]
        for arg in args_inner:
            try:
                arg_id = args_outer_str.index(str(arg))
                del args_outer_str[arg_id]
                del args_outer[arg_id]
            except ValueError:
                if not remove_item_if_exists(arg, args_outer):
                    return None
        args_remaining = true
        for arg in args_outer:
            args_remaining = And(args_remaining, arg)
        return to_cnf(args_remaining, simplify=True)
    return None


def remove_item_if_exists(item, items_list):
    for i in range(0, len(items_list)):
        if conditions_equal(item, items_list[i]):
            del items_list[i]
            return True
    return False


def conditions_equal(cond1, cond2):
    if cond1 == cond2:
        return True

    symbols_1 = get_symbols(cond1)
    symbols_2 = get_symbols(cond2)
    if symbols_1.symmetric_difference(symbols_2):
        return False

    cond1_simplified = simplify_logic(cond1)
    cond2_simplified = simplify_logic(cond2)
    if type(cond1_simplified) != type(cond2_simplified):
        return False
    elif len(cond1_simplified.args) != len(cond2_simplified.args):
        return False

    cond_mapping = bool_map(cond1, cond2)
    if type(cond_mapping) != bool:
        for k, v in cond_mapping[1].items():
            if k != v:
                return False
        return True
    return False


def get_symbols(logic_exp):
    symbols = set()
    if isinstance(logic_exp, Symbol):
        symbols.add(logic_exp)
    elif isinstance(logic_exp, Not):
        symbols.update(get_symbols(logic_exp.args[0]))
    elif isinstance(logic_exp, Or) or isinstance(logic_exp, And):
        for arg in logic_exp.args:
            symbols.update(get_symbols(arg))
    else:
        assert logic_exp in [true, false], "unrecognized logic expression type: {0}".format(logic_exp)
    return symbols


def get_arguments_number(cond, ignoreNot=True):
    if ignoreNot:
        if isinstance(cond, Not) and len(cond.args) == 1 and isinstance(cond.args[0], Symbol):
            return 0
    num = 0
    for arg in cond.args:
        num += 1 + get_arguments_number(arg, ignoreNot)
    return num


def in_conditions_list(cond, cond_list):
    for c in cond_list:
        if conditions_equal(c, cond):
            return True
    return False


def is_trivial_condition(condition):
    return condition == true


def has_compound_trivial_condition(condition_list):
    compound_condition = false
    for c in condition_list:
        compound_condition = Or(compound_condition, c)
    return is_trivial_condition(simplify_logic(compound_condition))


def get_negated_condition(exp):
    if isinstance(exp, HighLevelCondition):
        return ~exp
    elif isinstance(exp, ORExpression):
        return ANDExpression([get_negated_condition(op) for op in exp.operands], exp.is_condition)
    elif isinstance(exp, ANDExpression):
        return ORExpression([get_negated_condition(op) for op in exp.operands], exp.is_condition)
    elif isinstance(exp, LogicalNotExpression):
        return exp.operand
    else:
        return LogicalNotExpression(exp)

    #TODO handle later
    #else:
    #    return simplify_logic(Not(exp))
    #    assert False, "unrecognised expression: {0}".format(exp)


def get_condition_from_logic_expression(logic_exp, conditions_map):
    #return logic_exp
    if not isinstance(logic_exp, Symbol) and not isinstance(logic_exp, Not) and not isinstance(logic_exp, Or) \
        and not isinstance(logic_exp, And) and not isinstance(logic_exp, LocalVariable) and not logic_exp == true:
        return logic_exp

    logic_exp = simplify_logic(logic_exp)
    #return logic_exp
    if isinstance(logic_exp, Symbol):
        return conditions_map[logic_exp]
    elif isinstance(logic_exp, Not):
        return get_negated_condition(get_condition_from_logic_expression(logic_exp.args[0], conditions_map))
    elif isinstance(logic_exp, Or):
        return ORExpression([get_condition_from_logic_expression(arg, conditions_map) for arg in logic_exp.args],
                            is_condition=True)
    elif isinstance(logic_exp, And):
        return ANDExpression([get_condition_from_logic_expression(arg, conditions_map) for arg in logic_exp.args],
                             is_condition=True)
    elif logic_exp in [True, true]:
        return NumericConstant(1)
    elif isinstance(logic_exp, LocalVariable):
        return logic_exp
    else:
        assert False, 'unrecognised logic expression{0}'.format(logic_exp)


def alias_free_expression(logic_expr, conditions_map):
    #TODO remove first line
    return logic_expr
    symbols_alias_map = compute_aliases(logic_expr, conditions_map)
    return logic_expr.subs(symbols_alias_map)


def compute_aliases(logic_expr, conditions_map):
    symbols_alias_map = {}
    unique_conditions_map = {}
    for symbol1 in set(get_symbols(logic_expr)):
        condition1 = conditions_map[symbol1]
        alias_found = False
        for symbol2, condition2 in unique_conditions_map.items():
            if condition1 == condition2:
                symbols_alias_map[symbol1] = symbol2
                alias_found = True
                break
            elif condition1.equals_negated(condition2):
                symbols_alias_map[symbol1] = Not(symbol2)
                alias_found = True
                break
        if not alias_found:
            unique_conditions_map[symbol1] = condition1
    return symbols_alias_map

