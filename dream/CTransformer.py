# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import re
import json
from z3 import substitute, simplify, BitVecVal
from z3.z3consts import Z3_OP_TRUE
import itertools
from pyswip import Prolog
from z3.z3types import Z3Exception

from dream.RuleCompiler import RuleID
from dream.ControlFlowTree import SequenceNode, LoopNode, LoopType, ConditionNode, ForNode, CFTNode
from dream.ir.expressions import LocalVariable, Call, GlobalVariable, Pointer, TernaryExpression, AddressExpression, LogicalNotExpression, NegationExpression, HighLevelCondition, RemainderExpression, AdditionExpression, MultiplicationExpression, ANDExpression, ORExpression, XORExpression, NumericConstant, StringLiteral, Expression, CastExpression, DivisionExpression, ShiftExpression, ArrayIndexing, MemberAccess, ExponentiationExpression
from dream.ir.instructions import Return, Assignment, Break, Instruction, VariableDeclaration
from pycparser import c_ast, c_lexer, c_parser
from sympy import true, Symbol, Not, And, Or
from dream.logic import get_symbols, get_negated_condition
from dream.theorem_prover.z3_transformer import Z3Simplifier
from dream.transformations.named_constants import NAMED_CONSTANTS
from dream import config


import logging

l = logging.getLogger("dream.CTransformer")


class ID(object):
    def __init__(self, initial_value=0):
        self.value = initial_value

    def next_id(self):
        self.value += 1
        return self.value

    def reset(self):
        self.value = 0


class CTransformer(object):
    def __init__(self):
        self.ast = None
        self.id_node_map = {}
        self.pre_order = []
        self.names_id_map = {}
        self.variables_map = {}
        self.ordered_variable_names = []
        self.calls = []
        self.ast_facts = []
        self.id_generator = ID()
        with open(config.IMPORTS) as f_imports:
            self.api_functions = json.load(f_imports, encoding='ascii')
        self.prolog_engine = Prolog()
        self.start_prolog_engine()

    def start_prolog_engine(self):
        self.prolog_engine.consult(config.PROLOG['predicates'])
        self.prolog_engine.consult(config.PROLOG['builtin_rules'])
        self.prolog_engine.consult(config.PROLOG['rules'])

    def reset_prolog_engine(self):
        for fact in self.ast_facts:
            self.prolog_engine.retract(fact)
        self.ast_facts = []

    def reset_transformer(self):
        self.id_node_map.clear()
        self.pre_order = []
        self.names_id_map.clear()
        self.variables_map.clear()
        self.ordered_variable_names = []
        self.calls = []
        self.reset_prolog_engine()
        self.id_generator.reset()

    def set_ast(self, ast):
        self.ast = ast
        for param in self.ast.function_signature.parameters:
            param.show_type = True
        self.reset_transformer()

    def remove_side_effects(self, conditions_map):
        self.transform_to_facts_logic_symbols()
        answers = [a for a in self.prolog_engine.query('multiple_symbol_uses(Symbol, Uses)')]
        for answer in answers:
            symbol, uses = Symbol(answer['Symbol']), answer['Uses']
            condition = conditions_map[symbol]

            if True or any(isinstance(expr, Pointer) for expr in condition.elements()) or self.has_side_effects(condition, uses):
                first_use = self.get_first_use(uses)
                self.add_preserving_assignment(symbol, first_use, conditions_map)

    def print_facts(self):
        with open("/home/user/tmp/facts.pl", 'w') as fa:
            for f in self.ast_facts:
                fa.write(f + '.\n')
        return

    def apply_transformations(self):
        done = False
        while not done:
            removed_ids = set()
            done = True
            self.transform_to_facts()
            with open(config.PROLOG['queries'], 'r') as queries:
                for q in queries:
                    answers = [answer for answer in self.prolog_engine.query(q)]
                    for answer in answers:
                        stmt_id = answer[RuleID.INITIAL_ID]
                        parent_id = answer[RuleID.PARENT_ID]
                        children_ids = answer[RuleID.CHILDREN_IDs]

                        ids_to_remove = self.get_ids_to_remove(stmt_id, children_ids)
                        if self.can_apply_transformation(q, answer) and len(removed_ids.intersection(ids_to_remove)) == 0:
                            transform_ast = self.parse_transformation(answer[RuleID.TRANSFORMATION])
                            unification_map = {k: v for (k, v) in answer.items() if k not in [RuleID.TRANSFORMATION,
                                                                                              RuleID.CHILDREN_IDs,
                                                                                              RuleID.INITIAL_ID,
                                                                                              RuleID.PARENT_ID]}
                            transformed_stmt = self.statement_to_IR(transform_ast, unification_map)
                            self.replace_code(stmt_id, parent_id, children_ids, transformed_stmt)
                            removed_ids.update(ids_to_remove)
                            done = False

            if self.apply_builtin_transformations():
                done = False
            if done:
                self.update_variables_types()
                self.rename_variables()
                self.add_declarations()
                self.prolog_engine.consult(config.PROLOG['named_constants_rules'])
                tr = NamedConstantTransformer(self.id_node_map, self.prolog_engine, self.ast)
                tr.apply_transformations()

    def can_apply_transformation(self, query, answer):
        if 'compund_condition' in query:
            try:
                return self.is_condition(self.id_node_map[answer['Condb1']])\
                       and self.is_condition(self.id_node_map[answer['Condb2']])
            except KeyError:
                return False
        return True

    @staticmethod
    def is_condition(exp):
        return type(exp) == HighLevelCondition\
               or (type(exp) == ORExpression and exp.is_condition) \
               or (type(exp) == ANDExpression and exp.is_condition)

    @staticmethod
    def is_simplifiable(cond):
        return not(type(cond) == HighLevelCondition
                   and (hasattr(cond.lhsExpression, 'name') or type(cond.lhsExpression) == NumericConstant)
                   and (hasattr(cond.rhsExpression, 'name') or type(cond.rhsExpression) == NumericConstant))

    def update_variables_types(self):
        for pointer_id in set([a['Pointer'] for a in self.prolog_engine.query('memory_variable(Pointer)')]):
            self.assign_type_to_variable(self.id_node_map[pointer_id].name, 'void *', is_final=False)
            related_ints = set([a['RelatedInteger'] for a in self.prolog_engine.query(
                'related_integer({0}, RelatedInteger)'.format(pointer_id))])
            related_pointers = set([a['RelatedPointer'] for a in self.prolog_engine.query(
                'related_pointer({0}, RelatedPointer)'.format(pointer_id))])
            for v in [self.id_node_map[v_int] for v_int in related_ints]:
                self.assign_type_to_variable(v.name, 'int', is_final=False)
            for v in [self.id_node_map[v_ptr] for v_ptr in related_pointers]:
                self.assign_type_to_variable(v.name, 'void *', is_final=False)

        api_calls = (f for f in self.calls if f[1].get_func_name() in self.api_functions)
        for api_call in api_calls:
            api_type = self.api_functions[api_call[1].get_func_name()]
            parameter_types = [p['type'] for p in api_type['parameters']]
            for param, p_type in zip(api_call[1].parameters, parameter_types):
                if isinstance(param, LocalVariable):
                    self.assign_type_to_variable(param.name, p_type)
                elif type(param) == AddressExpression and p_type[:2] == 'LP' and type(param.operand) == LocalVariable:
                    self.assign_type_to_variable(param.operand.name, p_type[2:])
            ret_type = api_type['return']['type']
            if ret_type:
                parent_id = self.get_parent_id(api_call[0])
                if parent_id != 0:
                    call_parent = self.id_node_map[parent_id]
                    if isinstance(call_parent, Assignment) and isinstance(call_parent.lhs_operand, LocalVariable):
                        self.assign_type_to_variable(call_parent.lhs_operand.name, ret_type)

        for answer in [a for a in self.prolog_engine.query('address_expression_to_pointer(Variable, Def, Uses)')]:
            def_stmt = self.id_node_map[answer['Def']]
            uses_ids = answer['Uses']
            if type(def_stmt) == Assignment and type(uses_ids) == list:
                self.transform_address_expressions_to_pointers(answer['Def'], answer['Uses'])

        self.transform_to_facts()

        for a in list(self.prolog_engine.query('may_array_access(Pointer, Parent)')):
            pointer_exp = self.id_node_map[a['Pointer']]
            pointers, scalars = self.pointer_and_scalar_arguments(pointer_exp.address)
            if pointers is not None:
                if len(pointers) == 1 and hasattr(pointers[0], 'name') and 'char *' in self.get_variable_type(pointers[0]):
                    if len(scalars) == 1:
                        self.replace_code(a['Pointer'], a['Parent'], None, self.transform_to_array_access(pointers[0], scalars[0]))
                    else:
                        self.replace_code(a['Pointer'], a['Parent'], None, self.transform_to_array_access(pointers[0], AdditionExpression(scalars)))
            # TODO check if consistent accesses then array access and divide index by size

        self.transform_to_facts()

    def pointer_and_scalar_arguments(self, add_exp):
        assert isinstance(add_exp, AdditionExpression)
        scalars = []
        pointers = []
        for op in add_exp.operands:
            var_type = self.get_variable_type(op)
            if '*' in var_type:
                pointers.append(op)
            elif var_type == 'int':
                scalars.append(op)
            else:
                return None, None
        return pointers, scalars

    def transform_address_expressions_to_pointers(self, def_id, uses_ids):
        def_stmt = self.id_node_map[def_id]
        self.assign_type_to_variable(def_stmt.lhs_operand.name, 'char *')
        new_var = None
        if type(def_stmt.rhs_operand) == Pointer:
            def_stmt.rhs_operand = def_stmt.rhs_operand.address
            new_var = def_stmt.lhs_operand.deep_copy()
        elif type(def_stmt.rhs_operand) == NumericConstant:
            new_var = def_stmt.lhs_operand.deep_copy()
            def_stmt.lhs_operand = Pointer(def_stmt.lhs_operand)

        if new_var is not None:
            for u in uses_ids:
                self.replace_code(u, self.get_parent_id(u), None, new_var)

    def transform_to_array_access(self, array_expr, index_expr):
        self.add_to_variable_map(array_expr)
        if hasattr(index_expr, 'name'):
            self.add_to_variable_map(index_expr)
        return ArrayIndexing(array_expr, index_expr)

    def assign_type_to_variable(self, var_name, type_, is_final=True):
        if not is_final:
            types = [type_] + list({var.type for var in self.variables_map[var_name]})
            new_type = self.get_most_restricted_type(types)
        else:
            new_type = type_
        for v in self.variables_map[var_name]:
            v.type = new_type

    @staticmethod
    def get_most_restricted_type(types):
        return 'char *' if 'char *' in types or 'char*' in types \
            else 'short *' if 'short *' in types or 'short*' in types \
            else 'int *' if 'int *' in types or 'int*' in types \
            else 'void *' if 'void *' in types or 'void*' in types \
            else 'char' if 'char' in types \
            else 'short' if 'short' in types \
            else types[0]

    def get_variable_type(self, var):
        if hasattr(var, 'name') and hasattr(var, 'type') and var.name in self.variables_map:
            return self.variables_map[var.name][0].type
        elif type(var) == DivisionExpression or type(var) == RemainderExpression or type(var) == ShiftExpression or type(var) == NumericConstant:
            return 'int'
        return 'void'

    def add_declarations(self):
        for var_info in [a for a in self.prolog_engine.query('find_declaration(Variable, Defs, Uses, CommonAncestor)')]:
            var_id = var_info['Variable']
            var = self.id_node_map[var_id]
            if var not in self.ast.function_signature.parameters:
                ancestor_id = var_info['CommonAncestor']
                defs = var_info['Defs'] if type(var_info['Defs']) is list else []
                uses = var_info['Uses'] if type(var_info['Uses']) is list else []
                ancestor = self.id_node_map[ancestor_id]
                if isinstance(ancestor, SequenceNode):
                    children_ids = list(self.prolog_engine.query('sequenceT({0}, _, Children)'.format(ancestor_id)))[0]['Children']
                    in_seq_ancestor = [self.in_sequence_ancestor(n, ancestor_id) for n in defs + uses]
                    first_idx = min([children_ids.index(e) for e in in_seq_ancestor])
                    child_id = children_ids[first_idx]
                    if child_id in defs:
                        declaring_stmt = self.id_node_map[child_id]
                        declaring_stmt.lhs_operand.show_type = True
                    else:
                        initial_value = NumericConstant(0) if var.type == 'bool' else None
                        v_copy = var.deep_copy()
                        self.variables_map[v_copy.name].append(v_copy)
                        declaring_stmt = VariableDeclaration(v_copy, initial_value)
                        ancestor.children.insert(first_idx, declaring_stmt)
                else:
                    if isinstance(ancestor, ForNode):
                        #TODO not finished
                        if self.is_only_used_in_statement(var_id, ancestor_id):
                            ancestor.init[0].lhs_operand.show_type = True
                            continue
                    parent_id = self.get_parent_id(ancestor_id)
                    if parent_id == 0:
                        parent = self.ast.root = SequenceNode(True, [ancestor])
                    else:
                        parent = self.id_node_map[parent_id]
                    while isinstance(parent, Instruction):
                        ancestor = parent
                        parent_id = self.get_parent_id(parent_id)
                        if parent_id == 0:
                            parent = self.ast.root = SequenceNode(True, [ancestor])
                        else:
                            parent = self.id_node_map[parent_id]
                    v_copy = var.deep_copy()
                    self.variables_map[v_copy.name].append(v_copy)
                    if isinstance(parent, SequenceNode):
                        parent.children.insert(parent.children.index(ancestor), VariableDeclaration(v_copy))
                    elif isinstance(parent, LoopNode):
                        parent.body = SequenceNode(true, [VariableDeclaration(v_copy), parent.body])
                    elif isinstance(parent, ConditionNode):
                        if parent.trueChild == ancestor:
                            parent.trueChild = SequenceNode(true, [VariableDeclaration(v_copy), parent.trueChild])
                        elif parent.falseChild == ancestor:
                            parent.falseChild = SequenceNode(true, [VariableDeclaration(v_copy), parent.falseChild])
                        else:
                            continue
                            assert False, str(parent) + ":" + str(ancestor)
                    else:
                        continue
                        assert False, type(parent)

    def is_only_used_in_statement(self, var_id, stmt_id):
        answer = list(self.prolog_engine.query('only_used_in_statement({0}, {1})'.format(var_id, stmt_id)))
        return answer == ['[]']

    def apply_builtin_transformations(self):
        # print 'apply_builtin_transformations'
        done = False
        n = 0
        while not done:
            # print done
            n += 1
            done = True
            self.transform_to_facts()
            if self.propagate_single_defs_single_uses():
                done = False
                self.transform_to_facts()
            if self.propagate_simplify_complex_conditions():
                done = False
                self.transform_to_facts()
            if self.transform_sequences_with_single_statement():
                done = False
                self.transform_to_facts()
            if self.transform_ternary_expression_in_condition():
                done = False
                self.transform_to_facts()
            if self.endless_to_while_loops():
                done = False
                self.transform_to_facts()
            if self.transform_if_do_while_to_while():
                done = False
                self.transform_to_facts()
            if self.transform_do_while_to_while():
                done = False
                self.transform_to_facts()
            # if self.transform_shift_to_div_or_mul():
            #     done = False
            if self.transform_for_loop():
                done = False
        return n != 1

    def transform_sequences_with_single_statement(self):
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('sequenceT(Sequence, Parent, [Child])')]:
            transformation_applied = True
            self.replace_code(answer['Sequence'], answer['Parent'], None, self.id_node_map[answer['Child']].deep_copy())
        return transformation_applied

    def propagate_simplify_complex_conditions(self):
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('set_all_bits_expect_first_and_last(Assign, Parent, V, Exp)')]:
            uses_ids = self.get_uses(answer['V'])
            using_stmts_ids = {self.get_containing_stmt_id(i) for i in uses_ids}
            if len(using_stmts_ids) == 1:
                transformation_applied = True
                self.propagate_expression(uses_ids, answer['Assign'])

        return self.simplify_conditions() or transformation_applied

    def simplify_conditions(self):
        self.transform_to_facts()
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('condition(Cond, Parent)')]:
            cond = self.id_node_map[answer['Cond']]
            if self.is_condition(cond) and self.is_simplifiable(cond):
                simplified_cond = Z3Simplifier().simplify(cond)
                if not(simplified_cond is cond) and not(simplified_cond == cond):
                    transformation_applied = True
                    self.replace_code(answer['Cond'], answer['Parent'], None, simplified_cond)

        if transformation_applied:
            self.transform_to_facts()
        for answer in [a for a in self.prolog_engine.query('equality_comparison(Exp, Parent)')]:
            cmp_exp = self.id_node_map[answer['Exp']]
            assert type(cmp_exp) == HighLevelCondition
            if self.is_condition(cmp_exp.lhsExpression):
                if type(cmp_exp.rhsExpression) == NumericConstant and cmp_exp.rhsExpression.value == 0:
                    if cmp_exp.comparisonString == '!=':
                        simp_exp = cmp_exp.lhsExpression
                        self.replace_code(answer['Exp'], answer['Parent'], None, simp_exp)
                        transformation_applied = True
                    elif cmp_exp.comparisonString == '==':
                        simp_exp = ~cmp_exp.lhsExpression
                        self.replace_code(answer['Exp'], answer['Parent'], None, simp_exp)
                        transformation_applied = True
        return transformation_applied

    def get_defs(self, var_id):
        for use in [u for u in self.prolog_engine.query('definitions({0}, Defs)'.format(var_id))]:
            return use['Defs']

    def get_uses(self, var_id):
        for use in [u for u in self.prolog_engine.query('uses({0}, Uses)'.format(var_id))]:
            return use['Uses']

    def transform_ternary_expression_in_condition(self):
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('condition_with_ternary_operation(Condition, Parent)')]:
            condition = self.id_node_map[answer['Condition']]
            # print 'condition:', str(condition)
            assert isinstance(condition, HighLevelCondition)
            if isinstance(condition.lhsExpression, TernaryExpression):
                ternary_expr, operand = condition.lhsExpression, condition.rhsExpression
            else:
                ternary_expr, operand = condition.rhsExpression, condition.lhsExpression

            parent = self.id_node_map[answer['Parent']]
            if condition.comparisonString == '==':
                if ternary_expr.second_operand == operand:
                    self.replace_expr(parent, condition, ternary_expr.first_operand)
                    transformation_applied = True
                elif ternary_expr.third_operand == operand:
                    self.replace_expr(parent, condition, get_negated_condition(ternary_expr.first_operand))
                    transformation_applied = True
            elif condition.comparisonString == '!=':
                if ternary_expr.second_operand == operand:
                    self.replace_expr(parent, condition, get_negated_condition(ternary_expr.first_operand))
                    transformation_applied = True
                elif ternary_expr.third_operand == operand:
                    self.replace_expr(parent, condition, ternary_expr.first_operand)
                    transformation_applied = True
        return transformation_applied

    @staticmethod
    def replace_expr(parent, old_expr, new_expr):
        if isinstance(parent, Instruction):
            parent.replace_child_stmt(old_expr, new_expr)
        elif isinstance(parent, Expression):
            parent.replace_child_expr(old_expr, new_expr)
        elif isinstance(parent, ConditionNode) or isinstance(parent, LoopNode):
            assert parent.condition == old_expr
            parent.condition = new_expr

    def propagate_single_defs_single_uses(self):
        # self.print_facts()
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('single_def_single_use(Variable, Def, Use)')]:
            # print 'propagate_single_defs_single_uses({0})'.format(str(self.id_node_map[answer['Variable']]))
            def_stmt_id = answer['Def']
            def_stmt = self.id_node_map[def_stmt_id]
            use_stmt_id = answer['Use']
            start_id = def_stmt_id
            # start_id = answer['InSeqStart']
            end_id = use_stmt_id
            while not self.is_cfg_node(end_id):
                end_id = self.get_parent_id(end_id)
            if self.in_neighbours(end_id) == {start_id}:
                transformation_applied = True
                self.propagate_expression(use_stmt_id, def_stmt_id)

            elif all(not isinstance(v, Pointer) for v in def_stmt.uses()):
                overwritable_uses = [u for u in def_stmt.uses() if u.is_overwritable()]
                if not overwritable_uses:
                    self.propagate_expression(use_stmt_id, def_stmt_id)
                    transformation_applied = True
                elif all(isinstance(u, LocalVariable) for u in overwritable_uses):
                    # TODO get all definitions and then check if they exist on a path
                    # print '******* trying ', str(def_stmt)
                    # print '####### uses ', [str(s) for s in overwritable_uses]
                    # print '####### ids ', [self.names_id_map[s.name] for s in overwritable_uses]
                    # print
                    # print 'start_id = ', start_id
                    # print 'end_id = ', end_id
                    # TODO this takes a long time in complex graphs
                    # TODO bug: need to check loops
                    if all(self.is_preserved(u, start_id, end_id) for u in overwritable_uses):
                        transformation_applied = True
                        self.propagate_expression(use_stmt_id, def_stmt_id)

        return transformation_applied

    def propagate_expression(self, use_stmt_id, def_stmt_id):
        #use_stmt = self.id_node_map[use_stmt_id]
        def_stmt = self.id_node_map[def_stmt_id]
        #print '    propagating {0} -> {1}'.format(def_stmt, use_stmt)
        assert isinstance(def_stmt, Assignment)
        use_ids = use_stmt_id if type(use_stmt_id) == list else [use_stmt_id]
        use_stmts = [self.id_node_map[use_id] for use_id in use_ids]
        for use_stmt in use_stmts:
            if isinstance(use_stmt, Instruction):
                use_stmt.replace_child_stmt(def_stmt.lhs_operand, def_stmt.rhs_operand)
            elif isinstance(use_stmt, Expression):
                use_stmt.replace_child_expr(def_stmt.lhs_operand, def_stmt.rhs_operand)
            else:
                assert False
        self.remove_stmt(def_stmt_id)

    def endless_to_while_loops(self):
        transformation_applied = False
        for l in [a for a in self.prolog_engine.query('endless_to_while(Loop, NegatedCondition)')]:
            loop = self.id_node_map[l['Loop']]
            loop.type = LoopType.PRE_TESTED
            loop.condition = get_negated_condition(self.id_node_map[l['NegatedCondition']])
            del loop.body.children[0]
            transformation_applied = True
        return transformation_applied

    def transform_for_loop(self):
        transformation_applied = False
        for for_loop in self.find_for_loops():
            counter_variables = self.get_for_loop_counter_variables(for_loop['ForVariableList'])
            if counter_variables:
                transformation_applied = True
                loop_id = for_loop['ForLoop']
                while_loop = self.id_node_map[loop_id]
                for_node = ForNode([], while_loop.condition, [], while_loop.body)
                for v in counter_variables:
                    for_node.init.append(self.id_node_map[v[1]])
                    self.remove_stmt(v[1])
                    next_stmt = self.id_node_map[v[3]]
                    for_node.next.append(next_stmt)
                    for_node.body.children.remove(next_stmt)
                    transformation_applied = True
                self.replace_code(loop_id, self.get_parent_id(loop_id), None, for_node)

        return transformation_applied

    def find_for_loops(self):
        return [for_loop for for_loop in self.prolog_engine.query('for_loop(ForLoop, ForVariableList)')]

    def get_for_loop_counter_variables(self, counter_candidates):
        counter_variables = []
        for v in counter_candidates:
            after_init_stmts = v[2] if type(v[2]) == list else []
            after_update_stmts = v[4] if type(v[4]) == list else []
            if self.can_propagate_definition_through_statements(v[1], after_init_stmts) \
                    and self.can_propagate_definition_through_statements(v[3], after_update_stmts):
                counter_variables.append(v)
        return counter_variables

    def transform_if_do_while_to_while(self):
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('if_do_while(ParentId, If, DoWhile)')]:
            do_while = self.id_node_map[answer['DoWhile']]
            if_stmt = self.id_node_map[answer['If']]
            if do_while.condition == if_stmt.condition:
                do_while.type = LoopType.PRE_TESTED
                self.replace_code(answer['If'], answer['ParentId'], None, do_while)
                transformation_applied = True

        for answer in [a for a in self.prolog_engine.query('if_do_while_init(ParentId, If, DoWhile)')]:
            do_while = self.id_node_map[answer['DoWhile']]
            do_while.type = LoopType.PRE_TESTED
            self.replace_code(answer['If'], answer['ParentId'], None, do_while)
            transformation_applied = True

        return transformation_applied

    def transform_do_while_to_while(self):
        transformation_applied = False
        for answer in [a for a in self.prolog_engine.query('do_while_to_while(ParentId, DoWhile, Init)')]:
            try:
                do_while_stmt = self.id_node_map[answer['DoWhile']]
                init_stmt = self.id_node_map[answer['Init']]
                z3_cond = do_while_stmt.condition.to_symbolic()
                assert isinstance(init_stmt, Assignment)
                z3_lhs = init_stmt.lhs_operand.to_symbolic()
                z3_rhs = BitVecVal(init_stmt.rhs_operand.value, z3_lhs.size())
                e = substitute(z3_cond, (z3_lhs, z3_rhs))
                if simplify(e).decl().kind() == Z3_OP_TRUE:
                    do_while_stmt.type = LoopType.PRE_TESTED
                    transformation_applied = True
            except Z3Exception:
                pass
            except NotImplementedError:
                pass
        return transformation_applied

    def transform_shift_to_div_or_mul(self):
        for answer in [a for a in self.prolog_engine.query('shift_expression(Shift, ParentId)')]:
            shift_expr = self.id_node_map[answer['Shift']]
            assert isinstance(shift_expr, ShiftExpression)
            op1 = shift_expr.first_operand.deep_copy()
            op2 = NumericConstant(2 ** shift_expr.second_operand.value)
            if shift_expr.shift_operator == '<<':
                equiv_expr = MultiplicationExpression([op1, op2], shift_expr.is_signed)
            else:
                equiv_expr = DivisionExpression(op1, op2, shift_expr.is_signed)
            if Z3Simplifier().equivalent(shift_expr, equiv_expr):
                self.replace_code(answer['Shift'], answer['ParentId'], None, equiv_expr)

        return False

    def can_propagate_definition_through_statements(self, def_stmt_id, intermediate_stmt_ids):
        def_stmt_uses = [u for u in self.id_node_map[def_stmt_id].uses() if u.is_overwritable()]
        if def_stmt_uses:
            if all(isinstance(u, LocalVariable) for u in def_stmt_uses):
                uses_ids = [self.local_variable_id(u.name) for u in def_stmt_uses]
                return len([ans for ans in self.prolog_engine.query('variables_dead_in_statements({0}, {1})'.format(
                    self.list_to_string(uses_ids), self.list_to_string(intermediate_stmt_ids)
                ))]) > 0
            return False
        return True

    def local_variable_id(self, name):
        return self.prolog_engine.query('localT(Id, _, {0})'.format('\'' + name + '\'')).next()['Id']

    def in_neighbours(self, node_id):
        return set(self.prolog_engine.query('in_neighbours({0}, InNeighbours)'.format(node_id)).next()['InNeighbours'])

    def is_cfg_node(self, node_id):
        return len([a for a in self.prolog_engine.query('cfg_edge(P, {0})'.format(node_id))]) > 0

    def is_preserved(self, var, from_id, to_id):
        var_id = self.names_id_map[var.name]
        for stmt_id in [self.containing_instruction_id(u) for u in self.non_preserving_uses(var_id)]:
            if self.exists_on_path(stmt_id, from_id, to_id):
                return False
        return True

    def exists_on_path(self, stmt_id, from_id, to_id):
        answers = [a for a in self.prolog_engine.query('exists_on_path({0}, {1}, {2})'.format(stmt_id, from_id, to_id))]
        return len(answers) > 0

    def containing_instruction_id(self, expr_id):
        parent_id = expr_id
        stmt = self.id_node_map[parent_id]
        while not isinstance(stmt, Instruction) and not isinstance(stmt, Call) and not isinstance(stmt, CFTNode):
            parent_id = self.get_parent_id(parent_id)
            stmt = self.id_node_map[parent_id]
        return parent_id

    def non_preserving_uses(self, var_id):
        answers = [a for a in self.prolog_engine.query('non_preserving_use({0}, NonPreservingUse)'.format(var_id))]
        if answers:
            return [a['NonPreservingUse'] for a in answers]
        return []

    # @staticmethod
    # def is_preserved(var_def_stmt, by_statements):
    #     used_elements = var_def_stmt.uses()
    #     for stmt in by_statements:
    #         if isinstance(stmt, Assignment):
    #             if any(stmt.does_define(u) for u in used_elements):
    #                 return False
    #     return True

    def get_first_use(self, uses):
        return self.pre_order[min([self.pre_order.index(u) for u in uses])]

    def get_last_use(self, uses):
        return self.pre_order[max([self.pre_order.index(u) for u in uses])]

    def get_parent_id(self, node_id):
        # TODO problems when parent id is zero
        answers = [a for a in self.prolog_engine.query('parent_node({0}, ParentId)'.format(node_id))]
        assert len(answers) == 1
        return answers[0]['ParentId']

    def get_containing_stmt_id(self, exp_id):
        assert isinstance(self.id_node_map[exp_id], Expression)
        parent_id = self.get_parent_id(exp_id)
        while isinstance(self.id_node_map[parent_id], Expression):
            parent_id = self.get_parent_id(parent_id)
        return parent_id

    def has_side_effects(self, condition, uses):
        start_id = self.nearest_common_ancestor(uses)
        first_use = self.get_first_use(uses)
        if isinstance(self.id_node_map[start_id], SequenceNode):
            start_id = self.in_sequence_ancestor(first_use, start_id)
        middle_nodes = set()
        for u in set(uses) - {first_use}:
            middle_nodes.update(self.get_middle_nodes_not_passing_by(start_id, u, first_use))
            middle_nodes.update(self.get_middle_nodes(first_use, u))

        overwritable_elements = [e for e in condition.elements() if e.is_overwritable()]
        for stmt_id in [i for i in middle_nodes if isinstance(self.id_node_map[i], Instruction)]:
            stmt = self.id_node_map[stmt_id]
            if isinstance(stmt, Assignment):
                lhs = stmt.lhs_operand
                assert lhs.is_overwritable(), 'left-hand side of assignment is not overwritable'
                if self.have_common_elements(overwritable_elements, lhs.elements()):
                    return not self.is_def_free_path(stmt_id, first_use, lhs)

        return False

    def is_def_free_path(self, def_id, use_id, var):
        if type(var) != LocalVariable:
            return False

        middle_nodes = self.get_middle_nodes(def_id, use_id)
        if middle_nodes:
            return not any(type(self.id_node_map[i]) == Assignment and self.id_node_map[i].lhs_operand == var
                           for i in middle_nodes)
        return False

    @staticmethod
    def have_common_elements(expr_list1, expr_list2):
        for expr in expr_list1:
            if expr in expr_list2:
                return True
        return False

    def in_sequence_ancestor(self, node_id, sequence_id):
        answers = [a for a in self.prolog_engine.query('in_sequence_ancestor({0}, {1}, Ancestor)'.format(sequence_id,
                                                                                                         node_id))]
        assert len(answers) == 1
        return answers[0]['Ancestor']

    def nearest_common_ancestor(self, node_ids):
        #print 'node ids: {0}'.format(node_ids)
        answers = [a for a in self.prolog_engine.query('nearest_common_ancestor({0}, CommonAncestor)'.format(
            self.list_to_string(node_ids)))]
        #print answers
        assert len(answers) == 1
        #print 'CommonAncestor{0} = {1}'.format(self.list_to_string(node_ids), answers[0]['CommonAncestor'])
        return answers[0]['CommonAncestor']

    def get_middle_nodes(self, source_id, target_id):
        #print 'get_middle_statements({0}, {1}, {2})'.format(source_id, target_id)
        middle_ids = self.prolog_engine.query('middle_nodes({0}, {1}, NodeSet)'.format(
            source_id, target_id)).next()['NodeSet']
        return set(middle_ids) if type(middle_ids) == list else set()
        #return [self.id_node_map[i] for i in middle_ids if isinstance(self.id_node_map[i], Instruction)]

    def get_middle_nodes_not_passing_by(self, source_id, target_id, not_passing_by_id):
        #print 'get_middle_statements({0}, {1}, {2})'.format(source_id, target_id, not_passing_by_id)
        middle_ids = self.prolog_engine.query('middle_nodes_not_passing_by({0}, {1}, {2}, NodeSet)'.format(
            source_id, target_id, not_passing_by_id)).next()['NodeSet']
        return set(middle_ids) if type(middle_ids) == list else set()

    def add_preserving_assignment(self, symbol, first_use_id, condition_map):
        parent_id = self.get_parent_id(first_use_id)
        using_stmt = self.id_node_map[parent_id]
        assert isinstance(using_stmt, ConditionNode) or isinstance(using_stmt, LoopNode)
        var_name = 'cond_' + str(symbol)
        bool_var = LocalVariable(var_name, 'bool')
        preserving_assignment = Assignment(bool_var, condition_map[symbol])
        condition_map[symbol] = HighLevelCondition(bool_var.deep_copy(), '!=', NumericConstant(0))
        if isinstance(using_stmt, LoopNode) and using_stmt.type == LoopType.POST_TESTED:
            if isinstance(using_stmt.body, SequenceNode):
                using_stmt.body.children.append(preserving_assignment)
            else:
                using_stmt.body = SequenceNode(None, [using_stmt.body, preserving_assignment])
        else:
            using_stmt_parent = self.id_node_map[self.get_parent_id(parent_id)]
            if isinstance(using_stmt_parent, SequenceNode):
                using_stmt_parent.children.insert(using_stmt_parent.children.index(using_stmt), preserving_assignment)
            elif isinstance(using_stmt_parent, LoopNode):
                using_stmt_parent.body = SequenceNode(None, [preserving_assignment, using_stmt_parent.body])
            elif isinstance(using_stmt_parent, ConditionNode):
                if using_stmt == using_stmt_parent.trueChild:
                    using_stmt_parent.trueChild = SequenceNode(None,
                                                               [preserving_assignment, using_stmt_parent.trueChild])
                else:
                    using_stmt_parent.falseChild = SequenceNode(None,
                                                                [preserving_assignment, using_stmt_parent.falseChild])
            else:
                assert False
        #TODO remove later only for evaluation
        #return bool_var

    def transform_to_facts_logic_symbols(self):
        self.reset_transformer()
        root_id = self.id_generator.next_id()
        self.add_cfg_edge_fact(0, root_id)
        self.ast_node_facts_logic_symbols(self.ast.root, root_id, 0, None, None)
        # print self.cfg_edges
        # for v in self.variables_map:
        #     print v, ": ", len(self.variables_map[v])
        # with open('/home/yakdan/Bilder/pl/preorder', 'w') as pre:
        #     for i in self.pre_order:
        #         pre.write('{0}\n'.format(i))
        #f = open('/home/yakdan/Bilder/pl/facts.pl', 'w')
        for fact in self.ast_facts:
            #f.write('{0}.\n'.format(fact))
            self.prolog_engine.assertz(fact)
        #f.close()

    def ast_node_facts_logic_symbols(self, ast_node, ast_node_id, parent_id, successor_id=None, enclosing_loop_successor_id=None):
        if ast_node is not None:
            self.add_parent_fact(ast_node_id, parent_id)
            self.pre_order.append(ast_node_id)

            """if len(self.pre_order) >= 2:
                self.add_fact('pre_order_next({0}, {1})'.format(self.pre_order[-2], self.pre_order[-1]))"""
        self.id_node_map[ast_node_id] = ast_node

        if isinstance(ast_node, SequenceNode):
            '''sequenceT(id, parent_id, [statement_1, ...])'''
            stmt_ids = [self.id_generator.next_id() for c in ast_node.children]
            self.add_fact('sequenceT({0}, {1}, {2})'.format(ast_node_id, parent_id, self.list_to_string(stmt_ids)))
            #print stmt_ids
            self.add_cfg_edge_fact(ast_node_id, stmt_ids[0])
            for idx in range(0, len(stmt_ids)):
                self.ast_node_facts_logic_symbols(ast_node.children[idx], stmt_ids[idx], ast_node_id,
                                                  stmt_ids[idx + 1] if idx < len(stmt_ids) - 1 else successor_id,
                                                  enclosing_loop_successor_id)

        elif isinstance(ast_node, LoopNode):
            '''loopT(id, parent, 'type', condition, body)'''
            symbol_id_map = {}
            for s in get_symbols(ast_node.condition):
                symbol_id_map[self.id_generator.next_id()] = str(s)
            body_id = self.id_generator.next_id()
            cond_id = self.id_generator.next_id()
            self.add_fact('loopT({0}, {1}, \'{2}\', {3}, {4})'.format(ast_node_id, parent_id,
                                                                      self.loop_type_to_string(ast_node.type),
                                                                      cond_id,
                                                                      body_id))
            self.add_fact('logicExpressionT({0}, {1}, {2})'.format(cond_id, ast_node_id,
                                                                   self.list_to_string(symbol_id_map.keys())))
            #self.add_parent_fact(cond_id, ast_node_id)
            if ast_node.type == LoopType.POST_TESTED:
                self.add_cfg_edge_fact(ast_node_id, body_id)
                self.ast_node_facts_logic_symbols(ast_node.body, body_id, ast_node_id, cond_id, successor_id)
                self.ast_node_facts_logic_symbols(ast_node.condition, cond_id, ast_node_id)
            else:
                self.add_cfg_edge_fact(ast_node_id, cond_id)
                self.ast_node_facts_logic_symbols(ast_node.condition, cond_id, ast_node_id)
                self.ast_node_facts_logic_symbols(ast_node.body, body_id, ast_node_id, cond_id, successor_id)

            self.logic_symbols_facts(symbol_id_map, cond_id)
            self.add_cfg_edge_fact(cond_id, body_id)
            self.add_cfg_edge_fact(cond_id, successor_id)

        elif isinstance(ast_node, ConditionNode):
            '''ifT(id, parent, condition, trueBranch, falseBranch)'''
            symbol_id_map = {}
            for s in get_symbols(ast_node.condition):
                symbol_id_map[self.id_generator.next_id()] = str(s)

            cond_id = self.id_generator.next_id()
            true_id = self.id_generator.next_id() if ast_node.trueChild is not None else '\'null\''
            false_id = self.id_generator.next_id() if ast_node.falseChild is not None else '\'null\''
            self.add_fact('ifT({0}, {1}, {2}, {3}, {4})'.format(ast_node_id, parent_id,
                                                                cond_id, true_id, false_id))

            self.add_fact('logicExpressionT({0}, {1}, {2})'.format(cond_id, ast_node_id,
                                                                   self.list_to_string(symbol_id_map.keys())))
            #self.add_parent_fact(cond_id, ast_node_id)
            self.add_cfg_edge_fact(ast_node_id, cond_id)
            if ast_node.trueChild is not None:
                self.add_cfg_edge_fact(cond_id, true_id)
                #self.add_cfg_edge_fact(true_id, successor_id)
            else:
                self.add_cfg_edge_fact(cond_id, successor_id)
            if ast_node.falseChild is not None:
                self.add_cfg_edge_fact(cond_id, false_id)
                #self.add_cfg_edge_fact(false_id, successor_id)
            else:
                self.add_cfg_edge_fact(cond_id, successor_id)
            self.logic_symbols_facts(symbol_id_map, cond_id)
            self.ast_node_facts_logic_symbols(ast_node.condition, cond_id, ast_node_id)
            self.ast_node_facts_logic_symbols(ast_node.trueChild, true_id, ast_node_id,
                                              successor_id, enclosing_loop_successor_id)
            self.ast_node_facts_logic_symbols(ast_node.falseChild, false_id, ast_node_id,
                                              successor_id, enclosing_loop_successor_id)
        elif isinstance(ast_node, Instruction) or isinstance(ast_node, Call):
            if isinstance(ast_node, Break):
                self.add_cfg_edge_fact(ast_node_id, enclosing_loop_successor_id)
            else:
                self.add_cfg_edge_fact(ast_node_id, successor_id)
        elif isinstance(ast_node, CastExpression) or isinstance(ast_node, LocalVariable):
            #TODO remove this only for evaluation
            self.add_cfg_edge_fact(ast_node_id, successor_id)
        else:
            assert ast_node is None or isinstance(ast_node, Symbol) or isinstance(ast_node, Not) or\
                   isinstance(ast_node, And) or isinstance(ast_node, Or) or ast_node == True,\
                'no transformation to facts possible: {0}'.format(str(ast_node))

    def add_cfg_edge_fact(self, source_id, target_id):
        if target_id is not None:
            #if source_id not in self.cfg_edges:
            #    self.cfg_edges[source_id] = set()
            #self.cfg_edges[source_id].add(target_id)
            self.add_fact('cfg_edge({0}, {1})'.format(source_id, target_id))

    def logic_symbols_facts(self, symbol_id_map, parent_id):
        for symbol_id, symbol_name in symbol_id_map.items():
            if symbol_name not in self.names_id_map:
                logic_var_id = self.id_generator.next_id()
                self.names_id_map[symbol_name] = logic_var_id
                self.add_fact('logicSymbolT({0}, {1}, \'{2}\')'.format(logic_var_id, 'null', symbol_name))

            self.add_fact('logicIdentT({0}, {1}, {2})'.format(symbol_id, parent_id, self.names_id_map[symbol_name]))
            self.add_parent_fact(symbol_id, parent_id)
            self.pre_order.append(symbol_id)
            self.id_node_map[symbol_id] = Symbol(symbol_name)

    def transform_to_facts(self):
        self.reset_transformer()
        root_id = self.id_generator.next_id()
        self.add_cfg_edge_fact(0, root_id)
        self.ast_node_facts(self.ast.root, root_id, 0)
        # for v in self.variables_map:
        #     print v, ": ", len(self.variables_map[v])
        # with open('/home/yakdan/Bilder/pl/preorder', 'w') as pre:
        #     for i in self.pre_order:
        #         pre.write('{0}\n'.format(i))
        # f = open('/home/user/tmp/facts.pl', 'w')
        for fact in self.ast_facts:
            # f.write('{0}.\n'.format(fact))
            self.prolog_engine.assertz(fact)
        # f.close()

    def ast_node_facts(self, ast_node, ast_node_id, parent_id, successor_id=None, enclosing_loop_successor_id=None):
        if ast_node is not None:
            self.add_parent_fact(ast_node_id, parent_id)
            if isinstance(ast_node, Instruction) or isinstance(ast_node, Call):
                if isinstance(ast_node, Break):
                    self.add_cfg_edge_fact(ast_node_id, enclosing_loop_successor_id)
                else:
                    self.add_cfg_edge_fact(ast_node_id, successor_id)

            if not isinstance(ast_node, Expression) or isinstance(ast_node, HighLevelCondition):
                self.pre_order.append(ast_node_id)
                if len(self.pre_order) >= 2:
                    self.add_fact('pre_order_next({0}, {1})'.format(self.pre_order[-2], self.pre_order[-1]))
        #self.children_id_map[ast_node_id] = set()
        if not self.is_identifier(ast_node):
            self.id_node_map[ast_node_id] = ast_node
        if isinstance(ast_node, SequenceNode):
            '''sequenceT(id, parent_id, [statement_1, ...])'''
            stmt_ids = [self.id_generator.next_id() for c in ast_node.children]
            self.add_fact('sequenceT({0}, {1}, {2})'.format(ast_node_id, parent_id, self.list_to_string(stmt_ids)))
            self.add_cfg_edge_fact(ast_node_id, stmt_ids[0])
            for idx in range(0, len(stmt_ids)):
                self.ast_node_facts(ast_node.children[idx], stmt_ids[idx], ast_node_id,
                                    stmt_ids[idx + 1] if idx < len(stmt_ids) - 1 else successor_id,
                                    enclosing_loop_successor_id)
        elif isinstance(ast_node, LoopNode):
            '''loopT(id, parent, 'type', condition, body)'''
            condition_id = self.id_generator.next_id()
            body_id = self.id_generator.next_id()
            self.add_fact('loopT({0}, {1}, \'{2}\', {3}, {4})'.format(
                ast_node_id, parent_id, self.loop_type_to_string(ast_node.type), condition_id, body_id))

            if ast_node.type == LoopType.POST_TESTED:
                self.add_cfg_edge_fact(ast_node_id, body_id)
            else:
                self.add_cfg_edge_fact(ast_node_id, condition_id)

            self.add_cfg_edge_fact(condition_id, body_id)
            self.ast_node_facts(ast_node.condition, condition_id, ast_node_id)
            self.ast_node_facts(ast_node.body, body_id, ast_node_id, condition_id, successor_id)
            self.add_cfg_edge_fact(condition_id, successor_id)

        elif isinstance(ast_node, ForNode):
            init_ids = [self.id_generator.next_id() for i in ast_node.init]
            condition_id = self.id_generator.next_id()
            next_ids = [self.id_generator.next_id() for i in ast_node.next]
            body_id = self.id_generator.next_id()
            self.add_fact('forT({0}, {1}, {2}, {3}, {4}, {5})'.format(ast_node_id, parent_id,
                                                                      self.list_to_string(init_ids), condition_id,
                                                                      self.list_to_string(next_ids), body_id))

            self.add_cfg_edge_fact(ast_node_id, init_ids[0])
            num_init_ids = len(init_ids)
            for idx in range(0, num_init_ids):
                self.ast_node_facts(ast_node.init[idx], init_ids[idx], ast_node_id,
                                    init_ids[idx + 1] if idx < num_init_ids - 1 else condition_id)

            self.add_cfg_edge_fact(condition_id, body_id)
            self.ast_node_facts(ast_node.cond, condition_id, ast_node_id)
            self.ast_node_facts(ast_node.body, body_id, ast_node_id, next_ids[0], successor_id)
            num_next_ids = len(next_ids)
            for idx in range(0, num_next_ids):
                self.ast_node_facts(ast_node.next[idx], next_ids[idx], ast_node_id,
                                    next_ids[idx + 1] if idx < num_next_ids - 1 else condition_id)
            self.add_cfg_edge_fact(condition_id, successor_id)

        elif isinstance(ast_node, ConditionNode):
            '''ifT(id, parent, condition, trueBranch, falseBranch)'''
            condition_id = self.id_generator.next_id()
            true_id = self.id_generator.next_id() if ast_node.trueChild is not None else '\'null\''
            false_id = self.id_generator.next_id() if ast_node.falseChild is not None else '\'null\''
            self.add_fact('ifT({0}, {1}, {2}, {3}, {4})'.format(ast_node_id, parent_id, condition_id, true_id, false_id))

            self.add_cfg_edge_fact(ast_node_id, condition_id)
            if ast_node.trueChild is not None:
                self.add_cfg_edge_fact(condition_id, true_id)
                #self.add_cfg_edge_fact(true_id, successor_id)
            else:
                self.add_cfg_edge_fact(condition_id, successor_id)
            if ast_node.falseChild is not None:
                self.add_cfg_edge_fact(condition_id, false_id)
                #self.add_cfg_edge_fact(false_id, successor_id)
            else:
                self.add_cfg_edge_fact(condition_id, successor_id)

            self.ast_node_facts(ast_node.condition, condition_id, ast_node_id)
            self.ast_node_facts(ast_node.trueChild, true_id, ast_node_id, successor_id, enclosing_loop_successor_id)
            self.ast_node_facts(ast_node.falseChild, false_id, ast_node_id, successor_id, enclosing_loop_successor_id)
        elif isinstance(ast_node, Assignment):
            '''assignT(id, parent, lhs, rhs)'''
            lhs_id = self.get_expr_id(ast_node.lhs_operand)
            rhs_id = self.get_expr_id(ast_node.rhs_operand)
            self.add_fact('assignT({0}, {1}, {2}, {3})'.format(ast_node_id, parent_id, lhs_id, rhs_id))
            self.ast_node_facts(ast_node.lhs_operand, lhs_id, ast_node_id)
            self.ast_node_facts(ast_node.rhs_operand, rhs_id, ast_node_id)
        elif isinstance(ast_node, Call):
            '''callT(#id, #parent, 'name', [arg_1,...], #method)'''
            self.calls.append((ast_node_id, ast_node))
            arg_ids = [self.get_expr_id(arg) for arg in ast_node.parameters]
            self.add_fact('callT({0}, {1}, \'{2}\', {3})'.format(ast_node_id, parent_id, str(ast_node.function_pointer), self.list_to_string(arg_ids)))
            for idx in range(0, len(arg_ids)):
                self.ast_node_facts(ast_node.parameters[idx], arg_ids[idx], ast_node_id)

        elif isinstance(ast_node, Return):
            '''returnT(#id, #parent, #expr)'''
            expr_id = self.get_expr_id(ast_node.operand)
            self.add_fact('returnT({0}, {1}, {2})'.format(ast_node_id, parent_id, expr_id))
            self.ast_node_facts(ast_node.operand, expr_id, ast_node_id)
        elif isinstance(ast_node, Break):
            self.add_fact('breakT({0}, {1})'.format(ast_node_id, parent_id))

        elif isinstance(ast_node, TernaryExpression):
            '''ternaryOperatorT(#id, #parent, #condition, #truePart, #falsePart'''
            condition_id = self.get_expr_id(ast_node.first_operand)
            true_id = self.get_expr_id(ast_node.second_operand)
            false_id = self.get_expr_id(ast_node.third_operand)
            self.add_fact('ternaryOperatorT({0}, {1}, {2}, {3}, {4})'.format(ast_node_id, parent_id, condition_id, true_id, false_id))
            self.ast_node_facts(ast_node.first_operand, condition_id, ast_node_id)
            self.ast_node_facts(ast_node.second_operand, true_id, ast_node_id)
            self.ast_node_facts(ast_node.third_operand, false_id, ast_node_id)
        elif isinstance(ast_node, CastExpression):
            operand_id = self.get_expr_id(ast_node.cast_expression)
            self.add_fact('castT({0}, {1}, \'{2}\', {3})'.format(ast_node_id, parent_id, ast_node.cast_target, operand_id))
            self.ast_node_facts(ast_node.cast_expression, operand_id, ast_node_id)
        elif isinstance(ast_node, ArrayIndexing):
            array_id = self.get_expr_id(ast_node.array)
            index_id = self.get_expr_id(ast_node.index)
            self.add_fact('arrayIndexingT({0}, {1}, {2}, {3})'.format(ast_node_id, parent_id, array_id, index_id))
            self.ast_node_facts(ast_node.array, array_id, ast_node_id)
            self.ast_node_facts(ast_node.index, index_id, ast_node_id)
        elif isinstance(ast_node, MemberAccess):
            struct_id = self.get_expr_id(ast_node.struct)
            field_id = self.get_expr_id(ast_node.field)
            self.add_fact('memberAccessT({0}, {1}, {2}, {3}, \'{4}\')'.format(ast_node_id, parent_id, struct_id, field_id, ast_node.access_operator))
            self.ast_node_facts(struct_id, ast_node_id, ast_node.struct)
            self.ast_node_facts(field_id, ast_node_id, ast_node.field)
        elif isinstance(ast_node, DivisionExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.first_operand, ast_node.second_operand], '/')
        elif isinstance(ast_node, ShiftExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.first_operand, ast_node.second_operand], ast_node.shift_operator)
        elif isinstance(ast_node, AddressExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.operand], '&')
        elif isinstance(ast_node, LogicalNotExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.operand], '!')
        elif isinstance(ast_node, NegationExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.operand], '-')
        elif isinstance(ast_node, HighLevelCondition):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.lhsExpression, ast_node.rhsExpression], ast_node.comparisonString)
        elif isinstance(ast_node, RemainderExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.first_operand, ast_node.second_operand], '%')
        elif isinstance(ast_node, ExponentiationExpression):
            self.generate_operation_facts(ast_node_id, parent_id, [ast_node.first_operand, ast_node.second_operand], '^')
        elif isinstance(ast_node, AdditionExpression):
            self.generate_operation_facts(ast_node_id, parent_id, ast_node.operands, '+')
        elif isinstance(ast_node, MultiplicationExpression):
            self.generate_operation_facts(ast_node_id, parent_id, ast_node.operands, '*')
        elif isinstance(ast_node, ANDExpression):
            self.generate_operation_facts(ast_node_id, parent_id, ast_node.operands, '&&' if ast_node.is_condition else '&')
        elif isinstance(ast_node, ORExpression):
            self.generate_operation_facts(ast_node_id, parent_id, ast_node.operands, '||' if ast_node.is_condition else '|')
        elif isinstance(ast_node, XORExpression):
            self.generate_operation_facts(ast_node_id, parent_id, ast_node.operands, 'V')
        elif isinstance(ast_node, LocalVariable):
            self.add_to_variable_map(ast_node)
            var_id = self.get_variable_id(ast_node, 'local')
            self.add_fact('identT({0}, {1}, {2})'.format(ast_node_id, parent_id, var_id))
        elif isinstance(ast_node, GlobalVariable):
            self.add_to_variable_map(ast_node)
            var_id = self.get_variable_id(ast_node, 'global')
            self.add_fact('identT({0}, {1}, {2})'.format(ast_node_id, parent_id, var_id))
        elif isinstance(ast_node, Pointer):
            '''memoryT(#id, #parent, #address)'''
            add_id = self.get_expr_id(ast_node.address)
            self.add_fact('memoryT({0}, {1}, {2})'.format(ast_node_id, parent_id, add_id))
            self.ast_node_facts(ast_node.address, add_id, ast_node_id)
        elif isinstance(ast_node, NumericConstant):
            self.add_fact('numericLiteralT({0}, {1}, {2})'.format(ast_node_id, parent_id, ast_node.value))
        elif isinstance(ast_node, StringLiteral):
            str_value = re.sub(r"'", '', ast_node.value)
            str_value = re.sub(r"\\", '', str_value)
            self.add_fact('stringLiteralT({0}, {1}, \'{2}\')'.format(ast_node_id, parent_id, str_value))
        else:
            assert type(ast_node) == VariableDeclaration or ast_node is None, 'no transformation to facts possible: {0}'.format(str(ast_node))

    def add_parent_fact(self, node_id, parent_id):
        self.add_fact('parent_node({0}, {1})'.format(node_id, parent_id))

    @staticmethod
    def is_identifier(ast_node):
        return isinstance(ast_node, LocalVariable) or isinstance(ast_node, GlobalVariable)

    def get_variable_id(self, var, type_string):
        if var.name not in self.names_id_map:
            var_id = self.id_generator.next_id()
            self.names_id_map[var.name] = var_id
            self.add_fact('{0}T({1}, \'{2}\', \'{3}\')'.format(type_string, var_id, self.get_variable_type(var), var.name))
            self.id_node_map[var_id] = var
        return self.names_id_map[var.name]

    def get_expr_id(self, expr):
        return self.id_generator.next_id()

    @staticmethod
    def loop_type_to_string(loop_type):
        if loop_type == LoopType.ENDLESS:
            return 'endless'
        elif loop_type == LoopType.PRE_TESTED:
            return 'while'
        elif loop_type == LoopType.POST_TESTED:
            return 'doWhile'
        else:
            assert False

    @staticmethod
    def list_to_string(ids):
        s = '['
        for i in ids:
            s += str(i) + ', '
        return s[:-2]+']' if len(s) > 1 else '[]'

    def generate_operation_facts(self, op_id, parent_id, arguments, op_name):
        """operationT(id, parent, [arg1,...], 'operatorName')"""
        arg_ids = [self.get_expr_id(arg) for arg in arguments]
        self.add_fact('operationT({0}, {1}, {2}, \'{3}\')'.format(op_id, parent_id, self.list_to_string(arg_ids), op_name))
        for idx in range(0, len(arguments)):
            self.ast_node_facts(arguments[idx], arg_ids[idx], op_id)

    def add_fact(self, fact):
        self.ast_facts.append(fact)

    def remove_stmt(self, stmt_id):
        stmt = self.id_node_map[stmt_id]
        parent_id = self.get_parent_id(stmt_id)
        parent = self.id_node_map[parent_id]
        if isinstance(parent, SequenceNode):
            parent.children.remove(stmt)
            if not parent.children:
                self.remove_stmt(parent_id)
        elif isinstance(parent, ConditionNode):
            if stmt == parent.trueChild:
                parent.trueChild = None
            elif stmt == parent.falseChild:
                parent.falseChild = None
            if parent.trueChild is None and parent.falseChild is None:
                self.remove_stmt(parent_id)
        else:
            assert False

    @staticmethod
    def does_answer_overlap(answer, matched_stmt_ids):
        if answer[RuleID.INITIAL_ID] not in matched_stmt_ids:
            children_ids = answer[RuleID.CHILDREN_IDs]
            if type(children_ids) == list:
                return set(children_ids).issubset(matched_stmt_ids)
            else:
                return False
        return True

    @staticmethod
    def parse_transformation(transformation_str):
        #print transformation_str
        parser = c_parser.CParser()
        ast = parser.parse('wrapper(){' + transformation_str + '}', filename='<none>')
        assert type(ast) == c_ast.FileAST and type(ast.ext[0]) == c_ast.FuncDef
        body = ast.ext[0].body
        if type(body) == c_ast.Compound and len(body.block_items) == 1:
            return body.block_items[0]
        return body

    def statement_to_IR(self, stmt, unification_map):
        if type(stmt) == c_ast.Compound:
            return SequenceNode(true, [self.statement_to_IR(s, unification_map) for s in stmt.block_items])

        elif type(stmt) == c_ast.While or type(stmt) == c_ast.DoWhile:
            return LoopNode(LoopType.PRE_TESTED if type(stmt) == c_ast.While else LoopType.POST_TESTED,
                            self.statement_to_IR(stmt.stmt, unification_map),
                            self.statement_to_IR(stmt.cond, unification_map))

        elif type(stmt) == c_ast.For:
            pass

        elif type(stmt) == c_ast.If:
            return ConditionNode(self.statement_to_IR(stmt.cond, unification_map),
                                 self.statement_to_IR(stmt.iftrue, unification_map) if stmt.iftrue else None,
                                 self.statement_to_IR(stmt.iffalse, unification_map) if stmt.iffalse else None)

        elif type(stmt) == c_ast.Switch:
            pass

        elif type(stmt) == c_ast.Assignment:
            if stmt.op == c_lexer.CLexer.t_EQUALS:
                rhs = self.statement_to_IR(stmt.rvalue, unification_map)
            else:
                binary_op = c_ast.BinaryOp(stmt.op[:-1], stmt.lvalue, stmt.rvalue)
                rhs = self.statement_to_IR(binary_op)
            lhs = self.statement_to_IR(stmt.lvalue, unification_map)
            return Assignment(lhs, rhs)

        elif type(stmt) == c_ast.FuncCall:
            if stmt.name.name.title() not in unification_map:
                func_ptr = GlobalVariable(stmt.name.name, None)
            else:
                func_ptr = self.statement_to_IR(stmt.name, unification_map)
            params = [self.statement_to_IR(p, unification_map) for p in stmt.args.exprs]
            return Call(func_ptr, params)

        elif type(stmt) == c_ast.UnaryOp:
            if stmt.op == '*':
                return Pointer(self.statement_to_IR(stmt.expr, unification_map))
            elif stmt.op in ['p++', 'p--']:
                return Assignment(self.statement_to_IR(stmt.expr, unification_map),
                                  AdditionExpression([self.statement_to_IR(stmt.expr, unification_map),
                                                      NumericConstant(1 if stmt.op == 'p++' else -1)]))
            elif stmt.op == '&':
                return AddressExpression(self.statement_to_IR(stmt.expr, unification_map))
            elif stmt.op == '!':
                cond = self.statement_to_IR(stmt.expr, unification_map)
                assert isinstance(cond, HighLevelCondition)
                cond.negate()
                return cond

        elif type(stmt) == c_ast.BinaryOp:
            lhs = self.statement_to_IR(stmt.left, unification_map)
            rhs = self.statement_to_IR(stmt.right, unification_map)
            if stmt.op == '+':
                return AdditionExpression([lhs, rhs])
            if stmt.op == '-':
                if isinstance(rhs, NumericConstant):
                    rhs.value *= -1
                else:
                    rhs = NegationExpression(rhs)
                return AdditionExpression([lhs, rhs])
            elif stmt.op == '*':
                return MultiplicationExpression([lhs, rhs])
            elif stmt.op == '%':
                return RemainderExpression(lhs, rhs)
            elif stmt.op == '||':
                operands = []
                self.extend_or_append_operands(operands, lhs, ORExpression)
                self.extend_or_append_operands(operands, rhs, ORExpression)
                return ORExpression(self.filter_duplicates(operands), is_condition=True)
            elif stmt.op == '&&':
                operands = []
                self.extend_or_append_operands(operands, lhs, ANDExpression)
                self.extend_or_append_operands(operands, rhs, ANDExpression)
                return ANDExpression(self.filter_duplicates(operands), is_condition=True)
            elif stmt.op in ['==', '!=', '>', '>=', '<', '<=']:
                return HighLevelCondition(lhs, stmt.op, rhs)

        elif type(stmt) == c_ast.TernaryOp:
            return TernaryExpression(self.statement_to_IR(stmt.cond, unification_map),
                                     self.statement_to_IR(stmt.iftrue, unification_map),
                                     self.statement_to_IR(stmt.iffalse, unification_map))

        elif type(stmt) == c_ast.ID:
            assert stmt.name.title() in unification_map, 'identifier {0} is not unified'.format(stmt.name)
            expr_id = unification_map[stmt.name.title()]
            if expr_id in self.id_node_map:
                return self.id_node_map[expr_id].deep_copy()
            else:
                expr_id = self.get_identifier_variable(expr_id)
                assert expr_id in self.id_node_map
                return self.id_node_map[expr_id].deep_copy()

        elif type(stmt) == c_ast.Constant:
            if stmt.type == 'int':
                return NumericConstant(int(stmt.value))
            elif stmt.type == 'float':
                return NumericConstant(float(stmt.value))

        elif type(stmt) == c_ast.Return:
            return Return(self.statement_to_IR(stmt.expr, unification_map))
        else:
            assert False, "unrecognized stmt: {0}\n".format(type(stmt))

    @staticmethod
    def filter_duplicates(exprs):
        unique_exprs = []
        for exp in exprs:
            if exp not in unique_exprs:
                unique_exprs.append(exp)
        return unique_exprs

    @staticmethod
    def extend_or_append_operands(operands, exp, exp_type):
        if type(exp) == exp_type:
            operands.extend(exp.operands)
        else:
            operands.append(exp)

    def get_ids_to_remove(self, stmt_id, children_ids):
        stmt = self.id_node_map[stmt_id]
        root_ids = set()
        if isinstance(stmt, SequenceNode) and type(children_ids) == list and len(children_ids) < len(stmt.children):
            root_ids.update(children_ids)
        else:
            root_ids.add(stmt_id)

        ids_to_remove = set()
        for rm_id in root_ids:
            for answer in self.prolog_engine.query('get_all_children({0}, Children)'.format(rm_id)):
                ids_to_remove.update(answer['Children'])
        ids_to_remove.update(root_ids)
        return ids_to_remove

    def replace_code(self, stmt_id, parent_id, children_ids, transformed_stmt):
        stmt = self.id_node_map[stmt_id]
        if isinstance(stmt, SequenceNode):
            if type(children_ids) == list and len(children_ids) < len(stmt.children):
                stmts_to_remove = [self.id_node_map[s_id] for s_id in children_ids]
                stmt.replace_child_stmts(stmts_to_remove, transformed_stmt)
            else:
                if parent_id == 0:
                    self.ast.root = transformed_stmt
                else:
                    parent_stmt = self.id_node_map[parent_id]
                    parent_stmt.replace_child_stmt(stmt, transformed_stmt)
        else:
            parent_stmt = self.id_node_map[parent_id]
            if isinstance(parent_stmt, Expression):
                assert isinstance(stmt, Expression) and isinstance(transformed_stmt, Expression)
                parent_stmt.replace_child_expr(stmt, transformed_stmt)
            else:
                parent_stmt.replace_child_stmt(stmt, transformed_stmt)

    def add_to_variable_map(self, var):
        if var.name not in self.variables_map:
            self.variables_map[var.name] = []
            self.ordered_variable_names.append(var.name)
        self.variables_map[var.name].append(var)
        for param in self.ast.function_signature.parameters:
            if param.name == var.name:
                self.variables_map[var.name].append(param)
                break

    def rename_variables(self):
        renamed_vars_map = {}
        for call_tuple in self.calls:
            call_id = call_tuple[0]
            call = call_tuple[1]
            func_name = str(call.function_pointer)
            if func_name in self.api_functions:
                for idx in range(0, len(call.parameters)):
                    param = call.parameters[idx]
                    new_name = self.api_functions[func_name]['parameters'][idx]['name']
                    if new_name is not None:
                        if self.has_name(param):
                            self.rename_if_not_renamed(param.name, new_name, renamed_vars_map)
                        elif isinstance(param, AddressExpression) and self.has_name(param.operand):
                            new_name = new_name[2:] if new_name[:2] == 'lp' else new_name
                            self.rename_if_not_renamed(param.operand.name, new_name, renamed_vars_map)

                ret_name = self.api_functions[func_name]['return']['name']
                if ret_name is not None:
                    call_parent = self.id_node_map[self.get_parent_id(call_id)]
                    if isinstance(call_parent, Assignment) and isinstance(call_parent.lhs_operand, LocalVariable):
                        self.rename_if_not_renamed(call_parent.lhs_operand.name, ret_name, renamed_vars_map)

        self.rename_parameters(renamed_vars_map)
        self.rename_local_variables(renamed_vars_map.keys())

    def rename_parameters(self, renamed_variables):
        idx = 1
        for param in self.ast.function_signature.parameters:
            assert isinstance(param, LocalVariable)
            if param.name not in renamed_variables:
                self.rename_variable(param.name, 'a{0}'.format(idx))
                param.name = 'a{0}'.format(idx)
                idx += 1

    def rename_local_variables(self, renamed_variables):
        self.rename_return_variable(renamed_variables)
        boolean_vars = []
        non_boolean_vars = []
        for name in self.ordered_variable_names:
            if len(name) > 5 and name[:5] == 'cond_':
                boolean_vars.append(name)
            else:
                non_boolean_vars.append(name)
        parameter_names = [param.name for param in self.ast.function_signature.parameters]

        taken_names = parameter_names + renamed_variables
        self.rename_variable_list(boolean_vars, 'cond', taken_names)
        self.rename_loop_variables(non_boolean_vars, taken_names)
        self.rename_array_indexes(non_boolean_vars, taken_names)
        self.rename_variable_list(non_boolean_vars, 'v', taken_names)

    def rename_return_variable(self, renamed_variables):
        answer = [a for a in self.prolog_engine.query('return_result(Variable)')]
        assert len(answer) <= 1
        if answer:
            ret_var = self.id_node_map[answer[0]['Variable']]
            if ret_var.name not in renamed_variables:
                self.rename_variable(ret_var.name, 'result')
                renamed_variables.append('result')

    def rename_variable_list(self, variable_names_list, default_name, taken_names):
        idx = 1
        for name in variable_names_list:
            var_list = self.variables_map[name]
            if isinstance(var_list[0], LocalVariable) and name not in taken_names:
                new_name = '{0}{1}'.format(default_name, idx)
                self.rename_variable(name, new_name)
                taken_names.append(new_name)
                idx += 1

    def rename_loop_variables(self, variable_names_list, taken_names):
        self.rename_for_variables(variable_names_list, taken_names)
        n = 1
        for loop in self.get_counting_loops():
            for var in loop[1]:
                counting_var_name = self.id_node_map[var].name
                if counting_var_name not in taken_names:
                    new_name = 'counter{0}'.format(n)
                    n += 1
                    self.rename_variable(counting_var_name, new_name)
                    taken_names.append(new_name)
                    variable_names_list.remove(counting_var_name)

    def rename_for_variables(self, variable_names_list, taken_names):
        inner_loops = [f for f in self.get_short_self_contained_for_loops() if len(self.get_nested_for_loops(f)) == 0]
        if inner_loops:
            for_init_name = 'i'
            if for_init_name not in taken_names:
                if for_init_name in variable_names_list:
                    tmp_name = self.replace_by_tmp_variable(for_init_name)
                    variable_names_list[variable_names_list.index(for_init_name)] = tmp_name

                old_names = [self.id_node_map[f].init[0].lhs_operand.name for f in inner_loops]
                self.merge_variables(old_names, 'i')
                for old_name in old_names:
                    variable_names_list.remove(old_name)
                taken_names.append('i')

    @staticmethod
    def get_top_level_loops(nesting_map):
        inner_elements = set(itertools.chain(*nesting_map.values()))
        return [k for k in nesting_map.keys() if k not in inner_elements]

    def get_counting_loops(self):
        loops = [answer for answer in self.prolog_engine.query('counting_loops(LoopList)')][0]['LoopList']
        return loops if type(loops) == list else []

    def get_short_self_contained_for_loops(self):
        return [f for f in self.get_for_loops() if self.is_short_loop(f) and self.is_self_contained_loop(f)]

    def get_for_loops(self):
        return [a['ForLoop'] for a in self.prolog_engine.query('for_loop(ForLoop)')]

    def get_nested_for_loops(self, stmt_id):
        inner_for_loops = list(self.prolog_engine.query('nested_for_loops({0}, InnerForLoops)'.format(stmt_id)))[0]['InnerForLoops']
        return inner_for_loops if type(inner_for_loops) == list else []

    def is_self_contained_loop(self, for_id):
        for_stmt = self.id_node_map[for_id]
        if len(for_stmt.init) == 1:
            var = for_stmt.init[0].lhs_operand
            var_id = None
            for k, v in self.id_node_map.items():
                if v == var:
                    var_id = k
                    break
            assert var_id is not None
            return self.is_only_used_in_statement(var_id, for_id)
        return False

    def is_short_loop(self, for_id):
        for_stmt = self.id_node_map[for_id]
        if type(for_stmt.body) == SequenceNode:
            return len(for_stmt.body.children) <= 5
        else:
            return True

    def rename_array_indexes(self, variable_names_list, taken_names):
        index_ids = list({a['Index'] for a in self.prolog_engine.query('array_index(Index)')})
        index_ids.sort()
        for idx_id in index_ids:
            old_name = self.id_node_map[idx_id].name
            if old_name not in taken_names:
                new_name = 'index'
                if new_name in taken_names:
                    subscript = 1
                    while "{0}{1}".format(new_name, subscript) in taken_names:
                        subscript += 1
                    new_name = "{0}{1}".format(new_name, subscript)

                # print old_name, '->', new_name
                self.rename_variable(old_name, new_name)
                taken_names.append(new_name)
                variable_names_list.remove(old_name)

    def rename_if_not_renamed(self, old_name, new_name, renamed_variables):
        if old_name != new_name:
            if old_name not in renamed_variables:
                if new_name not in renamed_variables:
                    self.rename_variable(old_name, new_name)
                    renamed_variables[new_name] = 1
                else:
                    new_name_subscript = "{0}{1}".format(new_name, renamed_variables[new_name])
                    self.rename_variable(old_name, new_name_subscript)
                    renamed_variables[new_name] += 1
                    renamed_variables[new_name_subscript] = None
        else:
            if old_name not in renamed_variables:
                renamed_variables[old_name] = 0
            renamed_variables[old_name] += 1

    def rename_variable(self, old_name, new_name):
        if old_name == new_name:
            return
        if old_name in self.variables_map:
            if '.' in old_name:
                new_name = old_name
            elif new_name in self.variables_map:
                #this case does not happen as a result of previous renamings; only if the code originally contained a variable named new_name
                self.replace_by_tmp_variable(new_name)

            var_list = self.variables_map[old_name]
            for var in var_list:
                var.name = new_name
            del self.variables_map[old_name]
            self.variables_map[new_name] = var_list
            idx = self.ordered_variable_names.index(old_name)
            self.ordered_variable_names[idx] = new_name
        else:
            assert old_name in [x.name for x in self.ast.function_signature.parameters]

    def merge_variables(self, old_names, new_name):
        assert all(name in self.variables_map for name in old_names)
        if new_name in self.variables_map:
            self.replace_by_tmp_variable(new_name)
        self.variables_map[new_name] = []
        for old_name in old_names:
            var_list = self.variables_map[old_name]
            for var in var_list:
                var.name = new_name
            del self.variables_map[old_name]
            self.variables_map[new_name].extend(var_list)
            idx = self.ordered_variable_names.index(old_name)
            self.ordered_variable_names[idx] = new_name

    def replace_by_tmp_variable(self, var_name):
        tmp_name = self.get_new_name(var_name)
        self.rename_variable(var_name, tmp_name)
        return tmp_name

    def get_identifier_variable(self, ident_id):
        var_id = [a for a in self.prolog_engine.query('identT({0}, _, Variable)'.format(ident_id))]
        assert len(var_id) == 1
        return var_id[0]['Variable']

    def get_new_name(self, var_name):
        idx = 0
        while "{0}{1}".format(var_name, idx) in self.variables_map:
            idx += 1
        return "{0}{1}".format(var_name, idx)

    @staticmethod
    def has_name(var):
        return isinstance(var, LocalVariable) or isinstance(var, GlobalVariable)


class NamedConstantTransformer(object):
    def __init__(self, id_node_map, prolog_engine, ast):
        self.ast = ast
        self.id_node_map = id_node_map
        self.prolog_engine = prolog_engine

    def apply_transformations(self):
        used_named_constants = [v for v in self.get_used_constants() if v in NAMED_CONSTANTS]
        renamed_constants = set()
        for v in used_named_constants:
            for cond_id in self.get_using_compare_expr(v):
                cond_expr = self.id_node_map[cond_id]
                cond_expr.rhsExpression = LocalVariable(NAMED_CONSTANTS[v])
                renamed_constants.add(v)
        for v in renamed_constants:
            self.ast.global_declarations.append(VariableDeclaration(LocalVariable(NAMED_CONSTANTS[v], 'const int'), v))

    def get_using_compare_expr(self, const):
        return [a['Compare'] for a in self.prolog_engine.query('named_constant_compare({0}, Compare)'.format(const))]

    def get_used_constants(self):
        return set([a['Value'] for a in self.prolog_engine.query('numericLiteralT(_, _, Value)')])
