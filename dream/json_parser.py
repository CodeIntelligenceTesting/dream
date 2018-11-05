# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import json
from sympy.core.symbol import Symbol
from sympy.logic.boolalg import Not, true
from dream.ControlFlowGraph import ControlFlowGraph, NodeType
from dream.ControlFlowTree import FunctionSignature, SequenceNode
from dream.ir.expressions import (
    LocalVariable, GlobalVariable, Pointer, StringLiteral, NumericConstant,
    TernaryExpression, AddressExpression, LogicalNotExpression,
    NegationExpression, HighLevelCondition, RemainderExpression,
    ExponentiationExpression, AdditionExpression, MultiplicationExpression,
    ANDExpression, ORExpression, XORExpression, Call, ShiftExpression,
    DivisionExpression)
from dream.ir.instructions import Assignment, Return


class JsonGraphParser:
    def __init__(self):
        self.cfg = ControlFlowGraph()
        self.g_json = None
        # self.symbols_alias_map = {}

    def get_function_signature(self):
        parameters = []
        for param in self.g_json['arguments']:
            parameters.append(self.make_expression(param))
        return FunctionSignature(self.g_json['function_name'], parameters,
                                 None)

    def graph_from_json(self, file_name):
        f = open(file_name)
        self.g_json = json.load(f, encoding='ascii')
        f.close()
        nodes = self.g_json['cfg']['nodes']

        self.cfg.add_vertex(n=len(nodes))
        for n in nodes:
            v = self.cfg.vertex(int(n['id']))
            node_type = self.get_node_type(n)
            self.cfg.vertex_properties['type'][v] = node_type
            if node_type == NodeType.CODE:
                self.cfg.vertex_properties['ast'][v] = self.construct_ast(n)
            self.add_edges(v, n['successors'])
        self.cfg.conditions_map = self.construct_conditions_map(self.g_json[
            'cfg']['conditions_map'])

    @staticmethod
    def get_node_type(n_json):
        if n_json['type'] == 'Code':
            return NodeType.CODE
        elif n_json['type'] == 'Conditional':
            return NodeType.CONDITIONAL
        elif n_json['type'] == 'Switch':
            return NodeType.SWITCH

    def add_edges(self, v, successors_json):
        for s in successors_json:
            e = self.cfg.add_edge(v, int(s['node_id']))
            label = s['tag'].encode('ascii')
            if label == 'None':
                self.cfg.edge_properties['tag'][e] = None
            elif label[0] == '!':
                self.cfg.edge_properties['tag'][e] = Not(Symbol(label[1:]))
            else:
                self.cfg.edge_properties['tag'][e] = Symbol(label)

    def construct_ast(self, n_json):
        ast = SequenceNode(true, [])
        for inst in n_json['instructions']:
            ast.children.append(self.make_instruction(inst))
        return ast

    def make_instruction(self, inst_json):
        if inst_json['instruction_type'] == 'Assignment':
            return Assignment(
                self.make_expression(inst_json['lhsOperand']),
                self.make_expression(inst_json['rhsOperand']))
        elif inst_json['instruction_type'] == 'CALL':
            assert len(inst_json['returns']) <= 1
            call_expr = Call(
                self.make_expression(inst_json['functionPointer']), [
                    self.make_expression(exp_json)
                    for exp_json in inst_json['parameters']
                ])
            if inst_json['returns']:
                return Assignment(
                    self.make_expression(inst_json['returns'][0]), call_expr)
            else:
                return call_expr

        elif inst_json['instruction_type'] == 'Return':
            return Return(self.make_expression(inst_json['operand']))
        else:
            print inst_json
            assert False, "unsupported instruction type: {0}".format(inst_json[
                'instruction_type'])

    def make_expression(self, exp_json):
        if exp_json['expression_type'] == 'LocalVariable':
            name = exp_json['name']
            type_str = exp_json['type'].strip(
            ) if 'type' in exp_json else 'int'
            var = LocalVariable(name, type_str if type_str != 'void' else None)
            self.cfg.variable_names[var.name] = var
            return var

        elif exp_json['expression_type'] == 'GlobalVariable':
            name = exp_json['name']
            g_var = GlobalVariable(name, int(exp_json['address']))
            self.cfg.variable_names[g_var.name] = g_var
            return g_var
        elif exp_json['expression_type'] == 'PointerExp':
            return Pointer(
                self.make_expression(exp_json['addressExpression']),
                4)  # int(exp_json['size_in_bytes'])
        elif exp_json['expression_type'] == 'StringLiteral':
            return StringLiteral(exp_json['value'])
        elif exp_json['expression_type'] == 'NumericConstant':
            value = float(exp_json['value'])
            return NumericConstant(
                int(value) if value == int(value) else value)
        elif exp_json['expression_type'] == 'TernaryExpression':
            return TernaryExpression(
                self.make_expression(exp_json['firstOperand']),
                self.make_expression(exp_json['secondOperand']),
                self.make_expression(exp_json['thirdOperand']))
        elif exp_json['expression_type'] == 'AddressExpression':
            return AddressExpression(self.make_expression(exp_json['operand']))
        elif exp_json['expression_type'] == 'LogicalNotExpression':
            return LogicalNotExpression(
                self.make_expression(exp_json['operand']))
        elif exp_json['expression_type'] == 'NegationExpression':
            return NegationExpression(
                self.make_expression(exp_json['operand']))
        elif exp_json['expression_type'] == 'HighLevelCondition':
            return HighLevelCondition(
                self.make_expression(exp_json['firstOperand']),
                exp_json['comparisonOperand'],
                self.make_expression(exp_json['secondOperand']), False if
                'isUnsigned' in exp_json and exp_json['isUnsigned'] else True)
        elif exp_json['expression_type'] == 'RemainderExpression':
            return RemainderExpression(
                self.make_expression(exp_json['firstOperand']),
                self.make_expression(exp_json['secondOperand']))
        elif exp_json['expression_type'] == 'ExponentiationExpression':
            return ExponentiationExpression(
                self.make_expression(exp_json['firstOperand']),
                self.make_expression(exp_json['secondOperand']))
        elif exp_json['expression_type'] == 'DivisionExpression':
            return DivisionExpression(
                self.make_expression(exp_json['firstOperand']),
                self.make_expression(exp_json['secondOperand']))
        elif exp_json['expression_type'] == 'AdditionExpression':
            return AdditionExpression(
                [self.make_expression(exp) for exp in exp_json['operands']])
        elif exp_json['expression_type'] == 'MultiplicationExpression':
            return MultiplicationExpression(
                [self.make_expression(exp) for exp in exp_json['operands']])
        elif exp_json['expression_type'] == 'ANDExpression':
            return ANDExpression(
                [self.make_expression(exp) for exp in exp_json['operands']])
        elif exp_json['expression_type'] == 'ORExpression':
            return ORExpression(
                [self.make_expression(exp) for exp in exp_json['operands']])
        elif exp_json['expression_type'] == 'XORExpression':
            return XORExpression(
                [self.make_expression(exp) for exp in exp_json['operands']])
        elif exp_json['expression_type'] == 'ShiftExpression':
            return ShiftExpression(
                self.make_expression(exp_json['firstOperand']),
                self.make_expression(exp_json['secondOperand']),
                exp_json['operation'])
        else:
            assert False, "unsupported expression type: {0}".format(exp_json)

    def construct_conditions_map(self, conditions_json):
        conditions_map = {}
        for tag in conditions_json:
            conditions_map[Symbol(tag['tag_name'])] = self.make_expression(tag[
                'tag_condition'])
        return conditions_map
