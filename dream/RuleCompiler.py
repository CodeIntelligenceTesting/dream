# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import ConfigParser
import getopt
import os
import sys
from pycparser import c_ast, c_lexer, c_parser


class RuleID:
    INITIAL_ID = 'Id_0'
    PARENT_ID = 'ParentId'
    CHILDREN_IDs = 'ChildrenIds'
    TRANSFORMATION = 'Transformation'

    def __init__(self, initial_value=0):
        self.value = initial_value

    def next_id(self):
        self.value += 1
        return 'Id_{0}'.format(self.value)


class RuleHeader:
    def __init__(self, func_decl):
        assert type(func_decl) == c_ast.FuncDecl
        self.name = self.rule_name(func_decl)
        self.params = self.param_names(func_decl)
        self.ret = None

    @staticmethod
    def rule_name(func_decl):
        return func_decl.type.declname

    @staticmethod
    def param_names(func_decl):
        params = [RuleID.PARENT_ID, RuleID.INITIAL_ID, RuleID.CHILDREN_IDs, RuleID.TRANSFORMATION]
        for arg in func_decl.args.params:
            #TODO consider when types are there
            params.append(arg.name.title())
        return params

    def __str__(self):
        hdr_str = self.name + '('
        for param in self.params:
            hdr_str += param + ', '
        return hdr_str[:-2] + ')'

    def query_string(self):
        q_str = self.name + '('
        for i in range(0, len(self.params)):
            q_str += (self.params[i] if i < 3 else 'Arg_{0}'.format(i - 2)) + ', '
        return q_str[:-2] + ')'


class TransformationRule:
    SPECIAL_VARIABLE_START = '$'

    def __init__(self, rule_ast, rule_transformation):
        assert type(rule_ast) == c_ast.FuncDef, 'Transformation rules should be a valid function definition'
        self.rule_ast = rule_ast
        self.variable_ids = set()
        self.rule_body = ['{0} = \'{1}\''.format(RuleID.TRANSFORMATION, rule_transformation.replace("\n", ""))]
        self.rule_header = RuleHeader(rule_ast.decl.type)
        self.id_generator = RuleID()

    def __str__(self):
        rule_str = str(self.rule_header) + ' :-'
        for item in self.rule_body:
            rule_str += '\n    ' + item + ','
        return rule_str[:-1] + '.'

    def compile_rule(self):
        self.statement_rules(self.rule_ast.body, RuleID.INITIAL_ID, RuleID.PARENT_ID)
        variable_ids_list = list(self.variable_ids)
        for i in range(0, len(variable_ids_list)):
            for j in range(i+1, len(variable_ids_list)):
                self.rule_body.append('{0} \= {1}'.format(variable_ids_list[i], variable_ids_list[j]))

    def statement_rules(self, stmt, stmt_id, parent_id):
        if type(stmt) == c_ast.Compound:
            if len(stmt.block_items) == 1:
                self.statement_rules(stmt.block_items[0], stmt_id, parent_id)
            else:
                block_id = self.next_id()
                self.rule_body.append('sequenceT({0}, {1}, {2})'.format(stmt_id, parent_id, block_id))

                items_ids = [self.next_id() for s in stmt.block_items if type(s) != c_ast.Label]

                if stmt_id == RuleID.INITIAL_ID:
                    self.rule_body.append('{0} = {1}'.format(RuleID.CHILDREN_IDs, self.list_to_string(items_ids)))
                else:
                    self.rule_body.append('length({0}, {1})'.format(block_id, len(items_ids)))

                for idx in range(0, len(stmt.block_items)):
                    if type(stmt.block_items[idx]) == c_ast.Label:
                        self.parse_label(stmt.block_items[idx])
                    else:
                        self.statement_rules(stmt.block_items[idx], items_ids[idx], stmt_id)
                        if idx > 0:
                            self.rule_body.append('directly_after({0}, {1}, {2})'.format(items_ids[idx], items_ids[idx-1], block_id))

        elif type(stmt) == c_ast.While or type(stmt) == c_ast.DoWhile:
            # LoopNode(LoopType.PRE_TESTED, get_ast(stmt.stmt), get_ast(stmt.cond))
            condition_id = self.next_id()
            body_id = self.next_id()
            loop_type = 'doWhile' if type(stmt) == c_ast.DoWhile else 'while'
            self.rule_body.append('loopT({0}, {1}, \'{2}\', {3}, {4})'.format(stmt_id, parent_id, loop_type, condition_id, body_id))
            self.statement_rules(stmt.cond, condition_id, stmt_id)
            self.statement_rules(stmt.stmt, body_id, stmt_id)

        elif type(stmt) == c_ast.For:
            pass

        elif type(stmt) == c_ast.If:
            #ConditionNode(stmt.cond, stmt.iftrue, stmt.iffalse)
            condition_id = self.next_id()
            true_id = self.next_id() if stmt.iftrue is not None else '\'null\''
            false_id = self.next_id() if stmt.iffalse is not None else '\'null\''
            self.rule_body.append('ifT({0}, {1}, {2}, {3}, {4})'.format(stmt_id, parent_id, condition_id, true_id, false_id))
            self.statement_rules(stmt.cond, condition_id, stmt_id)
            if stmt.iftrue is not None:
                self.statement_rules(stmt.iftrue, true_id, stmt_id)
            if stmt.iffalse is not None:
                self.statement_rules(stmt.iffalse, false_id, stmt_id)

        elif type(stmt) == c_ast.Switch:
            pass

        elif type(stmt) == c_ast.Assignment:
            lhs_id = self.next_id()
            rhs_id = self.next_id()
            self.rule_body.append('assignT({0}, {1}, {2}, {3})'.format(stmt_id, parent_id, lhs_id, rhs_id))
            self.statement_rules(stmt.lvalue, lhs_id, stmt_id)
            if stmt.op == c_lexer.CLexer.t_EQUALS:
                self.statement_rules(stmt.rvalue, rhs_id, stmt_id)
            else:
                binary_op = c_ast.BinaryOp(stmt.op[:-1], stmt.lvalue, stmt.rvalue)
                self.statement_rules(binary_op, rhs_id, stmt_id)

        elif type(stmt) == c_ast.FuncCall:
            args_block_id = self.next_id()
            self.rule_body.append('callT({0}, {1}, \'{2}\', {3})'.format(stmt_id, parent_id, stmt.name.name, args_block_id))
            self.rule_body.append('length({0}, {1})'.format(args_block_id, len(stmt.args.exprs)))
            arg_ids = [self.next_id() for arg in stmt.args.exprs]
            for idx in range(0, len(arg_ids)):
                self.statement_rules(stmt.args.exprs[idx], arg_ids[idx], stmt_id)
                if idx > 0:
                    self.rule_body.append('directly_after({0}, {1}, {2})'.format(arg_ids[idx], arg_ids[idx - 1], args_block_id))

        elif type(stmt) == c_ast.UnaryOp:
            if stmt.op == '*':
                addr_expr_id = self.next_id()
                self.rule_body.append('memoryT({0}, {1}, {2})'.format(stmt_id, parent_id, addr_expr_id))
                self.statement_rules(stmt.expr, addr_expr_id, stmt_id)
            elif stmt.op in ['p++', 'p--']:
                assignment = c_ast.Assignment(c_lexer.CLexer.t_EQUALS,
                                              stmt.expr,
                                              c_ast.BinaryOp('+',
                                                             stmt.expr,
                                                             c_ast.Constant('int', 1 if stmt.op == 'p++' else -1)))
                self.statement_rules(assignment, stmt_id, parent_id)
            else:
                self.operation_rules(stmt_id, parent_id, [stmt.expr], stmt.op)

        elif type(stmt) == c_ast.BinaryOp:
            if stmt.op == '-':
                stmt.op = '+'
                if type(stmt.right) == c_ast.Constant and stmt.right.type in ['int', 'float']:
                    stmt.right.value = '-' + stmt.right.value
                else:
                    stmt.right = c_ast.UnaryOp('-', stmt.right)

            self.operation_rules(stmt_id, parent_id, [stmt.left, stmt.right], stmt.op)

        elif type(stmt) == c_ast.TernaryOp:
            cond_id = self.next_id()
            true_id = self.next_id()
            false_id = self.next_id()
            self.rule_body.append('ternaryOperatorT({0}, {1}, {2}, {3}, {4})'.format(stmt_id, parent_id, cond_id, true_id, false_id))
            self.statement_rules(stmt.cond, cond_id, stmt_id)
            self.statement_rules(stmt.iftrue, true_id, stmt_id)
            self.statement_rules(stmt.iffalse, false_id, stmt_id)

        elif type(stmt) == c_ast.ID:
            if stmt.name[0] == self.SPECIAL_VARIABLE_START:
                self.rule_body.append('{0} = {1}'.format(stmt.name[1:].title(), stmt_id))
            else:
                self.rule_body.append('identT({0}, {1}, {2})'.format(stmt_id, parent_id, stmt.name.title()))
                self.variable_ids.add(stmt.name.title())

        elif type(stmt) == c_ast.Constant:
            if stmt.type == 'int':
                try:
                    val = int(stmt.value)
                except ValueError:
                    val = int(stmt.value, 16)
                self.rule_body.append('numericLiteralT({0}, {1}, {2})'.format(stmt_id, parent_id, val))
        elif type(stmt) == c_ast.Break:
            self.rule_body.append('breakT({0}, {1})'.format(stmt_id, parent_id))
        elif type(stmt) == c_ast.Return:
            op_id = self.id_generator.next_id()
            self.rule_body.append('returnT({0}, {1}, {2})'.format(stmt_id, parent_id, op_id))
            self.statement_rules(stmt.expr, op_id, stmt_id)
        elif type(stmt) == c_ast.Label:
            self.parse_label(stmt)
        else:
            assert False, "unrecognized stmt: {0}\n".format(type(stmt))

    def operation_rules(self, stmt_id, parent_id, arguments, operation_name):
        args_block_id = self.next_id()
        self.rule_body.append('operationT({0}, {1}, {2}, \'{3}\')'.format(stmt_id, parent_id, args_block_id, operation_name))
        self.rule_body.append('length({0}, {1})'.format(args_block_id, len(arguments)))
        arg_ids = [self.next_id() for arg in arguments]
        for idx in range(0, len(arg_ids)):
            self.statement_rules(arguments[idx], arg_ids[idx], stmt_id)
            self.rule_body.append('member({0}, {1})'.format(arg_ids[idx], args_block_id))
            if not self.is_cumulative(operation_name) and idx > 0:
                self.rule_body.append('directly_after({0}, {1}, {2})'.format(arg_ids[idx], arg_ids[idx-1], args_block_id))

        for idx in range(0, len(arg_ids)):
            for idx_2 in range(idx+1, len(arg_ids)):
                self.rule_body.append('{0} \= {1}'.format(arg_ids[idx], arg_ids[idx_2]))

    @staticmethod
    def is_cumulative(op):
        return op in ['+', '*', '||', '&&', '|', '&']

    def next_id(self):
        return self.id_generator.next_id()

    @staticmethod
    def list_to_string(ids):
        s = '['
        for i in ids:
            s += str(i) + ', '
        return s[:-2] + ']'

    def parse_label(self, label):
        assert label.name == 'META' and type(label.stmt) == c_ast.FuncCall
        meta_call = label.stmt
        if meta_call.name.name == 'SAME_EXPR':
            meta_args = meta_call.args.exprs
            self.rule_body.append('same_expression({0}, {1})'.format(meta_args[0].name.title(),
                                                                     meta_args[1].name.title()))
        elif meta_call.name.name == 'INIT_VALUE':
            meta_args = meta_call.args.exprs
            self.rule_body.append('init_value({0}, {1})'.format(meta_args[0].name.title(),
                                                                meta_args[1].name.title()))


class RuleCompiler:
    def __init__(self, src_file, out_dir):
        self.out_dir = out_dir
        rules_src = ConfigParser.ConfigParser()
        rules_src.read(src_file)
        self.rules = [{
                          'signature': rules_src.get(rule, 'Signature'),
                          'transformation': rules_src.get(rule, 'Transformation')
                      }
                      for rule in rules_src.sections()]

        # self.rule_base = open(config.PROLOG['rules'], 'w')
        # self.query_base = open(config.PROLOG['queries'], 'w')

    def compile(self):
        with open(os.path.join(self.out_dir, 'rules.pl'), 'w') as rule_base, \
             open(os.path.join(self.out_dir, 'queries'), 'w') as query_base:
            for rule in self.rules:
                parser = c_parser.CParser()
                rule_ast = parser.parse(rule['signature'], filename='<none>')
                if type(rule_ast) == c_ast.FileAST and type(rule_ast.ext[0]) == c_ast.FuncDef:
                    signature = rule_ast.ext[0]
                    tr = TransformationRule(signature, rule['transformation'])
                    tr.compile_rule()
                    rule_base.write(str(tr) + '\n'*2)
                    query_base.write(str(tr.rule_header) + '\n')


def main():
    try:
        opts, args = getopt.getopt(sys.argv[1:], 'i:o:')
    except getopt.GetoptError:
        print 'compile_rule.py -i <input file> -o <output directory>'
        sys.exit(2)

    opts = dict(opts)
    assert '-i' in opts
    in_file = opts['-i']

    out_dir = opts['-o'] if '-o' in opts else os.getcwd()

    r_compiler = RuleCompiler(in_file, out_dir)
    r_compiler.compile()

if __name__ == '__main__':
    main()
