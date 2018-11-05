# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

import os
from dream.ControlFlowTree import CodeNode, SequenceNode, ConditionNode, BasicBlock, LoopNode, LoopType, SwitchNode, ForNode
from dream.ir.expressions import Expression
from dream.ir.instructions import Instruction
from dream.logic import get_negated_condition


class AST:
    def __init__(self, root_node, function_signature):
        self.root = root_node
        self.function_signature = function_signature
        self.global_declarations = []

    def write_to_file(self, path):
        f = open(path, 'w')
        self.write_node(self.root, f, 0)
        f.close()

    def write(self, file_name):
        dir_name = os.path.dirname(file_name)
        if not os.path.exists(dir_name):
            os.makedirs(dir_name)

        f = open(file_name, 'w')
        for decl in self.global_declarations:
            f.write(str(decl) + ';\n')
        if self.global_declarations:
            f.write('\n')
        f.write(str(self.function_signature) + '{\n')
        self.write_node(self.root, f, 1)
        f.write('}')
        f.close()

    def write_f(self, f):
        f.write(str(self.function_signature) + '{\n')
        self.write_node(self.root, f, 1)
        f.write('}')

    def write_node(self, node, f, indent, nested_if=False):
        assert not isinstance(node, CodeNode)
        assert not isinstance(node, BasicBlock)
        if isinstance(node, SequenceNode):
            for n in node.children:
                self.write_node(n, f, indent)
        elif isinstance(node, ConditionNode):
            condition_exp = node.condition
            negated_condition_exp = get_negated_condition(condition_exp)
            cond_str, neg_cond_str = str(condition_exp), str(negated_condition_exp)
            cond_str = cond_str #if cond_str[0] != '(' else cond_str[1:-1]
            neg_cond_str = neg_cond_str #if neg_cond_str[0] != '(' else neg_cond_str[1:-1]

            then_has_bracket = self.needs_brackets(node.trueChild)
            else_has_bracket = self.needs_brackets(node.falseChild)

            if not isinstance(node.trueChild, ConditionNode) and not isinstance(node.falseChild, ConditionNode):
                f.write('{0}if({1}){2}\n'.format(self.get_indent_str(indent) if not nested_if else '',
                                                 cond_str, '{' if then_has_bracket else ''))
                self.write_node(node.trueChild, f, indent+1)
                if node.falseChild is not None:
                    f.write('{0}{1}else{2}\n'.format(self.get_indent_str(indent),
                                                     '} ' if then_has_bracket else '',
                                                     '{' if else_has_bracket else ''))
                    self.write_node(node.falseChild, f, indent+1)
                    if else_has_bracket:
                        self.write_closing_bracket(indent, f)
                elif then_has_bracket:
                    self.write_closing_bracket(indent, f)
            elif isinstance(node.trueChild, ConditionNode) and isinstance(node.falseChild, ConditionNode):
                f.write('{0}if({1})\n'.format(self.get_indent_str(indent) if not nested_if else '', cond_str))
                self.write_node(node.trueChild, f, indent+1)
                f.write('{0}else '.format(self.get_indent_str(indent)))
                self.write_node(node.falseChild, f, indent)
            elif isinstance(node.trueChild, ConditionNode):
                if node.falseChild is None:
                    f.write('{0}if({1})\n'.format(self.get_indent_str(indent) if not nested_if else '',
                                                  cond_str))
                    self.write_node(node.trueChild, f, indent+1)
                else:
                    f.write('{0}if({1}){2}\n'.format(self.get_indent_str(indent) if not nested_if else '',
                                                     neg_cond_str, '{' if else_has_bracket else ''))
                    self.write_node(node.falseChild, f, indent+1)
                    f.write('{0}{1}else '.format(self.get_indent_str(indent), '} ' if else_has_bracket else ''))
                    self.write_node(node.trueChild, f, indent, True)
            else:
                if node.trueChild is None:
                    f.write('{0}if({1})\n'.format(self.get_indent_str(indent) if not nested_if else '',
                                                  neg_cond_str))
                    self.write_node(node.falseChild, f, indent+1)
                else:
                    f.write('{0}if({1}){2}\n'.format(self.get_indent_str(indent) if not nested_if else '',
                                                     cond_str, '{' if then_has_bracket else ''))
                    self.write_node(node.trueChild, f, indent+1)
                    f.write('{0}{1}else '.format(self.get_indent_str(indent), '} ' if then_has_bracket else ''))
                    self.write_node(node.falseChild, f, indent, True)
        elif isinstance(node, LoopNode):
            condition_exp = node.condition
            cond_str = str(condition_exp)
            cond_str = cond_str if cond_str[0] != '(' else cond_str[1:-1]
            body_has_brackets = self.needs_brackets(node.body)
            if node.type == LoopType.PRE_TESTED or node.type == LoopType.ENDLESS:
                f.write("{0}while({1}){2}\n".format(self.get_indent_str(indent),
                                                    cond_str, '{' if body_has_brackets else ''))
                self.write_node(node.body, f, indent + 1)
                if body_has_brackets:
                    self.write_closing_bracket(indent, f)
            elif node.type == LoopType.POST_TESTED:
                f.write("{0}do{1}\n".format(self.get_indent_str(indent), '{' if body_has_brackets else ''))
                self.write_node(node.body, f, indent + 1)
                f.write("{0}{1}while({2});\n".format(self.get_indent_str(indent),
                                                     '}' if body_has_brackets else '', cond_str))
        elif isinstance(node, ForNode):
            body_has_brackets = self.needs_brackets(node.body)
            f.write('{0}{1}{2}\n'.format(self.get_indent_str(indent), node.header_str(), '{' if body_has_brackets else ''))
            self.write_node(node.body, f, indent + 1)
            if body_has_brackets:
                self.write_closing_bracket(indent, f)
        elif isinstance(node, SwitchNode):
            f.write("{0}switch({1}){\n".format(self.get_indent_str(indent), node.testedVariableName))
            for c in node.cases:
                for v in c.caseValues:
                    f.write("{0}case {1}:\n".format(self.get_indent_str(indent + 1), v))
                self.write_node(c.node, f, indent + 2)
                if c.endsWithBreak:
                    f.write("{0}break\n".format(self.get_indent_str(indent + 2)))
            if node.defaultNode is not None:
                f.write("{0}default :\n".format(self.get_indent_str(indent + 1)))
                self.write_node(node.defaultNode, f, indent + 2)
            self.write_closing_bracket(indent, f)
        elif isinstance(node, Instruction) or isinstance(node, Expression):
            f.write("{0}{1};\n".format(self.get_indent_str(indent), str(node)))

    @staticmethod
    def needs_brackets(stmt):
        return isinstance(stmt, SequenceNode) and len(stmt.children) > 1

    def write_closing_bracket(self, indent, f):
        f.write('{0}{1}\n'.format(self.get_indent_str(indent), '}'))

    @staticmethod
    def get_indent_str(indent):
        return "  " * indent
