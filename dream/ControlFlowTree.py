# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from sympy import Not, And, true, Symbol, Or
from sympy.logic.boolalg import to_cnf, simplify_logic
from sys import maxint
from dream.ir.expressions import Expression
from dream.ir.instructions import Instruction, Break, Return
from dream.logic import conditions_equal, get_AND_remaining_term, get_arguments_number, is_trivial_condition, has_compound_trivial_condition, get_condition_from_logic_expression, get_negated_condition, alias_free_expression


class FunctionSignature:
    def __init__(self, name, parameters, return_value):
        self.name = name
        self.parameters = parameters
        self.return_value = return_value

    def __str__(self):
        param_str = ""
        for param in self.parameters:
            param_str += str(param) + ", "
        if len(param_str) > 2:
            param_str = param_str[:-2]
        return self.get_ret_type() + " " + self.name + "(" + param_str + ")"

    def get_ret_type(self):
        return str(self.return_value) if self.return_value is not None else ""


class CFTNode(object):
    def __init__(self, reaching_condition):
        self.reaching_condition = to_cnf(reaching_condition, simplify=True)
        self.ends_with_break = False
        
    def getChildCodeNodes(self):
        return []
    
    def getLeafNodes(self):
        return []

    def is_pure_break(self):
        return False

    def is_break_node(self):
        return self.ends_with_break

    def is_return_node(self):
        return False

    def replace_child_stmt(self, old_stmt, new_stmt):
        pass

    def deep_copy(self):
        pass


class CodeNode(CFTNode):
    def __init__(self, reaching_condition, ast, index):
        CFTNode.__init__(self, reaching_condition)
        self.ast = ast
        self.index = index
        self.is_latching_node = False

    def is_break_node(self):
        if isinstance(self.ast, Instruction):
            return isinstance(self.ast, Break)
        return self.ast.is_break_node()
        #return self.ast.ends_with_break

    def is_pure_break(self):
        if isinstance(self.ast, CFTNode):
            return self.ast.is_pure_break()
        else:
            return isinstance(self.ast, Break)

    def is_return_node(self):
        if isinstance(self.ast, CFTNode):
            return self.ast.is_return_node()
        else:
            return isinstance(self.ast, Return)

    def getLeafNodes(self):
        return [self]

    def get_refined_node(self, replace_by_ast=False):
        if replace_by_ast:
            if self.reaching_condition == true:
                return self.ast
            else:
                return ConditionNode(self.reaching_condition, self.ast, None)
        else:
            if self.reaching_condition == true:
                return self
            else:
                refined_node = ConditionNode(self.reaching_condition, self, None)
                self.reaching_condition = true
                return refined_node


class HelperNode(CFTNode):
    def __init__(self, reaching_condition, index):
        CFTNode.__init__(self, reaching_condition)
        self.index = index
    
    def getLeafNodes(self):
        return [self]


class SequenceNode(CFTNode):
    def __init__(self, reaching_condition, children):
        CFTNode.__init__(self, reaching_condition)
        self.children = children
        
    def getChildCodeNodes(self):
        l = []
        for n in self.children:
            l = l + ([n] if isinstance(n, CodeNode) else n.getChildCodeNodes())
        return l
    
    def getLeafNodes(self):
        l = []
        for n in self.children:
            l = l + n.getLeafNodes()
        return l

    def is_break_node(self):
        if not self.children:
            return False
        return isinstance(self.children[-1], Break)# or isinstance(self.children[-1], Return)
        #return self.children[-1].is_break_node()

    def is_pure_break(self):
        return len(self.children) == 1 and isinstance(self.children[0], Break)

    def is_return_node(self):
        return len(self.children) > 0 and isinstance(self.children[-1], Return)

    def has_no_breaks_in_middle(self):
        for child in self.children[:-1]:
            for l in child.getLeafNodes():
                if l.is_break_node():
                    return False
        return True

    def replace_child_stmt(self, old_stmt, new_stmt):
        self.children[self.children.index(old_stmt)] = new_stmt

    def replace_child_stmts(self, old_stmts, new_stmt):
        new_children = []
        new_stmt_added = False
        for s in self.children:
            if s not in old_stmts:
                new_children.append(s)
            elif not new_stmt_added:
                if isinstance(new_stmt, SequenceNode):
                    for s_new in new_stmt.children:
                        new_children.append(s_new)
                else:
                    new_children.append(new_stmt)
                new_stmt_added = True
        self.children = new_children

    def deep_copy(self):
        # FIXME children should not be none. This happened by /home/user/eval_dec/json/malware/zeus_p2p/sub_41302F.json
        return SequenceNode(self.reaching_condition, [child.deep_copy() for child in self.children if child is not None])


class ConditionNode(CFTNode):
    def __init__(self, condition, trueChild, falseChild, reaching_condition=true):
        CFTNode.__init__(self, reaching_condition)
        self.condition = condition
        self.trueChild = trueChild
        self.falseChild = falseChild
        
    def getChildCodeNodes(self):
        trueCodeNodes = [] if self.trueChild is None else ([self.trueChild] if isinstance(self.trueChild, CodeNode) else self.trueChild.getChildCodeNodes())
        falseCodeNodes = [] if self.falseChild is None else ([self.falseChild] if isinstance(self.falseChild, CodeNode) else self.falseChild.getChildCodeNodes())
        return trueCodeNodes + falseCodeNodes
    
    def getLeafNodes(self):
        trueLeafNodes = [] if self.trueChild is None else ([self.trueChild] if isinstance(self.trueChild, CodeNode) or isinstance(self.trueChild, HelperNode) else self.trueChild.getLeafNodes())
        falseLeafNodes = [] if self.falseChild is None else ([self.falseChild] if isinstance(self.falseChild, CodeNode) or isinstance(self.falseChild, HelperNode) else self.falseChild.getLeafNodes())
        return trueLeafNodes + falseLeafNodes

    def is_pure_break(self):
        if self.falseChild is None:
            if isinstance(self.trueChild, Instruction) or isinstance(self.trueChild, Expression):
                return isinstance(self.trueChild, Break)
            else:
                return self.trueChild.is_pure_break()
        return False

    def is_break_node(self):
        if self.trueChild is not None and self.falseChild is not None:
            return self.trueChild.is_break_node() and self.falseChild.is_break_node()
        return False

    def replace_child_stmt(self, old_stmt, new_stmt):
        if self.condition == old_stmt:
            self.condition = new_stmt
        elif self.trueChild == old_stmt:
            self.trueChild = new_stmt
        elif self.falseChild == old_stmt:
            self.falseChild = new_stmt

    def deep_copy(self):
        return ConditionNode(self.condition.deep_copy(),
                             self.trueChild.deep_copy() if self.trueChild is not None else None,
                             self.falseChild.deep_copy() if self.falseChild is not None else None)


class SwitchNode(CFTNode):
    def __init__(self, reaching_condition, cases, defaultNode, testedVariableName):
        CFTNode.__init__(self, reaching_condition)
        self.cases = cases
        self.defaultNode = defaultNode
        self.testedVariableName = testedVariableName
        self.ends_with_break = False
        
    def removeConditions(self):
        if self.defaultNode is not None:
            self.defaultNode.condition = true
        for case in self.cases:
            case.node.reaching_condition = true

    def getLeafNodes(self):
        leaf_nodes = []
        for case in self.cases:
            leaf_nodes = leaf_nodes + case.node.getLeafNodes()
        if self.defaultNode is not None:
            leaf_nodes = leaf_nodes + self.defaultNode.getLeafNodes()
        return leaf_nodes

    def deep_copy(self):
        switch_node = SwitchNode(self.reaching_condition,
                                 [case.deep_copy() for case in self.cases],
                                 self.defaultNode.deep_copy(),
                                 self.testedVariableName)
        switch_node.ends_with_break = self.ends_with_break
        return switch_node


class SwitchCase:
    def __init__(self, node, caseValues, endsWithBreak):
        self.node = node
        self.caseValues = caseValues
        self.endsWithBreak = endsWithBreak

    def deep_copy(self):
        return SwitchCase(self.node.deep_copy(), [v for v in self.caseValues], self.endsWithBreak)
        

class LoopNode(CFTNode):
    def __init__(self, loop_type, body, condition):
        CFTNode.__init__(self, true)
        self.type = loop_type
        self.body = body
        self.condition = condition
        self.ends_with_break = False

    def replace_child_stmt(self, old_stmt, new_stmt):
        if self.condition == old_stmt:
            self.condition = new_stmt
        elif self.body == old_stmt:
            self.body = new_stmt

    def deep_copy(self):
        loop_node = LoopNode(self.type, self.body.deep_copy(), self.condition.deep_copy())
        loop_node.ends_with_break = self.ends_with_break
        return loop_node


class ForNode(CFTNode):
    def __init__(self, init, cond, next, body):
        self.init = init
        self.cond = cond
        self.next = next
        self.body = body

    def header_str(self):
        h_str = 'for('
        for i in self.init:
            h_str += str(i) + ', '
        cond_str = str(self.cond)
        cond_str = cond_str if cond_str[0] != '(' else cond_str[1:-1]
        h_str = h_str[:-2] + '; {0}; '.format(cond_str)
        for n in self.next:
            h_str += str(n) + ', '
        return h_str[:-2] + ')'

    def replace_child_stmt(self, old_stmt, new_stmt):
        if self.cond == old_stmt:
            self.cond = new_stmt
        elif self.body == old_stmt:
            self.body = new_stmt
        elif self.next == old_stmt:
            self.next = new_stmt


class LoopType:
    PRE_TESTED = 1
    POST_TESTED = 2
    ENDLESS = 3


class BasicBlock(CFTNode):
    def __init__(self, instructions=None):
        CFTNode.__init__(self, true)
        if instructions is None:
            self.instructions = []
        else:
            self.instructions = instructions
        self.ends_with_break = False

    def __str__(self):
        if self.is_pure_break():
            return 'break;'
        else:
            inst_str = ""
            for inst in self.instructions:
                inst_str += str(inst) + "; "
            if self.ends_with_break:
                inst_str += "break;"
            return inst_str

    def is_pure_break(self):
        return len(self.instructions) == 0 and self.ends_with_break

    def to_string(self, indent_str):
        inst_str = ""
        for inst in self.instructions:
            inst_str += indent_str + str(inst) + "\n"
        if self.ends_with_break:
            inst_str += indent_str + "break;\n"
        return inst_str


class ConditionCluster:
    def __init__(self, condition):
        self.condition = condition
        self.trueNodes = []
        self.falseNodes = []
        self.remainingNodes = []
        
    def isValidCluster(self):
        trueCodeNodes = 0
        falseCodeNodes = 0
        for n in self.trueNodes:
            trueCodeNodes += 1 if self.isCodeNode(n) else 0
        for n in self.falseNodes:
            falseCodeNodes += 1 if self.isCodeNode(n) else 0
        return (trueCodeNodes >= 1 and falseCodeNodes >= 1) or (trueCodeNodes > 1) or (falseCodeNodes > 1)
    
    def isCodeNode(self, node):
        n = node
        if type(n) == tuple:
            n = n[0]
        return isinstance(n, CodeNode)
    
    def finializeCluster(self):
        trueNodesUpdatedCondition = []
        for n in self.trueNodes:
            n[0].reaching_condition = n[1]
            trueNodesUpdatedCondition.append(n[0])
        self.trueNodes = trueNodesUpdatedCondition
        falseNodesUpdatedCondition = []
        for n in self.falseNodes:
            n[0].reaching_condition = n[1]
            falseNodesUpdatedCondition.append(n[0])
        self.falseNodes = falseNodesUpdatedCondition


class SwitchCluster:
    def __init__(self):
        self.caseCandidates = []
        self.defaultCandidates = []
        self.remainingNodes = []


class ControlFlowTree:
    def __init__(self, children, reachability_map=None, conditions_map=None, latching_conditions=None):#remove default argument
        self.root = SequenceNode(True, children)
        self.reachability_map = reachability_map
        self.conditions_map = conditions_map
        self.latching_conditions = latching_conditions
        
    def refine(self):
        self.perform_condition_clustering()
        #self.structureSwitchRegions(self.root)
        #self.structureIfElseifElseRegions(self.root)
        self.finalize()

    def finalize(self):
        self.removeContainerNodesWithOneChild()

        self.refine_code_nodes_with_conditions()

        if not isinstance(self.root, SequenceNode):
            self.root = SequenceNode(true, [self.root])
        self.refine_break_nodes(self.root)
        if len(self.root.children) == 1:
            self.root = self.root.children[0]

        self.refine_condition_nodes_without_true_branch(self.root)

        self.unify_single_branched_condition_nodes(self.root)

        self.combine_pure_break_nodes(self.root)

    def replace_logic_symbols_by_conditions(self, ast_node):
        if isinstance(ast_node, ConditionNode):
            alias_free_condition = alias_free_expression(ast_node.condition, self.conditions_map)
            ast_node.condition = get_condition_from_logic_expression(alias_free_condition, self.conditions_map)
            self.replace_logic_symbols_by_conditions(ast_node.trueChild)
            self.replace_logic_symbols_by_conditions(ast_node.falseChild)
        elif isinstance(ast_node, LoopNode):
            alias_free_condition = alias_free_expression(ast_node.condition, self.conditions_map)
            ast_node.condition = get_condition_from_logic_expression(alias_free_condition, self.conditions_map)
            self.replace_logic_symbols_by_conditions(ast_node.body)
        elif isinstance(ast_node, SequenceNode):
            for s in ast_node.children:
                self.replace_logic_symbols_by_conditions(s)
        elif isinstance(ast_node, SwitchNode):
            for case in ast_node.cases:
                self.replace_logic_symbols_by_conditions(case.node)
            self.replace_logic_symbols_by_conditions(ast_node.defaultNode)

    def replace_basic_blocks_by_sequence(self, ast_node):
        if isinstance(ast_node, SequenceNode):
            new_children = []
            for c in ast_node.children:
                if isinstance(c, BasicBlock):
                    for stmt in c.instructions:
                        new_children.append(stmt)
                    if c.ends_with_break:
                        new_children.append(Break())
                else:
                    self.replace_basic_blocks_by_sequence(c)
                    new_children.append(c)
            ast_node.children = new_children
        elif isinstance(ast_node, ConditionNode):
            if isinstance(ast_node.trueChild, BasicBlock):
                ast_node.trueChild = self.basicBlock_to_sequence(ast_node.trueChild)
            else:
                self.replace_basic_blocks_by_sequence(ast_node.trueChild)

            if isinstance(ast_node.falseChild, BasicBlock):
                ast_node.falseChild = self.basicBlock_to_sequence(ast_node.falseChild)
            else:
                self.replace_basic_blocks_by_sequence(ast_node.falseChild)
        elif isinstance(ast_node, LoopNode):
            if isinstance(ast_node.body, BasicBlock):
                ast_node.body = self.basicBlock_to_sequence(ast_node.body)
            else:
                self.replace_basic_blocks_by_sequence(ast_node.body)
        elif isinstance(ast_node, SwitchNode):
            for c in ast_node.cases:
                if isinstance(c.node, BasicBlock):
                    c.node = self.basicBlock_to_sequence(c.node)
                else:
                    self.replace_basic_blocks_by_sequence(c.node)

    @staticmethod
    def basicBlock_to_sequence(bb):
        stmt_list = bb.instructions
        if bb.ends_with_break:
            stmt_list.append(Break())
        return SequenceNode(bb.reaching_condition, stmt_list)

    def combine_sequence_nodes_with_sequence_children(self, parent_node):
        if isinstance(parent_node, SequenceNode):
            new_children = []
            for child in parent_node.children:
                self.combine_sequence_nodes_with_sequence_children(child)
                if isinstance(child, SequenceNode):
                    new_children.extend(child.children)
                else:
                    new_children.append(child)
            parent_node.children = new_children
        elif isinstance(parent_node, ConditionNode):
            parent_node.trueChild = self.get_sequence_only_child(parent_node.trueChild)
            self.combine_sequence_nodes_with_sequence_children(parent_node.trueChild)
            parent_node.falseChild = self.get_sequence_only_child(parent_node.falseChild)
            self.combine_sequence_nodes_with_sequence_children(parent_node.falseChild)
        elif isinstance(parent_node, SwitchNode):
            for i in range(0, len(parent_node.cases)):
                parent_node.cases[i].node = self.get_sequence_only_child(parent_node.cases[i].node)
                self.combine_sequence_nodes_with_sequence_children(parent_node.cases[i].node)
            parent_node.defaultNode = self.get_sequence_only_child(parent_node.defaultNode)
            self.combine_sequence_nodes_with_sequence_children(parent_node.defaultNode)
        elif isinstance(parent_node, LoopNode):
            parent_node.body = self.get_sequence_only_child(parent_node.body)
            self.combine_sequence_nodes_with_sequence_children(parent_node.body)

    @staticmethod
    def get_sequence_only_child(node):
        child_node = node
        while isinstance(child_node, SequenceNode) and len(child_node.children) == 1:
            child_node = child_node.children[0]
        return child_node

    def refine_code_nodes_with_conditions(self):
        if isinstance(self.root, CodeNode):
            self.root = self.root.get_refined_node(replace_by_ast=False)
        else:
            self.refine_code_nodes(self.root, replace_by_ast=False)

    def replace_code_nodes_by_ast(self):
        if isinstance(self.root, CodeNode):
            self.root = self.root.get_refined_node(replace_by_ast=True)
        else:
            self.refine_code_nodes(self.root, replace_by_ast=True)

    def refine_code_nodes(self, node, replace_by_ast=False):
        if isinstance(node, SequenceNode):
            for i in range(0, len(node.children)):
                if isinstance(node.children[i], CodeNode):
                    node.children[i] = node.children[i].get_refined_node(replace_by_ast)
                else:
                    self.refine_code_nodes(node.children[i], replace_by_ast)
        elif isinstance(node, ConditionNode):
            if isinstance(node.trueChild, CodeNode):
                node.trueChild = node.trueChild.get_refined_node(replace_by_ast)
            else:
                self.refine_code_nodes(node.trueChild, replace_by_ast)

            if isinstance(node.falseChild, CodeNode):
                node.falseChild = node.falseChild.get_refined_node(replace_by_ast)
            else:
                self.refine_code_nodes(node.falseChild, replace_by_ast)
        elif isinstance(node, SwitchNode):
            for i in range(0, len(node.cases)):
                if isinstance(node.cases[i].node, CodeNode):
                    node.cases[i].node = node.cases[i].node.get_refined_node(replace_by_ast)
                else:
                    self.refine_code_nodes(node.cases[i].node, replace_by_ast)
            if isinstance(node.defaultNode, CodeNode):
                node.defaultNode = node.defaultNode.get_refined_node(replace_by_ast)
            else:
                self.refine_code_nodes(node.defaultNode, replace_by_ast)

    def combine_pure_break_nodes(self, parent_node):
        if isinstance(parent_node, ConditionNode):
            self.combine_pure_break_nodes(parent_node.trueChild)
            self.combine_pure_break_nodes(parent_node.falseChild)
        elif isinstance(parent_node, SequenceNode):
            for child in parent_node.children:
                self.combine_pure_break_nodes(child)
            i = 0
            while i < len(parent_node.children) - 1:
                n = parent_node.children[i]
                n_next = parent_node.children[i+1]
                if isinstance(n, ConditionNode) and isinstance(n_next, ConditionNode)\
                        and n.is_pure_break() and n_next.is_pure_break():
                    n.condition = simplify_logic(Or(n.condition, n_next.condition))
                    del parent_node.children[i+1]
                else:
                    i += 1

    def refine_condition_nodes_without_true_branch(self, parent_node):
        if isinstance(parent_node, SequenceNode):
            for child in parent_node.children:
                self.refine_condition_nodes_without_true_branch(child)
        elif isinstance(parent_node, ConditionNode):
            self.refine_condition_nodes_without_true_branch(parent_node.trueChild)
            self.refine_condition_nodes_without_true_branch(parent_node.falseChild)
            if self.is_empty_ast(parent_node.trueChild):
                parent_node.condition = simplify_logic(Not(parent_node.condition))
                parent_node.trueChild = parent_node.falseChild
                parent_node.falseChild = None

    @staticmethod
    def is_empty_ast(ast_node):
        return ast_node is None or (isinstance(ast_node, SequenceNode) and not ast_node.children)

    def unify_single_branched_condition_nodes(self, parent_node):
        if isinstance(parent_node, SequenceNode):
            for child in parent_node.children:
                self.unify_single_branched_condition_nodes(child)
        elif isinstance(parent_node, ConditionNode):
            self.unify_single_branched_condition_nodes(parent_node.trueChild)
            self.unify_single_branched_condition_nodes(parent_node.falseChild)
            if self.is_single_branched_conditional_node(parent_node):
                self.try_unify_single_branched_condition_node(parent_node)

    @staticmethod
    def is_single_branched_conditional_node(node):
        if isinstance(node, ConditionNode):
            return node.trueChild is None or node.falseChild is None

    def try_unify_single_branched_condition_node(self, n):
        if self.is_single_branched_conditional_node(n.trueChild):
            if n.trueChild.trueChild is not None:
                n.condition = simplify_logic(And(n.condition, n.trueChild.condition))
                n.trueChild = n.trueChild.trueChild
            else:
                n.condition = simplify_logic(And(n.condition, Not(n.trueChild.condition)))
                n.trueChild = n.trueChild.falseChild
        elif self.is_single_branched_conditional_node(n.falseChild):
            if n.falseChild.trueChild is not None:
                n.condition = simplify_logic(And(Not(n.condition), n.falseChild.condition))
                n.trueChild = n.falseChild.trueChild
            else:
                n.condition = simplify_logic(And(Not(n.condition), Not(n.falseChild.condition)))
                n.trueChild = n.falseChild.falseChild
            n.falseChild = None

    def refine_break_nodes(self, parent_node):
        if isinstance(parent_node, SequenceNode):
            new_children = []
            for child in parent_node.children:
                self.refine_break_nodes(child)
                serialized_children = self.try_serialize_node(child)
                if type(serialized_children) == list:
                    new_children.extend(serialized_children)
                else:
                    new_children.append(child)
            parent_node.children = new_children
        elif isinstance(parent_node, ConditionNode):
            self.refine_break_nodes(parent_node.trueChild)
            serialized_true_branch = self.try_serialize_node(parent_node.trueChild)
            if type(serialized_true_branch) == list:
                parent_node.trueChild = SequenceNode(true, serialized_true_branch)
            self.refine_break_nodes(parent_node.falseChild)
            serialized_false_branch = self.try_serialize_node(parent_node.falseChild)
            if type(serialized_false_branch) == list:
                parent_node.falseChild = SequenceNode(true, serialized_false_branch)

    def try_serialize_node(self, node):
        if isinstance(node, ConditionNode):
            if node.trueChild is not None and node.falseChild is not None:
                if node.trueChild.is_break_node():
                    return self.serialize_condition_node_with_break(node, true_branch_ends_with_break=True)
                elif node.falseChild.is_break_node():
                    return self.serialize_condition_node_with_break(node, true_branch_ends_with_break=False)
            #if self.is_break_node(node.trueChild) and not (node.falseChild is None):
            #    return self.serialize_condition_node_with_break(node, true_branch_ends_with_break=True)
            #elif self.is_break_node(node.falseChild) and not (node.trueChild is None):
            #    return self.serialize_condition_node_with_break(node, true_branch_ends_with_break=False)
        return node

    def serialize_condition_node_with_break(self, condition_node, true_branch_ends_with_break):
        children = [condition_node]
        child2 = condition_node.falseChild if true_branch_ends_with_break else condition_node.trueChild
        if not true_branch_ends_with_break:
            children[0].trueChild = None
        else:
            children[0].falseChild = None

        remaining_children = self.try_serialize_node(child2)
        if type(remaining_children) == list:
            children.extend(remaining_children)
        elif isinstance(remaining_children, SequenceNode):
            children.extend(remaining_children.children)
        else:
            children.append(remaining_children)
        return children

    """*********************Conditional Clustering***********************"""
    
    def perform_condition_clustering(self):
        self.condition_cluster_sequence_node(self.root)
        self.removeHelperNodes(self.root)
        self.removeContainerNodesWithOneChild()
            
    def condition_cluster_sequence_node(self, containerNode):
        conditionCluster = self.getNextConditionCluster(containerNode)
        failedConditions = None
        while conditionCluster is not None:
            conditionNode = self.construct_condition_node(conditionCluster)
            if isinstance(conditionNode.trueChild, SequenceNode):
                self.condition_cluster_sequence_node(conditionNode.trueChild)
            if isinstance(conditionNode.falseChild, SequenceNode):
                self.condition_cluster_sequence_node(conditionNode.falseChild)
                
            if not conditionCluster.remainingNodes:
                containerNode.children = [conditionNode]
                break
            #else:
            newChildren = self.addNodeAndPreserveTopologicalOrder(conditionCluster.remainingNodes, conditionNode)
            if newChildren is not None:
                containerNode.children = newChildren
            else:
                if failedConditions is None:
                    failedConditions = []
                failedConditions.append(conditionCluster.condition)
            conditionCluster = self.getNextConditionCluster(containerNode, failedConditions)
    
    def construct_condition_node(self, conditionCluster):
        orig_trueChild = self.makeCFTNode(conditionCluster.trueNodes)
        orig_falseChild = self.makeCFTNode(conditionCluster.falseNodes)
        if orig_trueChild is None:
            return ConditionNode(simplify_logic(Not(conditionCluster.condition)), orig_falseChild, None)
        elif orig_falseChild is None:
            return ConditionNode(simplify_logic(conditionCluster.condition), orig_trueChild, None)
        else:
            condition = simplify_logic(conditionCluster.condition)
            negatedCondition = simplify_logic(Not(conditionCluster.condition))
            conditionLength = get_arguments_number(condition)
            negatedConditionLength = get_arguments_number(negatedCondition)
            if conditionLength < negatedConditionLength:
                return ConditionNode(condition, orig_trueChild, orig_falseChild)
            elif negatedConditionLength < conditionLength:
                return ConditionNode(negatedCondition, orig_falseChild, orig_trueChild)
            elif get_arguments_number(condition, ignoreNot=False) < get_arguments_number(negatedCondition, ignoreNot=False):
                return ConditionNode(condition, orig_trueChild, orig_falseChild)
            else:
                return ConditionNode(negatedCondition, orig_falseChild, orig_trueChild)
             
    def addNodeAndPreserveTopologicalOrder(self, node_list, newNode):
        for index in range(0, len(node_list)):
            n = node_list[index]
            if self.doesReach(newNode, n):
                if not self.doesReach(n, newNode):
                    return node_list[:index] + [newNode] + node_list[index:]
                else:
                    return None
        return node_list + [newNode]
    
    def removeHelperNodes(self, parentNode):
        if isinstance(parentNode, SequenceNode):
            parentNode.children = [n for n in parentNode.children if not isinstance(n, HelperNode)]
            for n in parentNode.children:
                self.removeHelperNodes(n)
        elif isinstance(parentNode, ConditionNode):
            self.removeHelperNodes(parentNode.trueChild)
            self.removeHelperNodes(parentNode.falseChild)
            
    def removeContainerNodesWithOneChild(self):
        while self.isContainerNodeWithOneChild(self.root):
            self.root = self.root.children[0]
        self.removeContainerChildrenWithOneChild(self.root)
            
    def removeContainerChildrenWithOneChild(self, parentNode):
        if isinstance(parentNode, ConditionNode):
            if self.isContainerNodeWithOneChild(parentNode.trueChild):#while
                parentNode.trueChild = parentNode.trueChild.children[0]
            self.removeContainerChildrenWithOneChild(parentNode.trueChild)
            if self.isContainerNodeWithOneChild(parentNode.falseChild):#while
                parentNode.falseChild = parentNode.falseChild.children[0]
            self.removeContainerChildrenWithOneChild(parentNode.falseChild)
        elif isinstance(parentNode, SequenceNode):
            for index in range(0, len(parentNode.children)):
                if self.isContainerNodeWithOneChild(parentNode.children[index]):#while
                    parentNode.children[index] = parentNode.children[index].children[0]
                self.removeContainerChildrenWithOneChild(parentNode.children[index])
        elif isinstance(parentNode, SwitchNode):
            for index in range(0, len(parentNode.cases)):
                if self.isContainerNodeWithOneChild(parentNode.cases[index].node):
                    parentNode.cases[index].node = parentNode.cases[index].node.children[0]
                self.removeContainerChildrenWithOneChild(parentNode.cases[index].node)

            if self.isContainerNodeWithOneChild(parentNode.defaultNode):
                parentNode.defaultNode = parentNode.defaultNode.children[0]
            self.removeContainerChildrenWithOneChild(parentNode.defaultNode)

    def isContainerNodeWithOneChild(self, node):
        return isinstance(node, SequenceNode) and len(node.children) == 1
    
    def doesReach(self, node1, node2):
        leafNodes2 = node2.getLeafNodes()
        for leafNode1 in node1.getLeafNodes():
            for leafNode2 in leafNodes2:
                if self.reachability_map[leafNode1.index][leafNode2.index]:
                    return True
        return False
        
    def canSwitchNodesAndPreserveTopologicalOrder(self, node1, node2, nodes_list):
        start_index = nodes_list.index(node1)
        end_index = nodes_list.index(node2)
        for index in range(start_index, end_index):
            n1 = nodes_list[index]
            n2 = nodes_list[index + 1]
            if self.doesReach(n1, n2):
                return False
        return True
                    
    def makeCFTNode(self, nodes_list):
        numCodeNodes = self.codeNodesNumber(nodes_list)
        if numCodeNodes == 1:
            for n in nodes_list:
                if isinstance(n, CodeNode):
                    return n
        elif numCodeNodes > 1:
            return SequenceNode(true, nodes_list)
        else:
            return None
                    
    def codeNodesNumber(self, nodes_list):
        num = 0
        for n in nodes_list:
            if isinstance(n, CodeNode):
                num += 1
        return num
    
    def getNextConditionCluster(self, parentNode, failedConditions=None):
        clusteringCondition = self.getIfElseCondition(parentNode, failedConditions)
        if clusteringCondition is not None:
            conditionCluster = self.clusterCondition(clusteringCondition, parentNode.children)
            if conditionCluster is not None:
                return conditionCluster
        for node in parentNode.children:
            if not conditions_equal(node.reaching_condition, true) and not self.isFailedCondition(node.reaching_condition, failedConditions):
                conditionCluster = self.clusterCondition(node.reaching_condition, parentNode.children)
                if conditionCluster is not None:
                    return conditionCluster
        return None
    
    def getIfElseCondition(self, parentNode, failedConditions=None):
        for id1 in range(0, len(parentNode.children)):
            child1 = parentNode.children[id1]
            if isinstance(child1, CodeNode):
                for id2 in range(id1 + 1, len(parentNode.children)):
                    child2 = parentNode.children[id2]
                    if isinstance(child2, CodeNode):
                        if conditions_equal(Not(child1.reaching_condition), child2.reaching_condition):
                            candidate_condition = child1.reaching_condition if type(child1.reaching_condition) is not Not else child2.reaching_condition
                            if not self.isFailedCondition(candidate_condition, failedConditions):
                                return candidate_condition
        # for child1 in parentNode.children:
        #     for child2 in parentNode.children:
        #         if isinstance(child1, CodeNode) and isinstance(child2, CodeNode):
        #             if conditions_equal(child1.reaching_condition, Not(child2.reaching_condition)):
        #                 candidateCondition = child1.reaching_condition if type(child1.reaching_condition) is not Not else child2.reaching_condition
        #                 if not self.isFailedCondition(candidateCondition, failedConditions):
        #                     return candidateCondition
        return None
    
    def isFailedCondition(self, condition, failedConditions):
        if failedConditions is None:
            return False
        for failedCondition in failedConditions:
            if conditions_equal(condition, failedCondition):
                return True
        return False
                
    def cluster_dominating_condition(self, cond_cnf, nodes):
        cluster = ConditionCluster(cond_cnf)
        for node in nodes:
            remaining_cond = get_AND_remaining_term(cond_cnf, node.reaching_condition)
            if remaining_cond is not None:
                cluster.trueNodes.append((node, remaining_cond))
            else:
                return None

        cluster.finializeCluster()
        return cluster

    def clusterCondition(self, cond_cnf, nodes):
        cluster = ConditionCluster(cond_cnf)
        not_cond_cnf = None
        for node in nodes:
            remaining_cond = get_AND_remaining_term(cond_cnf, node.reaching_condition)
            if remaining_cond is not None:
                cluster.trueNodes.append((node, remaining_cond))
            else:
                if not_cond_cnf is None:
                    not_cond_cnf = to_cnf(~cond_cnf, simplify=True)
                remaining_cond = get_AND_remaining_term(not_cond_cnf, node.reaching_condition)
                if remaining_cond is not None:
                    cluster.falseNodes.append((node, remaining_cond))
                else:
                    cluster.remainingNodes.append(node)
            
        if cluster.isValidCluster():
            cluster.finializeCluster()
            return cluster
        
        return None

    """*******************SWITCH*************************"""
    
    def structureSwitchRegions(self, parentNode):
        if isinstance(parentNode, SequenceNode):
            for childNode in parentNode.children:
                self.structureSwitchRegions(childNode)
            self.structureSwitchRegionsInContainerNode(parentNode)
        elif isinstance(parentNode, ConditionNode):
            if parentNode.trueChild is not None:
                self.structureSwitchRegions(parentNode.trueChild)
            if parentNode.falseChild is not None:
                self.structureSwitchRegions(parentNode.falseChild)
            
    def structureSwitchRegionsInContainerNode(self, containerNode):
        if len(containerNode.children) > 2 and self.conditions_map is not None:#this condition should be deleted
            childrenCopy = containerNode.children[:]
            newChildren = []
            while len(childrenCopy) > 0:
                node = childrenCopy[0]
                if self.isCaseCandidate(node) or self.isDefaultCandidate(node):
                    switchVariableName = self.getTestedVariableName(node.reaching_condition)
                    switchInfo = self.tryStructureSwitchRegion(childrenCopy, switchVariableName, containerNode.reaching_condition)
                    if switchInfo is not None:
                        newChildren.append(switchInfo[0])
                        childrenCopy = switchInfo[1]
                    else:
                        newChildren.append(node)
                        del childrenCopy[0]     
                else:
                    newChildren.append(node)
                    del childrenCopy[0]
            containerNode.children = newChildren
    
    def tryStructureSwitchRegion(self, nodeList, switchVariableName, enclosingCondition):
        switchCluster = self.getSwitchNodeCandidates(nodeList, switchVariableName)
        if len(switchCluster.caseCandidates) > 1 or (len(switchCluster.caseCandidates) > 0 and len(switchCluster.defaultCandidates) > 0):
            defaultNode = switchCluster.defaultCandidates[0] if len(switchCluster.defaultCandidates) == 1\
                            else (SequenceNode(true, switchCluster.defaultCandidates) if len(switchCluster.defaultCandidates) > 1 else None)
            switchCases = self.constructSwitchCases(switchCluster.caseCandidates)
            if switchCases is not None:
                switchNode = SwitchNode(enclosingCondition, switchCases, defaultNode, switchVariableName)
                switchNode.removeConditions()# not correct
                return (switchNode, switchCluster.remainingNodes)
        return None
    
    def constructSwitchCases(self, caseNodes):
        caseClusters = self.computeCaseClusters(caseNodes)
        if caseClusters is not None:
            switchCases = []
            for cluster in caseClusters:
                self.constructSwitchCase(cluster, switchCases)
            return switchCases
        return None
        
    def constructSwitchCase(self, caseCluster, switchCases):
        handledCaseConditions = set()
        for index in range(0, len(caseCluster)):
            caseNode = caseCluster[index]
            uniqueConditions = set(self.getCaseConditionElements(caseNode.reaching_condition)).difference(handledCaseConditions)
            handledCaseConditions.update(uniqueConditions)
            caseValues = [hl_cond.rhsExpression for hl_cond in [self.conditions_map[c] for c in uniqueConditions]]
            endsWithBreak = index == len(caseCluster) - 1
            switchCases.append(SwitchCase(caseNode, caseValues, endsWithBreak))
    
    def computeCaseClusters(self, caseNodes):
        caseClusters = []
        while len(caseNodes) > 0:
            cluster = self.getCaseCluster(0, caseNodes)
            if cluster is None:
                return None
            caseClusters.append(cluster)
            caseNodes = [n for n in caseNodes if n not in cluster]
        return caseClusters
                    
    def getCaseCluster(self, node_index, node_list):
        node = node_list[node_index]
        cluster = [node]
        nextNode, nextIndex = self.findNextFallThroughNode(node_index, node_list)
        while nextNode is not None:
            cluster.append(nextNode)
            nextNode, nextIndex = self.findNextFallThroughNode(nextIndex, node_list)
        if nextIndex == 0:
            return cluster
        return None
            
    def findNextFallThroughNode(self, caseNodeIndex, caseNodeList):
        candidates = []
        node = caseNodeList[caseNodeIndex]
        caseCondElements = self.getCaseConditionElements(node.reaching_condition)
        minDifference = maxint
        for index in range(caseNodeIndex + 1, len(caseNodeList)):
            nextCaseNode = caseNodeList[index]
            nextCaseCondElements = self.getCaseConditionElements(nextCaseNode.reaching_condition)
            if caseCondElements.issubset(nextCaseCondElements):
                currentDifference = len(nextCaseCondElements) - len(caseCondElements)
                if minDifference > currentDifference:
                    minDifference = currentDifference
                    candidates = [(nextCaseNode, index)]
                elif minDifference == currentDifference:
                    candidates.append((nextCaseNode, index))
        return candidates[0] if len(candidates) == 1 else (None, len(candidates)) # if more than two are found --> handle
        
    def getCaseConditionElements(self, condition):
        return set([condition] if isinstance(condition, Symbol) else [arg for arg in condition.args])

    def doesReachNodeList(self, nodeList1, nodeList2):
        for n1 in nodeList1:
            for n2 in nodeList2:
                if self.doesReach(n1, n2):
                    return True
        return False
    
    def getSwitchNodeCandidates(self, nodeList, switchVariableName):
        switchNodes = []
        switchCluster = SwitchCluster()
        for childNode in nodeList:
            if self.isCaseCandidate(childNode, switchVariableName)\
                and not self.doesReachNodeList(switchCluster.defaultCandidates, [childNode])\
                and not self.doesReachNodeList(switchCluster.remainingNodes, [childNode]):
                switchCluster.caseCandidates.append(childNode)
                switchNodes.append(childNode)
            elif self.isDefaultCandidate(childNode, switchVariableName)\
                and not self.doesReachNodeList(switchCluster.remainingNodes, [childNode]):
                switchCluster.defaultCandidates.append(childNode)
                switchNodes.append(childNode)
            else:
                switchCluster.remainingNodes.append(childNode)
        return switchCluster
    
    def isCaseCandidate(self, node, switchVariableName=""):
        condition = node.reaching_condition
        if isinstance(condition, Symbol):
            return self.conditions_map[condition].does_test_equality_with_scalar(switchVariableName)
        return self.isCaseFallThroughCandidate(node, switchVariableName)
        
    def isCaseFallThroughCandidate(self, node, switchVariableName=""):
        condition = node.reaching_condition
        if type(condition) == Or:
            testedVariableName = switchVariableName if switchVariableName != "" else self.getTestedVariableName(condition)
            if testedVariableName is None:
                return False
            for arg in condition.args:
                if isinstance(arg, Symbol):
                    cond = self.conditions_map[arg]
                    if not cond.does_test_equality_with_scalar(testedVariableName):
                        return False
                else:
                    return False
            return True
        return False
    
    def isDefaultCandidate(self, node, switchVariableName=""):
        condition = node.reaching_condition
        if self.isSimpleConditionCandidateOfDafaultNode(condition, switchVariableName):
            return True
        return self.isDafaultFallThroughCandidate(node, switchVariableName)
    
    def isSimpleConditionCandidateOfDafaultNode(self, simpleCondition, testedVariableName=""):
        if isinstance(simpleCondition, Symbol):
            return self.conditions_map[simpleCondition].does_test_larger_than_scalar(testedVariableName)
        if type(simpleCondition) == Not and isinstance(simpleCondition.args[0], Symbol):
            return self.conditions_map[simpleCondition.args[0]].does_test_smaller_than_scalar(testedVariableName)
        return False
    
    def isDafaultFallThroughCandidate(self, node, switchVariableName=""):
        condition = node.reaching_condition
        if type(condition) == Or:
            #testedVariableName = self.getTestedVariableName(condition)
            testedVariableName = switchVariableName if switchVariableName != "" else self.getTestedVariableName(condition)
            if testedVariableName is None:
                return False
            for condArg in condition.args:
                if not self.isSimpleConditionCandidateOfDafaultNode(condArg, testedVariableName):
                    if not (isinstance(condArg, Symbol) and self.conditions_map[condArg].does_test_equality_with_scalar(testedVariableName)):
                        return False
            return True
        return False
    
    def getTestedVariableName(self, condition):
        if isinstance(condition, Symbol):
            return str(self.conditions_map[condition].lhsExpression)
        elif type(condition) == Or or type(condition) == Not:
            firstArg = condition.args[0]
            if isinstance(firstArg, Symbol):
                return str(self.conditions_map[firstArg].lhsExpression)
        return None
        
    """*********************IF Else***********************"""
    
    def structureIfElseifElseRegions(self, parentNode):
        if isinstance(parentNode, SequenceNode):
            for childNode in parentNode.children:
                self.structureIfElseifElseRegions(childNode)
            self.structureIfElseifElseRegionsInContainerNode(parentNode)
        elif isinstance(parentNode, ConditionNode):
            if parentNode.trueChild is not None:
                self.structureIfElseifElseRegions(parentNode.trueChild)
            if parentNode.falseChild is not None:
                self.structureIfElseifElseRegions(parentNode.falseChild)
    
    def structureIfElseifElseRegionsInContainerNode(self, containerNode):
        newChildren = []
        clusterNodes, succNodes = self.computeNextReachabilityCluster(containerNode.children)
        while len(clusterNodes) > 0:
            
            for n in reversed(succNodes):
                newChildren.insert(0, n)
                
            if has_compound_trivial_condition([n.reaching_condition for n in clusterNodes]):
                clusterNodes.sort(key=lambda n: get_arguments_number(n.reaching_condition))
                ifElseNode = self.computeIfElseTree(clusterNodes)
                newChildren.insert(0, ifElseNode)
            else:
                for n in reversed(clusterNodes):
                    newChildren.insert(0, n)
            
            containerNode.children = [n for n in containerNode.children if n not in clusterNodes + succNodes]
            clusterNodes, succNodes = self.computeNextReachabilityCluster(containerNode.children)
        
        for n in reversed(succNodes):
            newChildren.insert(0, n)
        containerNode.children = newChildren
    
    def computeIfElseTree(self, ifElseCluster, removeConditions=False):
        if len(ifElseCluster) == 1:
            if removeConditions:
                ifElseCluster[0].reaching_condition = true
            return ifElseCluster[0]
        else:
            trueChild = ifElseCluster[0]
            condition = trueChild.reaching_condition
            trueChild.reaching_condition = true
            falseChild = self.computeIfElseTree(ifElseCluster[1:], True)
            return ConditionNode(condition, trueChild, falseChild)
    
    def computeNextReachabilityCluster(self, nodeList):
        clusterNodes = []
        succNodes = []
        for node in reversed(nodeList):
            if not self.doesReachNodeList([node], clusterNodes):
                if not is_trivial_condition(node.reaching_condition):
                        clusterNodes.insert(0, node)
                else:
                    succNodes.insert(0, node)
        return (clusterNodes, succNodes)

    """*********************Cyclic***********************"""

    def refine_cyclic(self):
        if isinstance(self.root, SequenceNode):
            first_node = self.root.children[0]
            last_node = self.root.children[-1]
            if isinstance(first_node, ConditionNode):
                if first_node.falseChild is None and isinstance(first_node.trueChild, SequenceNode):
                    child_sequence = first_node.trueChild.children
                    if isinstance(child_sequence[0], ConditionNode):
                        if child_sequence[0].falseChild is None and child_sequence[0].trueChild.is_pure_break():
                            break_child = ConditionNode(And(first_node.condition, child_sequence[0].condition), child_sequence[0].trueChild, None)
                            del first_node.trueChild.children[0]
                            if len(first_node.trueChild.children) == 1:
                                first_node.trueChild = first_node.trueChild.children[0]
                            self.root.children.insert(0, break_child)
                            first_node = self.root.children[0]

            if isinstance(first_node, ConditionNode) and first_node.is_pure_break():
                loop_condition = simplify_logic(Not(first_node.condition))
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                del self.root.children[0]
                loop_body = self.root.children[0] if len(self.root.children) == 1 else self.root
                self.root = LoopNode(LoopType.PRE_TESTED, loop_body, loop_condition)
            elif isinstance(last_node, ConditionNode) and last_node.is_pure_break():
                    loop_condition = simplify_logic(Not(last_node.condition))
                    self.replace_code_nodes_by_ast()
                    self.combine_sequence_nodes_with_sequence_children(self.root)
                    del self.root.children[-1]
                    loop_body = self.root.children[0] if len(self.root.children) == 1 else self.root
                    self.root = LoopNode(LoopType.POST_TESTED, loop_body, loop_condition)
            elif self.has_nested_post_tested_loop():
                loop_condition = simplify_logic(Not(last_node.condition))
                del self.root.children[-1]
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                loop_body = self.root.children[0] if len(self.root.children) == 1 else self.root
                inner_loop = LoopNode(LoopType.POST_TESTED, loop_body, loop_condition)
                remaining_children = [last_node.trueChild] if not isinstance(last_node.trueChild, SequenceNode) else last_node.trueChild.children
                self.root = SequenceNode(true, [inner_loop] + remaining_children)
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                self.refine_cyclic()
            elif isinstance(last_node, Break):
                del self.root.children[-1]
            else:
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                self.root = LoopNode(LoopType.ENDLESS, self.root, true)
        elif isinstance(self.root, ConditionNode):
            true_branch_breaks = self.has_break_nodes(self.root.trueChild.getLeafNodes())
            false_branch_breaks = self.has_break_nodes(self.root.falseChild.getLeafNodes())
            if true_branch_breaks and not false_branch_breaks and not self.root.falseChild.is_return_node():
                true_branch = self.root.trueChild
                remaining_children = [true_branch] if not isinstance(true_branch, SequenceNode) else true_branch.children
                self.root.trueChild = None
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                inner_pretested_loop = LoopNode(LoopType.PRE_TESTED, self.root.falseChild, simplify_logic(Not(self.root.condition)))
                self.root = SequenceNode(true, [inner_pretested_loop] + remaining_children)
                self.refine_cyclic()
            elif false_branch_breaks and not true_branch_breaks and not self.root.trueChild.is_return_node():
                false_branch = self.root.falseChild
                remaining_children = [false_branch] if not isinstance(false_branch, SequenceNode) else false_branch.children
                self.root.falseChild = None
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                inner_pretested_loop = LoopNode(LoopType.PRE_TESTED, self.root.trueChild, simplify_logic(self.root.condition))
                self.root = SequenceNode(true, [inner_pretested_loop] + remaining_children)
                self.refine_cyclic()
            else:
                self.replace_code_nodes_by_ast()
                self.combine_sequence_nodes_with_sequence_children(self.root)
                self.root = LoopNode(LoopType.ENDLESS, self.root, true)

    def has_nested_post_tested_loop(self):
        if isinstance(self.root, SequenceNode) and isinstance(self.root.children[-1], ConditionNode):
            if self.root.has_no_breaks_in_middle() and self.root.children[-1].falseChild is None:
                return True
        return False

    def is_loop_to_seq(self):
        pass

    @staticmethod
    def has_break_nodes(nodes):
        for n in nodes:
            if n.is_break_node():
                return True
        return False

    @staticmethod
    def ends_with_break_or_return(node):
        if isinstance(node, CFTNode):
            return node.is_break_node()
        else:
            return isinstance(node, Break) or isinstance(node, Return)

    """*********************OUTPUT***********************"""
    
    def write_to_path(self, path):
        f = open(path, 'w')
        self.writeNode(self.root, f, 0)
        f.close()

    def write(self, fileName):
        f = open('/home/yakdan/Bilder/' + fileName, 'w')
        self.writeNode(self.root, f, 0)
        f.close()
        
    def writeNode(self, node, f, indent, nestedIf=False):
        assert not isinstance(node, CodeNode)
        if isinstance(node, SequenceNode):
            for n in node.children:
                self.writeNode(n, f, indent)
        elif isinstance(node, ConditionNode):
            condition_exp = get_condition_from_logic_expression(node.condition, self.conditions_map)
            negated_condition_exp = get_negated_condition(condition_exp)
            #negated_condition_exp = get_condition_from_logic_expression(simplify_logic(Not(node.condition)), self.conditions_map)
            if not isinstance(node.trueChild, ConditionNode) and not isinstance(node.falseChild, ConditionNode):
                f.write('{0}if({1})\n'.format(self.getIndentStr(indent) if not nestedIf else '', str(condition_exp)))
                self.writeNode(node.trueChild, f, indent+1)
                if node.falseChild is not None:
                    f.write('{0}else\n'.format(self.getIndentStr(indent)))
                    self.writeNode(node.falseChild, f, indent+1)
            elif isinstance(node.trueChild, ConditionNode) and isinstance(node.falseChild, ConditionNode):
                f.write('{0}if({1})\n'.format(self.getIndentStr(indent) if not nestedIf else '', str(condition_exp)))
                self.writeNode(node.trueChild, f, indent+1)
                f.write('{0}else '.format(self.getIndentStr(indent)))
                self.writeNode(node.falseChild, f, indent)
            elif isinstance(node.trueChild, ConditionNode):
                if node.falseChild is None:
                    f.write('{0}if({1})\n'.format(self.getIndentStr(indent) if not nestedIf else '', str(condition_exp)))
                    self.writeNode(node.trueChild, f, indent+1)
                else:
                    f.write('{0}if({1})\n'.format(self.getIndentStr(indent) if not nestedIf else '', negated_condition_exp))
                    self.writeNode(node.falseChild, f, indent+1)
                    f.write('{0}else '.format(self.getIndentStr(indent)))
                    self.writeNode(node.trueChild, f, indent, True)
            else:
                if node.trueChild is None:
                    f.write('{0}if({1})\n'.format(self.getIndentStr(indent) if not nestedIf else '', negated_condition_exp))
                    self.writeNode(node.falseChild, f, indent+1)
                else:
                    f.write('{0}if({1})\n'.format(self.getIndentStr(indent) if not nestedIf else '', str(condition_exp)))
                    self.writeNode(node.trueChild, f, indent+1)
                    f.write('{0}else '.format(self.getIndentStr(indent)))
                    self.writeNode(node.falseChild, f, indent, True)
        elif isinstance(node, BasicBlock):
            f.write(node.to_string(self.getIndentStr(indent)))
        elif isinstance(node, LoopNode):
            condition_exp = get_condition_from_logic_expression(node.condition, self.conditions_map)
            if node.type == LoopType.PRE_TESTED or node.type == LoopType.ENDLESS:
                f.write("{0}while({1})\n".format(self.getIndentStr(indent), condition_exp))
                self.writeNode(node.body, f, indent + 1)
            elif node.type == LoopType.POST_TESTED:
                f.write("{0}do\n".format(self.getIndentStr(indent)))
                self.writeNode(node.body, f, indent + 1)
                f.write("{0}while({1})\n".format(self.getIndentStr(indent), condition_exp))
        elif isinstance(node, SwitchNode):
            f.write("{0}switch({1})\n".format(self.getIndentStr(indent), node.testedVariableName))
            for c in node.cases:
                for v in c.caseValues:
                    f.write("{0}case {1}:\n".format(self.getIndentStr(indent + 1), v))
                self.writeNode(c.node, f, indent + 2)
                if c.endsWithBreak:
                    f.write("{0}break\n".format(self.getIndentStr(indent + 2)))
            if node.defaultNode is not None:
                f.write("{0}default :\n".format(self.getIndentStr(indent + 1)))
                self.writeNode(node.defaultNode, f, indent + 2)
        elif isinstance(node, Instruction):
            f.write("{0}{1};\n".format(self.getIndentStr(indent), str(node)))

    @staticmethod
    def getIndentStr(indent):
        return "    " * indent