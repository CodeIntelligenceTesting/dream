# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from graph_tool.all import Graph
from graph_tool.topology import is_DAG, topological_sort, shortest_distance, dominator_tree
import pydot
from sympy import And, Or, Not, false, true
from graph_tool.search import dfs_search
from sympy.core.symbol import Symbol
from sympy.logic.boolalg import to_cnf, simplify_logic
from dream.ControlFlowTree import CodeNode, ControlFlowTree, HelperNode, BasicBlock, SequenceNode, ConditionNode, CFTNode
from dream.DataFlowAnalysis import ReachingDefinitionsAnalysis, LivenessAnalysis, CongruenceAnalysis
from dream.ir.instructions import Assignment, Instruction, Break, Return
from dream.ir.expressions import HighLevelCondition, LocalVariable, NumericConstant, Expression
from dream.enums import NodeType
from graph_visitors import SliceVisitor, DepthFirstSearchVisitor
from dream.logic import conditions_equal, get_AND_remaining_term


class Interval:
    def __init__(self, header):
        self.header = header
        header.get_graph().vertex_properties['in_interval'][header] = True
        self.nodes = [header]

    def compute_interval_nodes(self):
        while True:
            new_nodes = self.frontier_nodes()
            if not new_nodes:
                return
            self.nodes.extend(new_nodes)

    def new_header_candidates(self):
        return self.frontier_nodes(inInterval=False)

    def frontier_nodes(self, inInterval=True):
        frontier = []
        for n in self.nodes:
            for s in n.out_neighbours():
                if not s.get_graph().vertex_properties['in_interval'][s] and s not in self.nodes and s not in frontier:
                    if self.all_immediate_predecessors_in_interval(s) if inInterval else not self.all_immediate_predecessors_in_interval(s):
                        s.get_graph().vertex_properties['in_interval'][s] = True
                        frontier.append(s)
        return frontier

    def all_immediate_predecessors_in_interval(self, node):
        for p in node.in_neighbours():
            if p not in self.nodes:
                return False
        return True

    def is_cyclic(self):
        for l in self.header.in_neighbours():
            if l in self.nodes:
                return True
        return False

    def get_reaching_nodes(self, cfg, target_nodes):
        loop_body_nodes = []
        for latchingNode in target_nodes:

            g_slice = cfg.compute_graph_slice(self.header, latchingNode)
            for n in [g_slice.slice_orig_map[v] for v in g_slice.cfg.vertices()]:
                if n not in target_nodes and n != self.header:
                    loop_body_nodes.append(n)
        return loop_body_nodes

    def get_latching_nodes(self):
        latching_nodes = []
        for p in self.header.in_neighbours():
            if p in self.nodes:
                latching_nodes.append(p)
        return latching_nodes


class GraphSlice:
    def __init__(self, cfg, header, tail, orig_slice_map, slice_orig_map):
        self.cfg = cfg
        self.header = header
        self.tail = tail
        self.orig_slice_map = orig_slice_map
        self.slice_orig_map = slice_orig_map
        self.vertex_code_map = {}
        self.reaching_conditions = None
        self.topological_order = None

    def add_node(self, n, cfg_orig, preds=None):
        # all predecessors should be already in the slice
        # cfg_orig = n.get_graph()
        n_new = self.cfg.add_vertex()
        self.cfg.vertex_properties['type'][n_new] = cfg_orig.vertex_properties['type'][n]
        self.cfg.vertex_properties['ast'][n_new] = cfg_orig.vertex_properties['ast'][n]
        self.orig_slice_map[n] = n_new
        self.slice_orig_map[n_new] = n
        if preds is None:
            for p in n.in_neighbours():
                e = self.cfg.add_edge(self.orig_slice_map[p], n_new)
                self.cfg.edge_properties['tag'][e] = cfg_orig.edge_properties['tag'][cfg_orig.edge(p, n)]
        else:
            for p in preds:
                e = self.cfg.add_edge(self.orig_slice_map[p], n_new)
                self.cfg.edge_properties['tag'][e] = cfg_orig.edge_properties['tag'][cfg_orig.edge(p, n)]

    def control_flow_tree(self, last_node_postdominates=False):
        assert is_DAG(self.cfg)
        self.cfg.compute_reachability_map()
        self.reaching_conditions = self.cfg.find_reaching_conditions(last_node_postdominates)
        self.compute_topological_order()
        self.vertex_code_map = {}
        tree_nodes = []
        latching_conditions = []
        self.cfg.vertex_properties['added_as_helper_node'] = self.cfg.new_vertex_property('bool')
        for n in self.topological_order:
            if self.cfg.vertex_properties['type'][n] == NodeType.CODE:
                code_node = CodeNode(self.reaching_conditions[n], self.cfg.vertex_properties['ast'][n], len(self.vertex_code_map))
                tree_nodes.append(code_node)
                self.vertex_code_map[n] = code_node
            elif self.cfg.vertex_properties['type'][n] == NodeType.CONDITIONAL:
                branches = [b for b in n.out_neighbours()]
                if self.has_only_conditional_children(n):
                    if not self.cfg.vertex_properties['added_as_helper_node'][branches[0]]:
                        self.cfg.vertex_properties['added_as_helper_node'][branches[0]] = True
                        helper_node = HelperNode(self.reaching_conditions[branches[0]], len(self.vertex_code_map))
                        tree_nodes.append(helper_node)
                        self.vertex_code_map[n] = helper_node
                elif len(branches) == 2:
                    index = None
                    if self.cfg.vertex_properties['type'][branches[0]] == NodeType.CONDITIONAL\
                            and self.cfg.reachability_map[int(branches[0])][int(branches[1])]:
                        index = 0
                    elif self.cfg.vertex_properties['type'][branches[1]] == NodeType.CONDITIONAL\
                            and self.cfg.reachability_map[int(branches[1])][int(branches[0])]:
                        index = 1
                    if index is not None:
                        if not self.cfg.vertex_properties['added_as_helper_node'][branches[index]]:
                            self.cfg.vertex_properties['added_as_helper_node'][branches[index]] = True
                            helper_node = HelperNode(self.reaching_conditions[branches[index]], len(self.vertex_code_map))
                            tree_nodes.append(helper_node)
                            self.vertex_code_map[n] = helper_node

            elif self.cfg.vertex_properties['type'][n] == NodeType.SWITCH:
                if not self.cfg.vertex_properties['added_as_helper_node'][n]:
                    self.cfg.vertex_properties['added_as_helper_node'][n] = True
                    helper_node = HelperNode(self.reaching_conditions[n], len(self.vertex_code_map))
                    tree_nodes.append(helper_node)
                    self.vertex_code_map[n] = helper_node
        reachability_map = [[x == y for x in range(0, len(self.vertex_code_map))] for y in range(0, len(self.vertex_code_map))]
        for u in self.vertex_code_map:
            for v in self.vertex_code_map:
                reachability_map[self.vertex_code_map[u].index][self.vertex_code_map[v].index] = self.cfg.reachability_map[self.cfg.vertex_index[u]][self.cfg.vertex_index[v]]

        del self.cfg.vertex_properties['added_as_helper_node']
        return ControlFlowTree(tree_nodes, reachability_map, self.cfg.conditions_map, latching_conditions)

    def has_only_conditional_children(self, conditional_node):
        branches = [b for b in conditional_node.out_neighbours()]
        return (len(branches) == 1 and self.cfg.vertex_properties['type'][branches[0]] == NodeType.CONDITIONAL) or \
               (len(branches) == 2 and self.cfg.vertex_properties['type'][branches[0]] == NodeType.CONDITIONAL
                and self.cfg.vertex_properties['type'][branches[1]] == NodeType.CONDITIONAL)

    def has_pure_conditional_paths(self):
        tail_nodes = self.tail if type(self.tail) == list else [self.tail]
        for v in self.cfg.vertices():
            if self.cfg.vertex_properties['type'][v] != NodeType.CONDITIONAL and v not in tail_nodes:
                return False
        return True

    def add_break_node(self, n_exit, break_nodes, tag_break):
        n_break = None
        for break_node in break_nodes:
            ncd = self.cfg.nearest_common_dominator([n_exit, break_node])
            if self.cfg.compute_graph_slice(ncd, [n_exit, break_node]).has_pure_conditional_paths():
                n_break = break_node
                break
        if n_break is None:
            #break_block = BasicBlock()
            #break_block.ends_with_break = True
            n_break = self.cfg.add_vertex()
            self.cfg.vertex_properties['type'][n_break] = NodeType.CODE
            self.cfg.vertex_properties['ast'][n_break] = SequenceNode(true, [Break()])#break_block
            self.cfg.vertex_properties['exit_node'][n_break] = 1
            break_nodes.append(n_break)
        e_break = self.cfg.add_edge(n_exit, n_break)
        self.cfg.edge_properties['tag'][e_break] = tag_break
        self.cfg.compute_dominator_tree(self.cfg.vertex(0))

    # def update_break_edges(self):
    #
    #     self.cfg.compute_reachability_map()
    #     for n in self.cfg.vertices():
    #         if self.cfg.vertex_properties['type'][n] == NodeType.CONDITIONAL and n.out_degree() == 2:
    #             branches = [s for s in n.out_neighbours()]
    #             if self.can_add_break_edges(branches, 0, 1):
    #                 print '    {0} -> {1}'.format(int(branches[0]), int(branches[1]))
    #                 self.cfg.add_edge(branches[0], branches[1])
    #             elif self.can_add_break_edges(branches, 1, 0):
    #                 print '    {0} -> {1}'.format(int(branches[1]), int(branches[0]))
    #                 self.cfg.add_edge(branches[1], branches[0])

    def can_add_break_edges(self, if_branches, from_id, to_id):
        if self.cfg.vertex_properties['type'][if_branches[from_id]] == NodeType.CODE:
            branch_i_ast = self.cfg.vertex_properties['ast'][if_branches[from_id]]
            if isinstance(branch_i_ast, Instruction) or isinstance(branch_i_ast, Expression):
                break_node = isinstance(branch_i_ast, Break)
            else:
                break_node = branch_i_ast.is_break_node()
            if break_node:
                return if_branches[to_id] not in if_branches[from_id].out_neighbours()\
                    and not self.cfg.reachability_map[int(if_branches[to_id])][int(if_branches[from_id])]
        return False

    # def update_return_nodes_edges(self):
    #     #TODO check reachability
    #     self.cfg.draw_graph('break0.png')
    #     self.cfg.compute_reachability_map()
    #     for n in self.cfg.vertices():
    #         #if self.cfg.vertex_properties['type'][n] == NodeType.CONDITIONAL and n.out_degree() == 2:
    #         if n.out_degree() == 2:
    #             branches = [s for s in n.out_neighbours()]
    #             if self.cfg.vertex_properties['type'][branches[0]] == NodeType.CODE\
    #                     and branches[0] in self.slice_orig_map and self.slice_orig_map[branches[0]].out_degree() == 0\
    #                     and not self.cfg.reachability_map[int(branches[1])][int(branches[0])]:
    #                 self.cfg.add_edge(branches[0], branches[1])
    #             elif self.cfg.vertex_properties['type'][branches[1]] == NodeType.CODE\
    #                     and branches[1] in self.slice_orig_map and self.slice_orig_map[branches[1]].out_degree() == 0\
    #                     and not self.cfg.reachability_map[int(branches[0])][int(branches[1])]:
    #                 self.cfg.add_edge(branches[1], branches[0])

    #    self.cfg.draw_graph('break1.png')

    def get_first_node_with_condition(self, condition):
        for n in self.topological_order:
            if conditions_equal(self.reaching_conditions[n], condition):
                return self.slice_orig_map[n]

    def remove_intermediate_code_nodes(self):
        done = False
        while not done:
            done = True
            for v in self.cfg.vertices():
                if self.cfg.vertex_properties['type'][v] == NodeType.CODE:
                    assert v.in_degree() > 0
                    if v.out_degree() > 0:
                        assert v.out_degree() == 1
                        predecessors = [p for p in v.in_neighbours()]
                        successor = [s for s in v.out_neighbours()][0]
                        for p in predecessors:
                            e = self.cfg.edge(p, v)
                            e_tag = self.cfg.edge_properties['tag'][e]
                            #self.cfg.remove_edge(e)
                            self.cfg.edge_properties['tag'][self.cfg.add_edge(p, successor)] = e_tag
                        #self.cfg.remove_edge(self.cfg.edge(v, successor))
                        self.cfg.clear_vertex(v)
                        self.cfg.remove_vertex(v)
                        done = False
                        break

    def compute_topological_order(self):
        self.topological_order = [self.cfg.vertex(i) for i in topological_sort(self.cfg)]
        #self.topological_order.reverse()


class RefinedLoopEntry:
    def __init__(self, target_node, condition_from_header):
        self.target_node = target_node
        self.condition_from_header = condition_from_header


class ControlFlowGraph(Graph):
    def __init__(self, *args, **kwargs):
        super(ControlFlowGraph, self).__init__(*args, **kwargs)
        self.vertex_conditions = {}
        self.vertex_properties['ast'] = self.new_vertex_property('object')
        self.vertex_properties['type'] = self.new_vertex_property('int')
        self.vertex_properties['is_header'] = self.new_vertex_property('int')
        self.vertex_properties['exit_node'] = self.new_vertex_property('int')
        self.edge_properties['tag'] = self.new_edge_property('object')
        self.reachability_map = None
        self.dominator_tree = None
        self.conditions_map = {}
        self.dfs_visitor = None
        self.variable_names = {}

    def add_code_node(self, stmts):
        v = self.add_vertex()
        self.vertex_properties['type'][v] = NodeType.CODE
        self.vertex_properties['ast'][v] = SequenceNode(true, stmts)
        return v

    def find_reaching_conditions(self, last_node_postdominates=False):
        vertex_conditions = {}
        if is_DAG(self):
            # topological_order = [self.vertex(i) for i in reversed(topological_sort(self))]
            topological_order = [self.vertex(i) for i in topological_sort(self)]
            for node in topological_order:
                if node.in_degree() == 0:
                    vertex_conditions[node] = true
                else:
                    is_break_node = self.vertex_properties['ast'][node].is_pure_break() \
                        if self.vertex_properties['type'][node] == NodeType.CODE else False
                    if topological_order.index(node) == len(topological_order) - 1 and last_node_postdominates \
                            and not is_break_node:
                        vertex_conditions[node] = true
                    else:
                        cond = false
                        for pred in node.in_neighbours():
                            in_e = self.edge(pred, node)
                            edge_tag = self.edge_properties['tag'][in_e] if self.edge_properties['tag'][in_e] is not None else true
                            cond = Or(cond, And(vertex_conditions[pred],  edge_tag))
                        #vertex_conditions[node] = simplify_logic(cond)
                        vertex_conditions[node] = to_cnf(cond, simplify=True)
                        #print vertex_conditions[node]
                #print int(node), vertex_conditions[node]
            #print "done reaching conditions"
            return vertex_conditions

    def compute_reachability_map(self):
        self.reachability_map = [[x == y for x in range(0, self.num_vertices())] for y in range(0, self.num_vertices())]
        distance_map = shortest_distance(self)
        for v in self.vertices():
            for u_index in range(0, self.num_vertices()):
                self.reachability_map[self.vertex_index[v]][u_index] = distance_map[v][u_index] < 2147483647

    def does_reach(self, src, dst):
        return shortest_distance(self, src, dst) < 2147483647
        #return self.reachability_map[self.vertex_index[src]][self.vertex_index[dst]]

    def compute_intervals(self):
        self.vertex_properties['in_interval'] = self.new_vertex_property('bool')
        intervals = []
        headers = [self.vertex(0)]
        while len(headers) > 0:
            I = Interval(headers[0])
            I.compute_interval_nodes()
            headers = headers[1:] + [h for h in I.new_header_candidates() if h not in headers + [interval.header for interval in intervals]]
            intervals.append(I)
        del self.vertex_properties['in_interval']
        return intervals

    def compute_graph_slice(self, src, dst):
        # self.draw_graph('slice0.png')
        virtual_node = self.add_vertex()
        if type(dst) == list:
            for v in dst:
                self.add_edge(v, virtual_node)
        else:
            self.add_edge(dst, virtual_node)
        # self.draw_graph('slice1.png')

        cfg_slice = ControlFlowGraph()
        cfg_slice.conditions_map = self.conditions_map
        cfg_slice.vertex_properties['orig'] = cfg_slice.new_vertex_property('object')
        sliceVisitor = SliceVisitor(src, virtual_node, cfg_slice)
        dfs_search(self, src, sliceVisitor)

        virtual_slice_node = sliceVisitor.graphToSliceNodeMap[virtual_node]
        del sliceVisitor.graphToSliceNodeMap[virtual_node]
        #self.remove_node_edges(virtual_node)
        #cfg_slice.remove_node_edges(virtual_slice_node)

        self.clear_vertex(virtual_node)
        cfg_slice.clear_vertex(virtual_slice_node)

        self.remove_vertex(virtual_node)
        cfg_slice.remove_vertex(virtual_slice_node)

        orig_slice_map = {}
        slice_orig_map = {}
        for v_slice in cfg_slice.vertices():
            v_orig = cfg_slice.vertex_properties['orig'][v_slice]
            orig_slice_map[v_orig] = v_slice
            slice_orig_map[v_slice] = v_orig
            cfg_slice.vertex_properties['type'][v_slice] = self.vertex_properties['type'][v_orig]
            cfg_slice.vertex_properties['ast'][v_slice] = self.vertex_properties['ast'][v_orig]

        for e in cfg_slice.edges():
            e_orig = self.edge(slice_orig_map[e.source()], slice_orig_map[e.target()])
            if self.edge_properties['tag'][e_orig] is not None:
                #e_tag = self.edge_properties['tag'][e_orig]
                cfg_slice.edge_properties['tag'][e] = self.edge_properties['tag'][e_orig]

        slice_header = orig_slice_map[src] if src in orig_slice_map else None

        if type(dst) == list:
            slice_tail = [orig_slice_map[v] if v in orig_slice_map else None for v in dst]
        else:
            slice_tail = orig_slice_map[dst] if dst in orig_slice_map else None

        return GraphSlice(cfg_slice, slice_header, slice_tail, orig_slice_map, slice_orig_map)

    def collapse_region(self, head, tail, region_nodes, syntax_tree):
        # print 'region_nodes: ', [int(n) for n in region_nodes]
        # self.draw_graph('cfg_re.dot')
        syntax_tree = syntax_tree if syntax_tree else SequenceNode(True, [])
        collapsed_node_is_header = self.get_cfg_header() in region_nodes
        preds = [p for p in head.in_neighbours() if p not in region_nodes]
        succs = []
  
        if type(tail) == list:
            for t in region_nodes:
                succs = succs + [s for s in t.out_neighbours() if s not in region_nodes and s not in succs]
        else:
            succs = [s for s in tail.out_neighbours() if s not in region_nodes]

        exit_nodes = set()
        for s in succs:
            exit_nodes.update([n_exit for n_exit in region_nodes if n_exit in s.in_neighbours()])
        exit_nodes = list(exit_nodes)

        assert len(succs) <= 1 or len(exit_nodes) <= 1
        if len(preds) > 0 or len(succs) > 0:
            collapsed_node = self.add_vertex()
            if collapsed_node_is_header:
                self.vertex_properties['is_header'][collapsed_node] = 1
            self.vertex_properties['type'][collapsed_node] = NodeType.CODE
            self.vertex_properties['ast'][collapsed_node] = syntax_tree
            for pred in preds:
                e = self.add_edge(pred, collapsed_node)
                self.edge_properties['tag'][e] = self.edge_properties['tag'][self.edge(pred, head)]

            if len(succs) <= 1:
                if len(succs) == 1:
                    e = self.add_edge(collapsed_node, succs[0])
                    self.edge_properties['tag'][e] = None
            else:
                for succ in succs:
                    e = self.add_edge(collapsed_node, succ)
                    # print '\ttag:', self.edge_properties['tag'][self.edge(exit_nodes[0], succ)]
                    # exit(0)
                    self.edge_properties['tag'][e] = self.edge_properties['tag'][self.edge(exit_nodes[0], succ)]
            # for succ in succs:
            #     e = self.add_edge(collapsed_node, succ)
            #     self.edge_properties['tag'][e] = None

            for n in region_nodes:
                self.clear_vertex(self.vertex(int(n)))

            self.remove_isolated_nodes()

        else:
            self.clear()
            collapsed_node = self.add_vertex()
            self.vertex_properties['type'][collapsed_node] = NodeType.CODE
            self.vertex_properties['ast'][collapsed_node] = syntax_tree
            if collapsed_node_is_header:
                self.vertex_properties['is_header'][collapsed_node] = 1
 
    @staticmethod
    def get_frontier_nodes(region_nodes, succFrontier=True):
        frontierNodes = []
        for n in region_nodes:
            for p in n.out_neighbours() if succFrontier else n.in_neighbours():
                if p not in region_nodes and p not in frontierNodes:
                    frontierNodes.append(p)
        return frontierNodes

    def compute_dominator_tree(self, root):
        dom = dominator_tree(self, root)
        self.dominator_tree = ControlFlowGraph()
        self.dominator_tree.add_vertex(self.num_vertices())
        for i in range(0, self.num_vertices()):
            if i != int(root):
                self.dominator_tree.add_edge(self.dominator_tree.vertex(dom.a[i]), self.dominator_tree.vertex(i))
        self.dominator_tree.compute_reachability_map()

    def nearest_common_dominator(self, nodes):
        node_indexes = [self.vertex_index[n] for n in nodes]
        ncd = 0
        next_ncd = 0
        while next_ncd is not None:
            ncd = next_ncd
            if ncd in node_indexes:
                break
            next_ncd = self.get_dominating_child(ncd, node_indexes)
        return self.vertex(ncd)

    def get_dominating_child(self, parent_node, dominated_nodes):
        #nodes here are represented by their indexes
        for succ in self.dominator_tree.vertex(parent_node).out_neighbours():
            succ_index = self.dominator_tree.vertex_index[succ]
            if self.does_dominate(succ_index, dominated_nodes):
                return succ_index
        return None

    def does_dominate(self, d, dominated_nodes):
        for n in dominated_nodes:
            if not self.dominator_tree.reachability_map[d][n]:
                return False
        return True

    """-------------------Structuring---------------------"""

    def structure(self, split_returns=True):
        # self.draw_graph('/home/user/tmp/cfg.dot')
        if self.num_vertices() == 1:
            return
        i = 1
        header_found = False
        for v in self.vertices():
            if v.in_degree() == 0:
                self.vertex_properties['is_header'][v] = 1
                header_found = True
                break
        if not header_found:
            self.vertex_properties['is_header'][self.vertex(0)] = 1
        # self.draw_graph('cfg.dot')
        if split_returns:
            self.split_pure_return_nodes()
        self.add_return_edges(self.get_cfg_header())
        # self.draw_graph('cfg_ret.dot')
        while self.num_vertices() > 1:
            # print 'step: ', i
            assert i < 200, 'Max number of iterations'
            # self.compute_reachability_map()
            # self.draw_graph('g{0}.dot'.format(i))
            header = self.get_cfg_header()
            self.compute_dominator_tree(header)
            # self.dominator_tree.draw_graph('dom{0}.dot'.format(i))
            self.dfs_visitor = DepthFirstSearchVisitor()
            dfs_search(self, header, self.dfs_visitor)
            # print [int(xx) for xx in reversed(self.dfs_visitor.postorder)]
            loop_headers = [e.target() for e in self.dfs_visitor.back_edges]

            visited_nodes = []
            for n in self.dfs_visitor.postorder:
                # print 'head: ', n
                if n in loop_headers:
                    latching_nodes = [e.source() for e in self.dfs_visitor.back_edges if e.target() == n]
                    self.structure_cyclic(n, latching_nodes)
                    break
                else:
                    dominated_nodes = self.get_dominated_nodes(n)
                    if len(dominated_nodes) > 1:
                        # if self.has_at_most_one_exit_node(dominated_nodes, consider_return_nodes=loop_headers)\
                        if self.has_at_most_one_exit_node(dominated_nodes, consider_return_nodes=len(loop_headers) > 0)\
                                or self.has_at_most_one_postdominating_successor(n, dominated_nodes):
                            tail_nodes = self.get_exit_nodes(dominated_nodes, consider_return_nodes=True)
                            # print 'structure_acyclic_{0}({1}, {2})'.format(i, int(n), [int(t) for t in tail_nodes])
                            self.structure_acyclic(n, tail_nodes)
                            break

                        tail_nodes = self.get_sub_region_tail(n, dominated_nodes, visited_nodes)
                        if tail_nodes is not None:
                            # print 'structure_acyclic_sub_{0}({1}, {2})'.format(i, int(n), [int(t) for t in tail_nodes])
                            self.structure_acyclic(n, tail_nodes)
                            break

                visited_nodes.append(n)
            i += 1

        assert self.num_vertices() == 1, 'structured finished with multiple node'

    def get_sub_region_tail(self, head, dominated_nodes, visited_node_in_postorder):
        sub_region_nodes = {head}
        for n in reversed(visited_node_in_postorder):
            if n not in dominated_nodes:
                return None
            sub_region_nodes.add(n)
            if self.is_post_dominating(n, sub_region_nodes):
                tail_nodes = [n] if n.out_degree() <= 1 else [p for p in n.in_neighbours()]
                if self.code_nodes_num(sub_region_nodes.union(set(tail_nodes))) > 1:
                    return tail_nodes

        return None

    def code_nodes_num(self, nodes):
        return len([n for n in nodes if self.vertex_properties['type'][n] == NodeType.CODE])

    @staticmethod
    def is_post_dominating(node, region_nodes):
        return_nodes = set([n for n in region_nodes if n.out_degree() == 0])
        #assert len(return_nodes) == 0, 'subregion contains return nodes'
        if len(return_nodes) == 0:
            exit_nodes = set()
            for v in region_nodes:
                for s in v.out_neighbours():
                    if s not in region_nodes:
                        exit_nodes.add(v)
                        break
            return len(exit_nodes) == 1 and node in exit_nodes

    def has_at_most_one_exit_node(self, region_nodes, consider_return_nodes=True):
        return len(self.get_exit_nodes(region_nodes, consider_return_nodes)) <= 1

    def has_at_most_one_postdominating_successor(self, header, region_nodes):
        successors = set()
        for v in region_nodes:
            successors.update([s for s in v.out_neighbours() if s not in region_nodes])
        if len(successors) == 1:
            successor_node = iter(successors).next()
            g_slice = self.compute_graph_slice(header, successor_node)
            diff = set(g_slice.slice_orig_map.values()).symmetric_difference(set(region_nodes))
            return len(diff) == 1 and iter(diff).next() == successor_node
            return not set(g_slice.slice_orig_map.values()).symmetric_difference(set(region_nodes))
        else:
            return len(successors) == 0

    def get_cfg_header(self):
        for v in self.vertices():
            if self.vertex_properties['is_header'][v] == 1:
                return v
        return None

    def get_dominated_nodes(self, dom_node):
        dominated_region = set()
        self.dominator_tree.get_children(self.dominator_tree.vertex(int(dom_node)), dominated_region)
        return set([self.vertex(i) for i in dominated_region])

    @staticmethod
    def get_entry_nodes(region_header, region_nodes):
        entry_nodes = set()
        entry_nodes.add(region_header)
        entry_nodes.update([n for n in region_nodes if [p for p in n.in_neighbours() if p not in region_nodes]])
        return list(entry_nodes)

    @staticmethod
    def get_exit_nodes(region_nodes, consider_return_nodes=True):
        return list(set([n for n in region_nodes if [s for s in n.out_neighbours() if s not in region_nodes]
                        or (n.out_degree() == 0 if consider_return_nodes else False)]))

    def get_children(self, parent_node, children):
        assert is_DAG(self)
        children.add(int(parent_node))
        for s in parent_node.out_neighbours():
            self.get_children(s, children)

    def split_pure_return_nodes(self, max_in_edges=2):
        ret_nodes = [n for n in self.vertices() if n.out_degree() == 0 and n.in_degree() > max_in_edges]
        for ret_node in ret_nodes:
            stmts = self.vertex_properties['ast'][ret_node].children
            if len(stmts) == 1 and isinstance(stmts[0], Return):
                ret_stmt = stmts[0]
                #print 'ret_stmt: ', ret_stmt
                preds = [p for p in ret_node.in_neighbours()]
                for p in preds[1:]:
                    tag = self.edge_properties['tag'][self.edge(p, ret_node)]
                    new_ret_node = self.add_vertex()
                    self.vertex_properties['type'][new_ret_node] = NodeType.CODE
                    self.vertex_properties['ast'][new_ret_node] = SequenceNode(true, [ret_stmt.deep_copy()])
                    self.edge_properties['tag'][self.add_edge(p, new_ret_node)] = tag
                    self.remove_edge(self.edge(p, ret_node))
                    #print 'tag({0}, {1}) = {2}'.format(int(p), int(ret_node), tag)
                    #n_break =
                    #self.cfg.vertex_properties['type'][n_break] = NodeType.CODE
                    #self.cfg.vertex_properties['ast'][n_break] = SequenceNode(true, [Break()])
        #self.draw_graph('plitted.png')

    def is_return_vertex(self, v):
        if v.out_degree() == 0 and self.vertex_properties['type'][v] == NodeType.CODE:
            return self.vertex_properties['ast'][v].is_return_node()
        return False

    def is_break_vertex(self, v):
        if v.out_degree() == 0 and self.vertex_properties['type'][v] == NodeType.CODE:
            return self.vertex_properties['ast'][v].is_break_node()
        return False

    def add_return_edges(self, header, final_return_nodes=[]):
        #self.add_edge(self.vertex(24), self.vertex(22))
        #return
        #graph slice should only be computed if the graph is cyclic
        ret_nodes = [v for v in self.vertices() if self.is_return_vertex(v) and v not in final_return_nodes]
        #print 'ret_nodes: ', [int(x) for x in ret_nodes]
        if len(ret_nodes + final_return_nodes) > 1:
            dfs_visitor = DepthFirstSearchVisitor()
            dfs_search(self, header, dfs_visitor)
            loops_latching_nodes = [e.source() for e in dfs_visitor.back_edges if e.source().out_degree() == 1]

            g_slice = self.compute_graph_slice(header, ret_nodes + final_return_nodes + loops_latching_nodes)
            #g_slice.cfg.draw_graph('ret_slice.png')
            #g_slice.cfg.compute_reachability_map()
            for ret_n in ret_nodes:
                #print '  n_ret: ', int(ret_n)
                target_candidates = self.get_return_edge_target_candidates(ret_n, ret_n, g_slice)
                #print '    target_candidates: ', [int(x) for x in target_candidates]
                if len(target_candidates) == 1:
                    ret_target = next(iter(target_candidates))
                    if ret_target not in ret_nodes:
                        g_slice.cfg.compute_dominator_tree(g_slice.cfg.vertex(0))
                        tail = [g_slice.orig_slice_map[ret_n], g_slice.orig_slice_map[ret_target]]
                        ncd = g_slice.cfg.nearest_common_dominator(tail)
                        inner_nodes = {g_slice.slice_orig_map[v]:
                                       set([g_slice.slice_orig_map[p] for p in v.in_neighbours()])
                                       for v in g_slice.cfg.vertices()
                                       if g_slice.cfg.does_reach(ncd, v)
                                       and any(g_slice.cfg.does_reach(v, n_tail) for n_tail in tail)
                                       and v not in tail + [ncd]}
                        if self.is_self_contained(inner_nodes):
                            self.edge_properties['tag'][self.add_edge(ret_n, ret_target)] = None
                            g_slice.cfg.add_edge(g_slice.orig_slice_map[ret_n], g_slice.orig_slice_map[ret_target])
                            #g_slice.cfg.compute_reachability_map()
                            #print 'Added return edge {0} -> {1}'.format(ret_n, next(iter(target_candidates)))

    def add_break_edges(self, final_break_nodes=[]):
        assert is_DAG(self)
        #graph slice should only be computed if the graph is cyclic
        break_nodes = [v for v in self.vertices() if self.is_break_vertex(v) and v not in final_break_nodes]
        if len(break_nodes + final_break_nodes) > 1:
            for break_n in break_nodes:
                target_candidates = self.get_break_target_candidates(break_n, break_n)
                if len(target_candidates) == 1:
                    break_target = next(iter(target_candidates))
                    if break_target not in break_nodes:
                        self.add_edge(break_n, break_target)

    def get_break_target_candidates(self, orig_ret_node, transit_ret_node):
        target_candidates = set()
        for p in transit_ret_node.in_neighbours():
            if p.out_degree() == 1:
                target_candidates.update(self.get_break_target_candidates(orig_ret_node, p))
            elif self.vertex_properties['type'][p] == NodeType.CONDITIONAL:
                n_f = [n for n in p.out_neighbours() if n != transit_ret_node][0]
                if not self.does_reach(n_f, orig_ret_node):
                    target_candidates.add(n_f)
        return target_candidates

    def get_return_edge_target_candidates(self, orig_ret_node, transit_ret_node, g_slice):
        target_candidates = set()
        for n_pred in transit_ret_node.in_neighbours():
            if n_pred.out_degree() == 1:
                target_candidates.update(self.get_return_edge_target_candidates(orig_ret_node, n_pred, g_slice))
            elif self.vertex_properties['type'][n_pred] == NodeType.CONDITIONAL:
                n_f = [n for n in n_pred.out_neighbours() if n != transit_ret_node][0]
                if n_f in g_slice.orig_slice_map and orig_ret_node in g_slice.orig_slice_map:
                    if not g_slice.cfg.does_reach(g_slice.orig_slice_map[n_f], g_slice.orig_slice_map[orig_ret_node]):
                        target_candidates.add(n_f)
        return target_candidates

    @staticmethod
    def is_self_contained(region_nodes):
        for n, preds in region_nodes.items():
            preds_orig = set([p for p in n.in_neighbours()])
            if preds ^ preds_orig:
                return False
        return True

    """ ------------------ Dominator Tree structuring------------------------ """
    def structure_using_dom_tree(self, header, tail):
        g_slice = self.compute_graph_slice(header, tail)
        slice_header = g_slice.orig_slice_map[header]
        g_slice.cfg.compute_dominator_tree(slice_header)
        g_slice.cfg.reaching_conditions = {}
        structuring_var = LocalVariable(self.make_new_variable_name(), 'int')
        g_slice.cfg.compute_hierarchical_conditions(slice_header, structuring_var)
        g_slice.cfg.topological_order = list(topological_sort(g_slice.cfg))
        g_slice.cfg.compute_reachability_map()
        syntax_tree = g_slice.cfg.structure_region(slice_header)
        self.collapse_region(header, tail, g_slice.orig_slice_map.keys(), syntax_tree)

    def structure_region(self, header):
        D = sorted(self.directly_dominated_nodes(header), key=lambda n: self.topological_order.index(int(n)))
        if not D:
            if self.vertex_properties['type'][header] == NodeType.CODE:
                region_ast = self.vertex_properties['ast'][header]
                if isinstance(region_ast, SequenceNode) and not region_ast.children:
                    return None
                return region_ast
            else:
                return None
        tree_nodes = []
        code_vertex_map = {}

        if self.vertex_properties['type'][header] == NodeType.CODE:
            h_ast = self.vertex_properties['ast'][header]
            if not isinstance(h_ast, SequenceNode) or len(h_ast.children) > 0:
                tree_nodes.append(CodeNode(True, h_ast, 0))
                code_vertex_map[0] = int(header)

        for d in D:
            d_ast = self.structure_region(d)
            d_cond = self.reaching_conditions[header][d]
            idx = len(tree_nodes)
            if d_ast is not None:
                if isinstance(d_ast, ConditionNode):
                    if d_ast.falseChild is None:
                        code_node = CodeNode(d_cond & d_ast.condition, d_ast.trueChild, idx)
                    elif d_ast.trueChild is None:
                        code_node = CodeNode(d_cond & ~d_ast.condition, d_ast.falseChild, idx)
                    else:
                        code_node = CodeNode(d_cond, d_ast, idx)
                    tree_nodes.append(code_node)
                    code_vertex_map[idx] = int(d)
                else:
                    if not isinstance(d_ast, SequenceNode) or len(d_ast.children) > 0:
                        code_node = CodeNode(d_cond, d_ast, idx)
                        tree_nodes.append(code_node)
                        code_vertex_map[idx] = int(d)
                    else:
                        assert False, "problem here"

        if not tree_nodes:
            return None

        reachability_map = [[x == y for x in range(len(tree_nodes))] for y in range(len(tree_nodes))]

        for i in range(len(tree_nodes)):
            for j in range(i+1, len(tree_nodes)):
                reachability_map[i][j] = self.reachability_map[code_vertex_map[i]][code_vertex_map[j]]

        control_flow_tree = ControlFlowTree(tree_nodes, reachability_map, self.conditions_map)
        control_flow_tree.refine()
        control_flow_tree.replace_code_nodes_by_ast()
        control_flow_tree.combine_sequence_nodes_with_sequence_children(control_flow_tree.root)
        control_flow_tree.finalize()
        final_ast = control_flow_tree.root
        if isinstance(final_ast, SequenceNode) and not final_ast.children:
            print "returning empty sequence"
        return control_flow_tree.root

    def print_conditions(self, n):
        D = self.directly_dominated_nodes(n)
        for d in D:
            self.print_conditions(d)
        for d in D:
            print('cond[{0},{1}] = {2}'.format(n, d, self.reaching_conditions[n][d]))

    def compute_hierarchical_conditions(self, dom_node, var):
        D = self.directly_dominated_nodes(dom_node)
        self.reaching_conditions[dom_node] = {}
        for d in D:
            self.compute_hierarchical_conditions(d, var)
        for d in D:
            self.reaching_conditions[dom_node][d] = self.get_reaching_condition(dom_node, d, var)

    def get_reaching_condition(self, n_source, n_sink, var):
        gs = self.compute_graph_slice(n_source, n_sink)
        if gs.cfg.num_vertices() > 8:
            new_symbol = self.get_new_logic_symbol()
            self.conditions_map[new_symbol] = HighLevelCondition(var.deep_copy(), '==', NumericConstant(int(n_sink)))
            assign_stmt = Assignment(var.deep_copy(), NumericConstant(int(n_sink)))
            self.insert_assignment_on_incoming_edges(n_sink, assign_stmt)
            return new_symbol
        else:
            return gs.cfg.find_reaching_conditions()[gs.orig_slice_map[n_sink]]

    def insert_assignment_on_incoming_edges(self, n, assign_stmt):
        predecessors = list(n.in_neighbours())
        for p in predecessors:
            # print int(p), ' -> ', hex(assign_stmt.rhs_operand.value)
            if self.vertex_properties['type'][p] == NodeType.CODE:
                self.append_stmt_to_code_node(p, assign_stmt.deep_copy())
            else:
                p_cfg = self.add_vertex()
                self.vertex_properties['type'][p_cfg] = NodeType.CODE
                self.vertex_properties['ast'][p_cfg] = SequenceNode(True, [assign_stmt.deep_copy()])

                p_dom = self.dominator_tree.add_vertex()
                self.dominator_tree.add_edge(self.dominator_tree.vertex(int(p)), p_dom)

                assert int(p_cfg) == int(p_dom)

                e_p_n = self.edge(p, n)
                tag = self.edge_properties['tag'][e_p_n]
                if p not in self.reaching_conditions:
                    self.reaching_conditions[p] = {}
                self.reaching_conditions[p][p_cfg] = tag
                self.edge_properties['tag'][self.add_edge(p, p_cfg)] = tag
                self.edge_properties['tag'][self.add_edge(p_cfg, n)] = None
                self.remove_edge(e_p_n)

    def append_stmt_to_code_node(self, n, stmt):
        n_ast = self.vertex_properties['ast'][n]
        if isinstance(n_ast, SequenceNode):
            self.vertex_properties['ast'][n].children.append(stmt)
        else:
            try:
                cond = n_ast.reaching_condition
            except AttributeError:
                cond = True
            n_ast.reaching_condition = True
            self.vertex_properties['ast'][n] = SequenceNode(cond, [n_ast, stmt])

    def directly_dominated_nodes(self, n):
        dom_idx = [int(d) for d in self.dominator_tree.vertex(int(n)).out_neighbours()]
        return [self.vertex(i) for i in dom_idx]

    def get_new_logic_symbol(self):
        i = 0
        sym = Symbol('X')
        while sym in self.conditions_map:
            i += 1
            sym = Symbol('X{0}'.format(i))
        return sym
    """ ----------------------------------------------------------------- """

    def structure_acyclic(self, head, tail, is_loop_body=False):
        self.structure_using_dom_tree(head, tail)
        return
        # print 'structure_acyclic({0}, {1})'.format(int(head), [int(v) for v in tail])
        g_slice = self.compute_graph_slice(head, tail)
        # print(g_slice.cfg.num_vertices(), ' nodes')
        # g_slice.update_return_nodes_edges()
        last_node_postdominates = (type(tail) != list or len(tail) == 1) and not is_loop_body
        show = False
        control_flow_tree = g_slice.control_flow_tree(last_node_postdominates)
        control_flow_tree.refine()
        control_flow_tree.replace_code_nodes_by_ast()
        control_flow_tree.combine_sequence_nodes_with_sequence_children(control_flow_tree.root)
        control_flow_tree.finalize()
        syntax_tree = control_flow_tree.root
        self.collapse_region(head, tail, g_slice.orig_slice_map.keys(), syntax_tree)

    def structure_cyclic(self, header_node, latching_nodes):
        # print 'structure_cyclic: ', header_node, [int(x) for x in latching_nodes]
        # self.draw_graph('cfg_cyclic.dot')
        loop_slice = self.compute_graph_slice(header_node, latching_nodes)

        # TODO check if this step leads to improvement: if not undo
        self.refine_loop_exits(loop_slice)

        loop_nodes = loop_slice.slice_orig_map.values()

        abnormal_entry_edges = self.get_loop_abnormal_entry_edges(header_node, loop_nodes)
        if abnormal_entry_edges:
            self.restructure_abnormal_loop_entries(header_node, loop_nodes, abnormal_entry_edges, loop_slice)

        loop_exit_edges = self.loop_exits(loop_nodes)
        loop_exits = set([e.target() for e in loop_exit_edges])
        # print 'loop_exits: ', [int(x) for x in loop_exits]
        break_nodes = []
        if len(loop_exits) > 1:
            n_successor = self.restructure_abnormal_loop_exits_using_structuring_variable(loop_nodes, loop_exit_edges)
            break_nodes = self.add_break_statements(loop_slice, n_successor)
        elif len(loop_exits) == 1:
            n_successor = iter(loop_exits).next()
            break_nodes = self.add_break_statements(loop_slice, n_successor)
        else:
            n_successor = None

        slice_latching_nodes = [loop_slice.orig_slice_map[v] for v in latching_nodes] \
            if type(latching_nodes) == list else [latching_nodes]
        final_break_nodes = [v for v in break_nodes if any(v in set(p.out_neighbours()) for p in slice_latching_nodes)]
        num_edges_1 = loop_slice.cfg.num_edges()
        loop_slice.cfg.add_break_edges(final_break_nodes)
        num_edges_2 = loop_slice.cfg.num_edges()

        loop_ast = loop_slice.cfg.structure_loop_body(True or num_edges_1 != num_edges_2)

        # loop_slice.cfg.structure()
        # assert loop_slice.cfg.num_vertices() == 1
        # control_flow_tree = ControlFlowTree(None)
        # control_flow_tree.root = loop_slice.cfg.vertex_properties['ast'][loop_slice.cfg.vertex(0)]
        # control_flow_tree.conditions_map = self.conditions_map

        # control_flow_tree.replace_code_nodes_by_ast()
        # control_flow_tree.combine_sequence_nodes_with_sequence_children(control_flow_tree.root)
        # control_flow_tree.finalize()

        #loop_slice.update_break_edges()
        #loop_slice.update_return_nodes_edges()

        #control_flow_tree = loop_slice.control_flow_tree()
        #control_flow_tree.refine()
        # control_flow_tree.refine_cyclic()
        tail = [p for p in n_successor.in_neighbours() if p in loop_nodes] if n_successor is not None else []
        # self.draw_graph('/home/user/tmp/cfg_.dot')
        # print [int(x) for x in loop_nodes]
        self.collapse_region(header_node, tail, loop_nodes, loop_ast)

    def structure_loop_body(self, added_break_edges):
        assert is_DAG(self)
        if added_break_edges:
            i = 1
            header_found = False
            for v in self.vertices():
                if v.in_degree() == 0:
                    self.vertex_properties['is_header'][v] = 1
                    header_found = True
                    break
            if not header_found:
                self.vertex_properties['is_header'][self.vertex(0)] = 1

            no_progress = False
            while self.num_vertices() > 1 and not no_progress:
                no_progress = True
                assert i < 200, 'Max number of iterations'
                # self.compute_reachability_map()
                # self.draw_graph('g_l_{0}.png'.format(i))
                header = self.get_cfg_header()
                self.compute_dominator_tree(header)
                self.dfs_visitor = DepthFirstSearchVisitor()
                dfs_search(self, header, self.dfs_visitor)
                visited_nodes = []
                for n in self.dfs_visitor.postorder:
                    # print 'loop node: ', n
                    dominated_nodes = self.get_dominated_nodes(n)
                    if len(dominated_nodes) > 1:
                        if self.has_at_most_one_exit_node(dominated_nodes)\
                                or self.has_at_most_one_postdominating_successor(n, dominated_nodes):
                            tail_nodes = self.get_exit_nodes(dominated_nodes)
                            #structure_aprint 'structure_acyclic_l_{0}({1}, {2})'.format(i, int(n), [int(t) for t in tail_nodes])
                            self.structure_acyclic(n, tail_nodes, is_loop_body=True)
                            no_progress = False
                            break

                        tail_nodes = self.get_sub_region_tail(n, dominated_nodes, visited_nodes)
                        if tail_nodes is not None:
                            # print 'structure_acyclic_l_{0}({1}, {2})'.format(i, int(n), [int(t) for t in tail_nodes])
                            self.structure_acyclic(n, tail_nodes, is_loop_body=True)
                            no_progress = False
                            break

                    visited_nodes.append(n)
                i += 1
            if no_progress:
                tail_nodes = self.get_exit_nodes(set(self.vertices()))
                loop_slice = GraphSlice(self, header, tail_nodes, None, None)
                last_node_postdominates = len(tail_nodes) == 1
                control_flow_tree = loop_slice.control_flow_tree(last_node_postdominates)
                control_flow_tree.refine()
                control_flow_tree.replace_code_nodes_by_ast()
                control_flow_tree.combine_sequence_nodes_with_sequence_children(control_flow_tree.root)
                control_flow_tree.finalize()
            else:
                control_flow_tree = ControlFlowTree(None)
                control_flow_tree.root = self.vertex_properties['ast'][self.vertex(0)]
        else:
            tail_nodes = self.get_exit_nodes(set(self.vertices()))
            loop_slice = GraphSlice(self, self.get_cfg_header(), tail_nodes, None, None)
            control_flow_tree = loop_slice.control_flow_tree()
            control_flow_tree.refine()
        control_flow_tree.refine_cyclic()
        return control_flow_tree.root

    def refine_loop_exits(self, loop_slice):
        loop_header = loop_slice.slice_orig_map[loop_slice.header]
        n_loop = set(loop_slice.slice_orig_map.values())
        n_exit = set()
        for n in n_loop:
            n_exit.update([s for s in n.out_neighbours() if self.can_be_added_to_loop_nodes(s, loop_header, n_loop)])
        n_new = n_exit.copy()
        while self.num_exit_nodes(n_loop) > 1 and len(n_new) > 0:
            n_new.clear()
            for n in n_exit.copy():
                if self.all_predecessors_in_loop(n, n_loop):
                    n_loop.add(n)
                    loop_slice.add_node(n, self)
                    n_exit.remove(n)
                    n_new.update([s for s in n.out_neighbours()
                                  if self.can_be_added_to_loop_nodes(s, loop_header, n_loop) and s not in n_exit])
                    if self.num_exit_nodes(n_loop) <= 1:
                        return
            n_exit.update(n_new)

    def can_be_added_to_loop_nodes(self, n_exit, loop_header, loop_nodes):
        header_index = self.vertex_index[loop_header]
        exit_index = self.vertex_index[n_exit]
        return n_exit not in loop_nodes and self.dominator_tree.reachability_map[header_index][exit_index]\
            and not self.is_dominated_by_all_loop_nodes(n_exit, loop_nodes)

    def is_dominated_by_all_loop_nodes(self, n_exit, loop_nodes):
        n_exit_index = self.vertex_index[n_exit]
        for n in loop_nodes:
            n_index = self.vertex_index[n]
            if not self.dominator_tree.reachability_map[n_index][n_exit_index]:
                return False
        return True

    @staticmethod
    def num_exit_nodes(loop_nodes):
        exits = set()
        for n in loop_nodes:
            exits.update([s for s in n.out_neighbours() if s not in loop_nodes])
        return len(exits)

    @staticmethod
    def all_predecessors_in_loop(n, loop_nodes):
        return len([p for p in n.in_neighbours() if p not in loop_nodes]) == 0

    def loop_exits(self, loop_nodes):
        exits = []
        for n in loop_nodes:
            exits.extend([self.edge(n, s) for s in n.out_neighbours() if s not in loop_nodes])
        return exits

    """---------------------Abnormal Entries Restructuring-----------------------"""
    def restructure_abnormal_loop_entries(self, header, loop_nodes, abnormal_entry_edges, loop_slice):
        refined_loop_entries = self.refine_loop_entries(header, loop_nodes, abnormal_entry_edges, loop_slice)
        loop_slice.header = loop_slice.cfg.add_vertex()
        loop_slice.cfg.vertex_properties['type'][loop_slice.header] = NodeType.CONDITIONAL
        h_current = loop_slice.header
        for i in xrange(len(refined_loop_entries) - 1):
            entry_node = refined_loop_entries[i].target_node
            entry_condition = refined_loop_entries[i].condition_from_header
            edge_to_entry_node = loop_slice.cfg.add_edge(h_current, entry_node)
            loop_slice.cfg.edge_properties['tag'][edge_to_entry_node] = entry_condition
            if i < len(refined_loop_entries) - 2:
                false_child = loop_slice.cfg.add_vertex()
                loop_slice.cfg.vertex_properties['type'][false_child] = NodeType.CONDITIONAL
                edge_to_next_test = loop_slice.cfg.add_edge(h_current, false_child)
                loop_slice.cfg.edge_properties['tag'][edge_to_next_test] = Not(entry_condition)
                h_current = false_child

        n_last_entry = refined_loop_entries[-1].target_node
        e_last_entry = loop_slice.cfg.add_edge(h_current, n_last_entry)
        loop_slice.cfg.edge_properties['tag'][e_last_entry] = Not(refined_loop_entries[-2].condition_from_header)

    def refine_loop_entries(self, header, loop_nodes, abnormal_entry_edges, loop_slice):
        refined_entries = []
        entry_var = LocalVariable(self.make_new_variable_name(), 'int')
        self.variable_names[entry_var.name] = entry_var
        h_entries = [self.edge(p, header) for p in header.in_neighbours() if p not in loop_nodes]
        self.add_loop_entry_refinement_node(h_entries, SequenceNode(true, [self.make_assignment(entry_var, 0)]), header)
        refined_entries.append(RefinedLoopEntry(loop_slice.orig_slice_map[header],
                                                self.make_equality_condition(entry_var.deep_copy(), 0)))
        i = 1
        for abnormal_entry in abnormal_entry_edges:
            abnormal_entry_target = loop_slice.orig_slice_map[abnormal_entry[0].target()]
            if loop_slice.cfg.vertex_properties['type'][abnormal_entry_target] != NodeType.CODE:
                loop_slice.cfg.vertex_properties['type'][abnormal_entry_target] = NodeType.CODE
                loop_slice.cfg.vertex_properties['ast'][abnormal_entry_target] = SequenceNode(true, [])

            loop_slice.cfg.vertex_properties['ast'][abnormal_entry_target].children.append(self.make_assignment(entry_var.deep_copy(), 0))
            refined_entries.append(RefinedLoopEntry(abnormal_entry_target, self.make_equality_condition(entry_var.deep_copy(), i)))
            self.add_loop_entry_refinement_node(abnormal_entry, SequenceNode(true, [self.make_assignment(entry_var.deep_copy(), i)]), header)
            i += 1
        return refined_entries

    def add_loop_entry_refinement_node(self, entry_edges, ast, new_successor):
        v_pre = self.add_vertex()
        self.vertex_properties['type'][v_pre] = NodeType.CODE
        self.vertex_properties['ast'][v_pre] = ast
        for e_in in entry_edges:
            self.edge_properties['tag'][self.add_edge(e_in.source(), v_pre)] = self.edge_properties['tag'][e_in]
            self.remove_edge(e_in)
        self.edge_properties['tag'][self.add_edge(v_pre, new_successor)] = None

    @staticmethod
    def make_assignment(var, value):
        return Assignment(var, NumericConstant(value))

    def make_equality_condition(self, var, value):
        condition = Symbol('c_{0}_{1}'.format(var.name, value))
        self.conditions_map[condition] = HighLevelCondition(var, '==', NumericConstant(value))
        return condition

    def make_new_variable_name(self):
        suffix = 1
        new_name = 's'
        while new_name in self.variable_names:
            new_name = '{0}{1}'.format('s', suffix)
            suffix += 1
        return new_name

    def get_loop_abnormal_entry_edges(self, header, loop_nodes):
        abnormal_entries = []
        for n in loop_nodes:
            if n != header:
                abnormal_entries_to_n = [self.edge(v, n) for v in n.in_neighbours() if v not in loop_nodes]
                if abnormal_entries_to_n:
                    abnormal_entries.append(abnormal_entries_to_n)
        return abnormal_entries

    """---------------------Abnormal Exits Restructuring-----------------------"""
    def restructure_abnormal_loop_exits_using_structuring_variable(self, loop_nodes, loop_exit_edges):
        # self.draw_graph('t1.dot')
        in_loop_exit_nodes = set([e.source() for e in loop_exit_edges])
        ncd = self.nearest_common_dominator(in_loop_exit_nodes)
        loop_orig_successor = self.get_loop_successor(loop_exit_edges)

        abnormal_exit_edges = [e for e in loop_exit_edges if e.target() != loop_orig_successor]
        abnormal_exit_map = self.get_loop_abnormal_exit_map(loop_orig_successor, loop_nodes)

        exit_slice = self.compute_graph_slice(ncd, list(in_loop_exit_nodes))
        for x, preds in abnormal_exit_map.items():
            exit_slice.add_node(x, self, preds=preds)

        sorted_abnormal_exits = self.sort_abnormal_exits(exit_slice, abnormal_exit_edges)

        exit_var = LocalVariable(self.make_new_variable_name(), 'int')
        self.variable_names[exit_var.name] = exit_var

        exit_var_value = 0
        new_successor = self.add_vertex()
        self.vertex_properties['type'][new_successor] = NodeType.CONDITIONAL
        current_test_node = new_successor
        next_test_node = current_test_node
        exit_condition = None
        for n_exit in sorted_abnormal_exits:
            exit_stmt = self.make_assignment(exit_var, exit_var_value)
            for in_loop_pred in abnormal_exit_map[n_exit]:
                exit_edge = self.edge(in_loop_pred, n_exit)
                exit_tag = self.edge_properties['tag'][exit_edge]
                # print 'in_loop_pred:', in_loop_pred
                # print [int(v) for v in self.vertices()]
                if self.vertex_properties['type'][in_loop_pred] == NodeType.CODE:
                    self.vertex_properties['ast'][in_loop_pred].children.append(exit_stmt.deep_copy())
                    self.edge_properties['tag'][self.add_edge(in_loop_pred, new_successor)] = exit_tag
                else:
                    n = self.add_vertex()
                    self.vertex_properties['type'][n] = NodeType.CODE
                    self.vertex_properties['ast'][n] = SequenceNode(true, [exit_stmt.deep_copy()])
                    self.edge_properties['tag'][self.add_edge(in_loop_pred, n)] = exit_tag
                    self.edge_properties['tag'][self.add_edge(n, new_successor)] = None
                    loop_nodes.append(n)
                self.remove_edge(exit_edge)

            # add new condition after loop exit
            if exit_condition is not None:
                next_test_node = self.add_vertex()
                self.vertex_properties['type'][next_test_node] = NodeType.CONDITIONAL
                self.edge_properties['tag'][self.add_edge(current_test_node, next_test_node)] = Not(exit_condition)

            exit_condition = self.make_equality_condition(exit_var.deep_copy(), exit_var_value)
            self.edge_properties['tag'][self.add_edge(next_test_node, n_exit)] = exit_condition

            current_test_node = next_test_node
            exit_var_value += 1

        for e_exit in [e for e in loop_exit_edges if e.target() == loop_orig_successor]:
            exit_tag = self.edge_properties['tag'][e_exit]
            self.edge_properties['tag'][self.add_edge(e_exit.source(), new_successor)] = exit_tag
            self.remove_edge(e_exit)
        self.edge_properties['tag'][self.add_edge(current_test_node, loop_orig_successor)] = Not(exit_condition)

        # self.draw_graph('t2.png')
        return new_successor

    def restructure_abnormal_loop_exits_using_reaching_conditions(self, loop_nodes, loop_exit_edges):
        # self.draw_graph('t1.png')
        in_loop_exit_nodes = set([e.source() for e in loop_exit_edges])
        ncd = self.nearest_common_dominator(in_loop_exit_nodes)
        loop_successor = self.get_loop_successor(loop_exit_edges)

        """ start """
        abnormal_exit_edges = [e for e in loop_exit_edges if e.target() != loop_successor]
        abnormal_exit_map = self.get_loop_abnormal_exit_map(loop_successor, loop_nodes)
        # in_loop_abnormal_exit_nodes = in_loop_exit_nodes.difference(set([loop_successor]))
        exit_slice = self.compute_graph_slice(ncd, list(in_loop_exit_nodes))
        for x, preds in abnormal_exit_map.items():
            exit_slice.add_node(x, self, preds=preds)
        """ end """

        # abnormal_exits = self.get_loop_abnormal_exits(loop_successor, loop_nodes)
        # exit_slice = self.compute_graph_slice(ncd, abnormal_exits)

        reaching_conditions = exit_slice.cfg.find_reaching_conditions()
        for n in reaching_conditions:
            reaching_conditions[n] = to_cnf(reaching_conditions[n], simplify=True)
        #TODO structure reaching conditions to exit nodes
        sorted_abnormal_exits = self.sort_abnormal_exits(exit_slice, abnormal_exit_edges)#loop_exit_edges)

        new_successor = self.add_vertex()
        self.vertex_properties['type'][new_successor] = NodeType.CONDITIONAL
        for e_exit in loop_exit_edges:
            exit_tag = self.edge_properties['tag'][e_exit]
            self.edge_properties['tag'][self.add_edge(e_exit.source(), new_successor)] = exit_tag
            self.remove_edge(e_exit)

        current_test_node = new_successor
        current_exit_condition = true
        for n_exit in sorted_abnormal_exits:
            n_exit_slice = exit_slice.orig_slice_map[n_exit]
            next_exit_condition = reaching_conditions[n_exit_slice]
            remaining_condition = get_AND_remaining_term(to_cnf(Not(current_exit_condition), simplify=True), next_exit_condition)
            current_exit_condition = next_exit_condition if remaining_condition is None else remaining_condition
            self.edge_properties['tag'][self.add_edge(current_test_node, n_exit)] = current_exit_condition
            if sorted_abnormal_exits.index(n_exit) == len(sorted_abnormal_exits) - 1:
                self.edge_properties['tag'][self.add_edge(current_test_node, loop_successor)] = simplify_logic(Not(current_exit_condition))
            else:
                next_test_node = self.add_vertex()
                self.vertex_properties['type'][next_test_node] = NodeType.CONDITIONAL
                self.edge_properties['tag'][self.add_edge(current_test_node, next_test_node)] = simplify_logic(Not(current_exit_condition))
                current_test_node = next_test_node
        # self.draw_graph('t2.png')
        return new_successor

    def get_next_node_in_postorder(self):
        pass

    def get_loop_successor(self, exit_edges):
        successor_source = exit_edges[0].source()
        successor = exit_edges[0].target()
        for e_exit in exit_edges:
            if self.dfs_visitor.postorder.index(e_exit.source()) < self.dfs_visitor.postorder.index(successor_source):
                successor_source = e_exit.source()
                successor = e_exit.target()
        return successor

    @staticmethod
    def get_loop_abnormal_exits(loop_successor, loop_nodes):
        abnormal_exits = set()
        for n in loop_nodes:
            for s in n.out_neighbours():
                if s not in loop_nodes and s != loop_successor:
                    abnormal_exits.add(s)
        return list(abnormal_exits)

    @staticmethod
    def get_loop_abnormal_exit_map(loop_successor, loop_nodes):
        abnormal_exits = set()
        for n in loop_nodes:
            for s in n.out_neighbours():
                if s not in loop_nodes and s != loop_successor:
                    abnormal_exits.add(s)
        abnormal_exit_map = {}
        for x in abnormal_exits:
            abnormal_exit_map[x] = set([n for n in x.in_neighbours() if n in loop_nodes])
        return abnormal_exit_map

    @staticmethod
    def sort_abnormal_exits(exit_slice, loop_exit_edges):
        sorted_exits = []
        exit_slice.compute_topological_order()
        orig_topological_order = [exit_slice.slice_orig_map[n] for n in exit_slice.topological_order
                                  if n in exit_slice.slice_orig_map]
        for n_orig in orig_topological_order:
            for e_exit in loop_exit_edges:
                if e_exit.source() == n_orig:
                    if e_exit.target() not in sorted_exits:
                        sorted_exits.append(e_exit.target())
        return sorted_exits

    """--------------------------------------------"""

    def semantic_preserving_condition(self, src, dst, ignore_code_nodes=False):
        # self.draw_graph('g3.png')
        graph_slice = self.compute_graph_slice(src, dst)
        if ignore_code_nodes:
            found_new_code_node = True
            while found_new_code_node:
                found_new_code_node = False
                for v in graph_slice.cfg.vertices():
                    if v != graph_slice.header and v != graph_slice.tail:
                        if self.vertex_properties['type'][graph_slice.slice_orig_map[v]] == NodeType.CODE:
                            if v.in_degree() > 0 or v.out_degree() > 0:
                                found_new_code_node = True
                                graph_slice.cfg.clear_vertex(v)
                                # graph_slice.cfg.remove_node_edges(v)
                                break
        vertex_conditions = graph_slice.cfg.find_reaching_conditions()
        return vertex_conditions[graph_slice.orig_slice_map[dst]]

    # def remove_node_edges(self, n):
    #     succs = [s for s in n.out_neighbours()]
    #     for succ in succs:
    #         self.remove_edge(self.edge(n, succ))
    #
    #     preds = [p for p in n.in_neighbours()]
    #     for pred in preds:
    #         self.remove_edge(self.edge(pred, n))

    def restructure_abnormal_loop_entries_(self, header, abnormal_entries):
        for e_in in abnormal_entries:
            abnormal_entry_nodes = [e.source() for e in e_in]
            ncd = self.nearest_common_dominator(abnormal_entry_nodes + [header])
            h_new = self.add_vertex()
            self.vertex_properties['type'][h_new] = NodeType.CONDITIONAL
            sp_cond = false
            for n_abnormal in abnormal_entry_nodes:
                e_ab = self.edge(n_abnormal, e_in[0].target())
                e_tag = self.edge_properties['tag'][e_ab]
                e_tag = e_tag if e_tag is not None else true
                sp_cond = Or(sp_cond, And(self.semantic_preserving_condition(ncd, n_abnormal), e_tag))
                self.edge_properties['tag'][e_ab] = None
                self.remove_edge(e_ab)
                self.edge_properties['tag'][self.add_edge(n_abnormal, h_new)] = e_tag
            sp_cond = simplify_logic(sp_cond)

            header_predecessors = [p for p in header.in_neighbours()]
            for p in header_predecessors:
                in_edge = self.edge(p, header)
                e_tag = self.edge_properties['tag'][in_edge]
                self.edge_properties['tag'][in_edge] = None
                self.remove_edge(in_edge)
                if p in h_new.in_neighbours():
                    e_tag_new = simplify_logic(Or(e_tag, self.edge_properties['tag'][self.edge(p, h_new)]))
                    self.edge_properties['tag'][self.edge(p, h_new)] = e_tag_new if e_tag_new != true else None
                else:
                    self.edge_properties['tag'][self.add_edge(p, h_new)] = e_tag

            self.edge_properties['tag'][self.add_edge(h_new, e_in[0].target())] = sp_cond
            self.edge_properties['tag'][self.add_edge(h_new, header)] = Not(sp_cond)

            header = h_new

        #self.compute_reachability_map()
        self.compute_dominator_tree(self.get_cfg_header())
        return header

    def add_break_statements(self, loop_slice, successor_node):
        break_nodes = []
        #to avoid iterating over nodes that are added to the slice by the entry restructuring step
        for n, n_orig in loop_slice.slice_orig_map.items():
            if n_orig in successor_node.in_neighbours():
                #print '    successor_node: ', int(successor_node)
                if loop_slice.cfg.vertex_properties['type'][n] == NodeType.CODE:
                    tag_break = self.edge_properties['tag'][self.edge(n_orig, successor_node)]
                    loop_slice.add_break_node(n, break_nodes, tag_break)
                    #loop_slice.cfg.vertex_properties['ast'][n].ends_with_break = True
                elif loop_slice.cfg.vertex_properties['type'][n] == NodeType.CONDITIONAL:
                    tag_break = self.edge_properties['tag'][self.edge(n_orig, successor_node)]
                    loop_slice.add_break_node(n, break_nodes, tag_break)
        return break_nodes

    """--------------------Variable Merging------------------------"""
    def merge_congruent_variables(self):
        CongruenceAnalysis(self, self.id_statement_map()).apply()

    def id_statement_map(self):
        stmt_id = 0
        id_stmt_map = {}
        for v in self.vertices():
            if self.vertex_properties['type'][v] == NodeType.CODE:
                #stmts = self.vertex_properties['ast'][v].instructions
                stmts = self.vertex_properties['ast'][v].children
            elif self.vertex_properties['type'][v] == NodeType.CONDITIONAL:
                tag = self.edge_properties['tag'][self.edge(v, v.out_neighbours().next())]
                stmts = [self.conditions_map[tag if isinstance(tag, Symbol) else tag.args[0]]]

            for stmt in stmts:
                id_stmt_map[stmt_id] = stmt
                stmt_id += 1
        return id_stmt_map

    def remove_empty_code_nodes(self):
        empty_node = self.get_empty_node()
        while empty_node is not None:
            #print 'empty_node: ', int(empty_node)
            predecessors = [p for p in empty_node.in_neighbours()]
            successors = [s for s in empty_node.out_neighbours()]
            if successors:
                assert len(successors) == 1
                successor = successors[0]
                for p in predecessors:
                    e = self.edge(p, empty_node)
                    e_tag = self.edge_properties['tag'][e]
                    e_succ = self.add_edge(p, successor)
                    self.edge_properties['tag'][e_succ] = e_tag
                    self.edge_properties['tag'][e] = None

            self.clear_vertex(empty_node)
            self.remove_vertex(empty_node)
            empty_node = self.get_empty_node()

    def is_empty_code_node(self, node):
        if self.vertex_properties['type'][node] == NodeType.CODE:
            ast = self.vertex_properties['ast'][node]
            if isinstance(ast, SequenceNode):
                if not ast.children and node.out_degree() == 1:
                    return True
        return False

    def get_empty_node(self):
        for v in self.vertices():
            if self.vertex_properties['type'][v] == NodeType.CODE:
                ast = self.vertex_properties['ast'][v]
                if isinstance(ast, SequenceNode) and not ast.children:
                    #if v.out_degree() == 1 or (v.out_degree() == 0 and v.in_degree() == 1):
                    if v.out_degree() == 1 \
                            or (v.out_degree() == 0
                                and all(self.vertex_properties['type'][p] == NodeType.CODE for p in v.in_neighbours())):
                        return v
        return None

    def remove_isolated_nodes(self):
        # has_isolated_nodes = True
        # while has_isolated_nodes:
        #     has_isolated_nodes = False
        #     for n in self.vertices():
        #         if n.in_degree() == 0 and n.out_degree() == 0:
        #             self.remove_vertex(n)
        #             has_isolated_nodes = True
        #             break
        isolated_node = self.get_isolated_node()
        while isolated_node is not None:
            self.remove_vertex(isolated_node)
            isolated_node = self.get_isolated_node()

    def get_isolated_node(self):
        for v in self.vertices():
            if v.in_degree() == 0 and v.out_degree() == 0:
                return v
        return None

    """--------------------------------------------"""

    def combine_single_pred_single_succ_nodes(self):
        simple_seq = self.get_simple_sequence()
        while simple_seq is not None:
            if simple_seq[-1].out_degree() == 1:
                e = self.add_edge(simple_seq[0], simple_seq[-1].out_neighbours().next())
                self.edge_properties['tag'][e] = None
            ast = self.vertex_properties['ast'][simple_seq[0]]
            for v in simple_seq[1:]:
                ast.children.extend(self.vertex_properties['ast'][v].children)
                self.clear_vertex(v)

            if set(simple_seq) == {v for v in self.vertices()}:
                self.clear()
                self.add_code_node(ast.children)
                return

            self.remove_isolated_nodes()
            simple_seq = self.get_simple_sequence()

    def get_simple_sequence(self):
        for v in self.vertices():
            if v.out_degree() == 1:
                v_succ = v.out_neighbours().next()
                if v_succ.in_degree() == 1 and v_succ.out_degree() <= 1:
                    path_nodes = [v, v_succ]
                    self.extend_sequence(path_nodes)
                    return path_nodes
        return None

    @staticmethod
    def extend_sequence(path_vertices):
        v_start = path_vertices[0]
        while v_start.in_degree() == 1 and v_start.in_neighbours().next().out_degree() == 1:
            v_start = v_start.in_neighbours().next()
            path_vertices.insert(0, v_start)

        v_end = path_vertices[-1]
        while v_end.out_degree() == 1:
            v_end = v_end.out_neighbours().next()
            if v_end.in_degree() != 1 or v_end.out_degree() != 1:
                break
            path_vertices.append(v_end)

    """--------------------------------------------"""

    def draw_graph(self, image_file):
        node_map = dict()
        dot_graph = pydot.Dot(graph_type='digraph')

        for v in self.vertices():
            if self.vertex_properties['type'][v] == NodeType.CODE:
                ast = self.vertex_properties['ast'][v]
                if isinstance(ast, SequenceNode) and not ast.children:
                    dot_node = pydot.Node(str(int(v)), style='filled', fillcolor="red")
                else:
                    dot_node = pydot.Node(str(int(v)))
            else:
                dot_node = pydot.Node(str(int(v)), style='filled', fillcolor="green")
            dot_graph.add_node(dot_node)
            node_map[int(v)] = dot_node

        for e in self.edges():
            src_node = node_map[int(e.source())]
            dst_node = node_map[int(e.target())]
            if self.edge_properties['tag'][e] is not None:
                e = pydot.Edge(src_node, dst_node, label=str(simplify_logic(self.edge_properties['tag'][e])))
            else:
                e = pydot.Edge(src_node, dst_node)

            dot_graph.add_edge(e)
                                    #label = str(self.edge_tags[e]) if e in self.edge_tags else ""))
        # dot_graph.write(image_file)
        dot_graph.write('/home/user/Pictures/' + image_file)
