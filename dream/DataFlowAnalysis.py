# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from graph_tool.search import dfs_search
from sympy.core.symbol import Symbol
from dream.ir.expressions import LocalVariable, Call
from dream.ir.instructions import Instruction, Assignment
from dream.enums import NodeType
from dream.graph_visitors import DepthFirstSearchVisitor


class DataFlowInfo:
    def __init__(self, live_in, live_out, reach_in, reach_out):
        self.live_in = live_in
        self.live_out = live_out
        self.reach_in = reach_in
        self.reach_out = reach_out
        self.id_stmt_map = {}


class DataFlowAnalysis:
    def __init__(self, cfg, id_stmt_map):
        self.cfg = cfg
        self.id_stmt_map = id_stmt_map
        self.gen_b = {}
        self.kill_b = {}
        self.in_b = {v: set() for v in self.cfg.vertices()}
        self.out_b = {v: set() for v in self.cfg.vertices()}

        self.gen_s = {stmt_id: set() for stmt_id in self.id_stmt_map}
        self.kill_s = {stmt_id: set() for stmt_id in self.id_stmt_map}
        self.in_s = {stmt_id: set() for stmt_id in self.id_stmt_map}
        self.out_s = {stmt_id: set() for stmt_id in self.id_stmt_map}

        self.defs = {}
        self.uses = {}

    def sets_changed(self, old_in, old_out):
        for v in self.cfg.vertices():
            if old_in[v] ^ self.in_b[v] or old_out[v] ^ self.out_b[v]:
                return True
        return False

    def compute_defs(self):
        for stmt_id, stmt in self.id_stmt_map.items():
            if isinstance(stmt, Instruction):
                for d in [var for var in stmt.defs() if isinstance(var, LocalVariable)]:
                    if d not in self.defs:
                        self.defs[d] = set()
                    self.defs[d].add(stmt_id)

    def compute_uses(self):
        for stmt_id, stmt in self.id_stmt_map.items():
            used_vars = stmt.uses() if isinstance(stmt, Instruction) else stmt.elements()
            for u in [var for var in used_vars if isinstance(var, LocalVariable)]:
                if u not in self.uses:
                    self.uses[u] = set()
                self.uses[u].add(stmt_id)


class ReachingDefinitionsAnalysis(DataFlowAnalysis):
    def __init__(self, cfg, id_stmt_map):
        DataFlowAnalysis.__init__(self, cfg, id_stmt_map)
        self.defs = {}

    def apply(self):
        self.compute_defs()
        self.compute_gens_kills()
        dfs = DepthFirstSearchVisitor()
        dfs_search(self.cfg, self.cfg.vertex(0), dfs)
        done = False
        while not done:
            in_old = {n: {var for var in var_set} for (n, var_set) in self.in_b.items()}
            out_old = {n: {var for var in var_set} for (n, var_set) in self.out_b.items()}
            for v in reversed(dfs.postorder):
                self.in_b[v].clear()
                for p in v.in_neighbours():
                    self.in_b[v].update(self.out_b[p])
                self.out_b[v] = self.gen_b[v] | (self.in_b[v] - self.kill_b[v])
            done = not self.sets_changed(in_old, out_old)
        self.propagate_dataflow_to_statements()

    def compute_gens_kills(self):
        for v in self.cfg.vertices():
            self.gen_b[v] = set()
            self.kill_b[v] = set()
            if self.cfg.vertex_properties['type'][v] == NodeType.CODE:
                #for stmt in self.cfg.vertex_properties['ast'][v].instructions:
                for stmt in self.cfg.vertex_properties['ast'][v].children:
                    stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(stmt)]
                    if isinstance(stmt, Instruction):
                        for d in stmt.defs():
                            if isinstance(d, LocalVariable):
                                self.gen_s[stmt_id] = {stmt_id}
                                self.kill_s[stmt_id] = self.defs[d] - self.gen_s[stmt_id]
                                self.gen_b[v] = self.gen_s[stmt_id] | (self.gen_b[v] - self.kill_s[stmt_id])
                                self.kill_b[v].update(self.kill_s[stmt_id])

    def propagate_dataflow_to_statements(self):
        for n in self.cfg.vertices():
            reach_in = self.in_b[n]
            if self.cfg.vertex_properties['type'][n] == NodeType.CODE:
                #for stmt in self.cfg.vertex_properties['ast'][n].instructions:
                for stmt in self.cfg.vertex_properties['ast'][n].children:
                    stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(stmt)]
                    self.in_s[stmt_id] = reach_in
                    self.out_s[stmt_id] = self.gen_s[stmt_id] | (reach_in - self.kill_s[stmt_id])
                    reach_in = self.out_s[stmt_id]
            elif self.cfg.vertex_properties['type'][n] == NodeType.CONDITIONAL:
                tag = self.cfg.edge_properties['tag'][self.cfg.edge(n, n.out_neighbours().next())]
                cond_expr = self.cfg.conditions_map[tag if isinstance(tag, Symbol) else tag.args[0]]
                stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(cond_expr)]
                self.in_s[stmt_id] = self.in_b[n]
                self.out_s[stmt_id] = self.out_b[n]
            assert reach_in == self.out_b[n], "{0}: {1} != {2}".format(int(n), [int(i) for i in reach_in],
                                                                  [int(i) for i in self.out_b[n]])

    def reaching_definitions(self, of_var, at_stmt):
        reaching_defs = []
        for s in self.in_s[at_stmt]:
            if of_var in self.id_stmt_map[s].defs():
                reaching_defs.append(self.id_stmt_map[s])
        return reaching_defs


class LivenessAnalysis(DataFlowAnalysis):
    def __init__(self, cfg, id_stmt_map):
        DataFlowAnalysis.__init__(self, cfg, id_stmt_map)

    def apply(self):
        self.compute_gens_kills()
        dfs = DepthFirstSearchVisitor()
        dfs_search(self.cfg, self.cfg.vertex(0), dfs)
        done = False
        while not done:
            in_old = {n: {var for var in var_set} for (n, var_set) in self.in_b.items()}
            out_old = {n: {var for var in var_set} for (n, var_set) in self.out_b.items()}

            for v in dfs.postorder:
                self.out_b[v].clear()
                for s in v.out_neighbours():
                    self.out_b[v].update(self.in_b[s])
                self.in_b[v] = self.gen_b[v] | (self.out_b[v] - self.kill_b[v])
            done = not self.sets_changed(in_old, out_old)
        self.propagate_dataflow_to_statements()

    def compute_gens_kills(self):
        for v in self.cfg.vertices():
            self.gen_b[v] = set()
            self.kill_b[v] = set()

            if self.cfg.vertex_properties['type'][v] == NodeType.CODE:
                #for stmt in reversed(self.cfg.vertex_properties['ast'][v].instructions):
                for stmt in reversed(self.cfg.vertex_properties['ast'][v].children):
                    stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(stmt)]
                    if isinstance(stmt, Call):
                        defs = set()
                        uses = {u for u in stmt.elements() if isinstance(u, LocalVariable)}
                    else:
                        defs = {d for d in stmt.defs() if isinstance(d, LocalVariable)}
                        uses = {u for u in stmt.uses() if isinstance(u, LocalVariable)}
                    self.gen_s[stmt_id] = uses
                    self.kill_s[stmt_id] = defs
                    self.gen_b[v] = uses | (self.gen_b[v] - defs)
                    self.kill_b[v].update(defs)

            elif self.cfg.vertex_properties['type'][v] == NodeType.CONDITIONAL:
                tag = self.cfg.edge_properties['tag'][self.cfg.edge(v, v.out_neighbours().next())]
                cond_expr = self.cfg.conditions_map[tag if isinstance(tag, Symbol) else tag.args[0]]
                stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(cond_expr)]
                self.gen_b[v] = {u for u in cond_expr.elements() if isinstance(u, LocalVariable)}
                self.gen_s[stmt_id] = {u for u in cond_expr.elements() if isinstance(u, LocalVariable)}

    def propagate_dataflow_to_statements(self):
        for n in self.cfg.vertices():
            if self.cfg.vertex_properties['type'][n] == NodeType.CODE:
                live_out = self.out_b[n]
                #for stmt in reversed(self.cfg.vertex_properties['ast'][n].instructions):
                for stmt in reversed(self.cfg.vertex_properties['ast'][n].children):
                    stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(stmt)]
                    self.out_s[stmt_id] = live_out
                    self.in_s[stmt_id] = self.gen_s[stmt_id] | (live_out - self.kill_s[stmt_id])
                    live_out = self.in_s[stmt_id]
                assert live_out == self.in_b[n]
            elif self.cfg.vertex_properties['type'][n] == NodeType.CONDITIONAL:
                tag = self.cfg.edge_properties['tag'][self.cfg.edge(n, n.out_neighbours().next())]
                cond_expr = self.cfg.conditions_map[tag if isinstance(tag, Symbol) else tag.args[0]]
                stmt_id = self.id_stmt_map.keys()[self.id_stmt_map.values().index(cond_expr)]
                self.out_s[stmt_id] = self.out_b[n]
                self.in_s[stmt_id] = self.gen_s[stmt_id] | (self.out_b[n] - self.kill_s[stmt_id])
                assert self.in_s[stmt_id] == self.in_b[n], "{0}: {1} != {2}".format(int(n), [str(i) for i in self.in_s[stmt_id]],
                                                                                    [str(i) for i in self.in_b[n]])

    def is_live_in(self, var, at_stmt):
        return var in self.in_s[at_stmt]

    def is_live_out(self, var, at_stmt):
        return var in self.out_s[at_stmt]


class CongruenceAnalysis(DataFlowAnalysis):
    def __init__(self, cfg, id_stmt_map):
        DataFlowAnalysis.__init__(self, cfg, id_stmt_map)
        self.liveness_alg = LivenessAnalysis(cfg, id_stmt_map)
        self.liveness_alg.apply()
        self.reaching_alg = ReachingDefinitionsAnalysis(cfg, id_stmt_map)
        self.reaching_alg.apply()
        self.compute_uses()
        self.compute_defs()
        self.variables_map = self.compute_variables_map()

    def apply(self):
        found_congruences = False
        for stmt_id, stmt in self.id_stmt_map.items():
            if self.is_copy_stmt(stmt):
                # print 'handling: {0} -> {1}'.format(stmt_id, str(stmt))
                lhs_var, rhs_var = stmt.lhs_operand, stmt.rhs_operand
                if self.all_reaching_definitions_equal(lhs_var, self.uses[rhs_var], rhs_var)\
                        and self.all_definitions_not_in_live_range(rhs_var, lhs_var):
                    # print "Congruent Variables: ", lhs_var, rhs_var, lhs_var == rhs_var
                    if not(lhs_var == rhs_var):
                        if rhs_var == self.cfg.function_signature.return_value or rhs_var in self.cfg.function_signature.parameters:
                            self.rename(lhs_var.name, rhs_var.name)
                        else:
                            self.rename(rhs_var.name, lhs_var.name)
                        found_congruences = True

        if found_congruences:
            has_emtpy_nodes = False
            for v in self.cfg.vertices():
                if self.cfg.vertex_properties['type'][v] == NodeType.CODE:
                    basic_block = self.cfg.vertex_properties['ast'][v]
                    basic_block.children = [stmt for stmt in basic_block.children
                                            if not self.is_trivial_copy_stmt(stmt)]
                    if not basic_block.children:
                        has_emtpy_nodes = True
            if has_emtpy_nodes:
                self.cfg.remove_empty_code_nodes()


    def rename(self, old_name, new_name):
        for v in self.variables_map[old_name]:
            v.name = new_name
            self.variables_map[new_name].append(v)
        del self.variables_map[old_name]

    def all_definitions_not_in_live_range(self, var_d, of_variable):
        if var_d in self.defs:
            for d in self.defs[var_d]:
                if self.in_live_range(d, of_variable) and not self.is_copy_stmt_(self.id_stmt_map[d], var_d, of_variable):
                    return False
        return True

    def in_live_range(self, stmt_id, of_variable):
        return self.liveness_alg.is_live_out(of_variable, stmt_id)

    def all_reaching_definitions_equal(self, variable, at_stmts, value):
        for stmt_id in at_stmts:
            stmt = self.id_stmt_map[stmt_id]
            if not self.is_copy_stmt_(stmt, variable, value) and not self.reaching_value_equals(variable, stmt_id, value):
                return False
        return True

    def reaching_value_equals(self, of_variable, at_stmt, value):
        reaching_defs = self.reaching_alg.reaching_definitions(of_variable, at_stmt)
        for def_stmt in reaching_defs:
            if not self.is_copy_stmt_(def_stmt, of_variable, value):
                return False
        return True

    @staticmethod
    def is_trivial_copy_stmt(stmt):
        return isinstance(stmt, Assignment) and stmt.lhs_operand == stmt.rhs_operand

    @staticmethod
    def is_copy_stmt_(stmt, lhs, rhs):
        return isinstance(stmt, Assignment) and stmt.lhs_operand == lhs and stmt.rhs_operand == rhs

    @staticmethod
    def is_copy_stmt(stmt):
        return isinstance(stmt, Assignment)\
            and isinstance(stmt.lhs_operand, LocalVariable) \
            and isinstance(stmt.rhs_operand, LocalVariable)

    def compute_variables_map(self):
        var_map = {}
        for stmt in self.id_stmt_map.values():
            vars = stmt.defs() + stmt.uses() if isinstance(stmt, Instruction) else stmt.elements()
            for v in [var for var in vars if isinstance(var, LocalVariable)]:
                if v.name not in var_map:
                    var_map[v.name] = []
                var_map[v.name].append(v)
        return var_map
