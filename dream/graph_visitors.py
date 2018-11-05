# Copyright (C) 2011-2017 Khaled Yakdan.
# All rights reserved.

from graph_tool.search import DFSVisitor


class SliceVisitor(DFSVisitor):
    def __init__(self, v_src, v_dst, gSlice):
        self.stk = []
        self.v_src = v_src
        self.v_dst = v_dst
        self.gSlice = gSlice
        self.graphToSliceNodeMap = {}

    def discover_vertex(self, u):
        self.stk.append(u)
        if u == self.v_dst:
            self.addEdgeSeries()

    def getSlicedNode(self, orig_node):
        if orig_node not in self.graphToSliceNodeMap:
            slice_node = self.gSlice.add_vertex()
            self.graphToSliceNodeMap[orig_node] = slice_node
            self.gSlice.vertex_properties['orig'][slice_node] = orig_node
        return self.graphToSliceNodeMap[orig_node]

    def addEdgeSeries(self):
        for i in range(len(self.stk)):
            if i == len(self.stk) - 1:
                break
            self.addEdge(self.getSlicedNode(self.stk[i]), self.getSlicedNode(self.stk[i+1]))

    def addEdge(self, s, d):
        if d not in s.out_neighbours():
            self.gSlice.add_edge(s, d)

    def examine_edge(self, e):
        while len(self.stk) != 0 and e.source() != self.stk[-1]:
            self.stk.pop()
        if e.target() in self.graphToSliceNodeMap and e.target() not in self.stk:
            self.stk.append(e.target())
            self.addEdgeSeries()
            self.stk.pop()


class DepthFirstSearchVisitor(DFSVisitor):
    def __init__(self):
        self.postorder = []
        self.back_edges = []

    def finish_vertex(self, v):
        self.postorder.append(v)

    def back_edge(self, e):
        self.back_edges.append(e)

