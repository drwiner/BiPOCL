import collections

from Ground_Compiler_Library.Graph import Graph, Edge
from Ground_Compiler_Library.Element import Element
#from clockdeco import clock


class OrderingGraph(Graph):
	def __init__(self, ID=None, typ=None, name=None, Elements=None, Edges=None):
		if typ is None:
			typ = 'ordering graph'
		super(OrderingGraph, self).__init__(ID, typ, name, Elements, Edges)

	def __len__(self):
		return len(self.edges)

	def isInternallyConsistent(self):

		if len(self) == 0:
			return True

		# cycles mean not consistent
		if self.detectCycle():
			return False

		# 2 cntgs means not consistent
		if not self.cntg_consistent():
			return False

		return True

	def addLabeledEdge(self, source, sink, label):
		if label == "cntg":
			self.addCntg(source, sink)
		else:
			self.addEdge(source, sink)

	def addEdge(self, source, sink):

		if self.isPath(source, sink):
			return
		self.elements.add(source)
		self.elements.add(sink)
		self.edges.add(Edge(source, sink, '<'))

		if self.isCntgPath(source, sink):
			return
		# check cntg_source of sink
		cntg_of_sink = self.get_source_of_cntg(sink)
		if cntg_of_sink != sink and cntg_of_sink != source:
			self.addEdge(source, cntg_of_sink)
		cntg_of_source = self.get_sink_of_cntg(source)
		if cntg_of_source != source and cntg_of_source != sink:
			self.addEdge(cntg_of_source, sink)

	def addCntg(self, source, sink):
		self.addEdge(source, sink)
		self.edges.add(Edge(source, sink, "cntg"))

	def detectCycle(self, ):
		''' Returns True if cycle, False otherwise
			Strategy: for each element, find descendent elements. If a is descendant of b and b is descendant of a,
			then there is a cycle'''

		for element in self.elements:
			visited = self.rDetectCycle(element) - {element}
			predecessors = set(edge.source for edge in self.edges if edge.sink.ID == element.ID)
			# predecessors = self.getParents(element)
			for elm in visited:
				if elm in predecessors:
					return True
		return False

	######       rDetect       ####################
	def rDetectCycle(self, element, visited=None):
		if visited is None:
			visited = set()

		# Base Case 1
		if element in visited:
			return visited

		visited.add(element)

		# Base Case 2
		incidentEdges = self.getIncidentEdges(element)
		if len(incidentEdges) == 0:
			return visited

		# Induction
		for edge in incidentEdges:
			# Descendants.add(edge.sink)
			visited = self.rDetectCycle(edge.sink, visited=visited)
		return visited

	def foundPath(self, start, finish):
		""" Returns if there is path start to finish (1) finish to start (2) or none at all (0)"""
		visited = self.rDetectCycle(start)
		if visited:
			if finish in visited:
				return 1
		visited2 = self.rDetectCycle(finish)
		if visited2:
			if start in visited2:
				return 2
		return 0

	#@clock
	def isPath(self, start, finish):
		"""Returns True if path from start to Finish, False otherwise"""
		visited = self.rDetectCycle(start)
		if visited:
			if finish in visited:
				return True
		return False

	def isCntgPath(self, start, finish):
		while True:
			cntg_edges = list(self.getIncomingEdgesByLabel(finish, "cntg"))
			if len(cntg_edges) == 0:
				break
			if len(cntg_edges) > 1:
				raise ValueError("multiple cntg edges? that\'s impossible!!")
			if cntg_edges[0].source == start:
				return True
			finish = cntg_edges[0].source
		return False

	def get_sink_of_cntg(self, start):
		cntg_edges = list(self.getIncidentEdgesByLabel(start, "cntg"))
		if len(cntg_edges) == 0:
			return start
		if len(cntg_edges) > 1:
			raise ValueError("multiple cntg edges? that\'s impossible!!")
		return self.get_sink_of_cntg(cntg_edges[0].sink)

	def get_source_of_cntg(self, start):
		cntg_edges = list(self.getIncomingEdgesByLabel(start, "cntg"))
		if len(cntg_edges) == 0:
			return start
		if len(cntg_edges) > 1:
			raise ValueError("multiple cntg edges? that\'s impossible!!")
		return self.get_source_of_cntg(cntg_edges[0].source)

	def cntg_consistent(self):
		cntg_edges = [edge for edge in self.edges if edge.label == "cntg"]
		sources = []
		sinks = []
		# cntg must be s -> t -> u and cannot exist another s -> s' or t' -> u
		for edge in cntg_edges:
			if edge.sink in sinks:
				return False
			if edge.source in sources:
				return False
			sources.append(edge.source)
			sinks.append(edge.sink)
			# cannot be an ordering between cntg edge e.g. s --cntg--> t and s < u < t
			ordering_edges = [ord for ord in self.edges if ord.source == edge.source and ord.sink != edge.sink and ord.label == "<"]
			for ord in ordering_edges:
				if self.isPath(ord.sink, edge.sink):
					return False
			ordering_edges = [ord for ord in self.edges if ord.sink == edge.sink and ord.source != edge.source and ord.label == "<"]
			for ord in ordering_edges:
				if self.isPath(edge.source, ord.source):
					return False

		return True

	def topoSort(self):
		L = []
		for step in self.elements:
			L.append(step)
			for i in range(len(L)-1):
				if self.isPath(step, L[i]):
					L.insert(i, step)
					L = L[0:-1]
					break
		return L

	def __lt__(self, other):
		#only compared when already has same number of elements
		if len(self.edges) != len(other.edges):
			return len(self.edges) < len(other.edges)

		S = list(self.elements)
		S.sort(key=lambda x: x.stepnumber)
		O = list(other.elements)
		O.sort(key=lambda x: x.stepnumber)
		for s, o in zip(S, O):
			if s.stepnumber != o.stepnumber:
				return s.stepnumber < o.stepnumber
			sumo = self.numOutgoing(s)
			oumo = other.numOutgoing(o)
			if sumo != oumo:
				return sumo < oumo


	def numOutgoing(self, step):
		return len({ordering for ordering in self.edges if ordering.source == step})

	def __repr__(self):
		return str(['{} < {}'.format(edge.source, edge.sink) for edge in self.edges])


class CausalLinkGraph(OrderingGraph):
	def __init__(self, ID=None, typ=None, name=None, Elements=None, Edges=None):
		if typ is None:
			typ = 'causal link graph'
		super(CausalLinkGraph, self).__init__(ID, typ, name, Elements, Edges)
		self.nonThreats = collections.defaultdict(set)

	def addEdge(self, source, sink, condition):
		self.elements.add(source)
		self.elements.add(sink)
		new_link = Edge(source, sink, condition)
		self.edges.add(new_link)
		return new_link

	def __repr__(self):
		return str(['{} --{}--> {}'.format(edge.source, edge.label, edge.sink) for edge in self.edges])




import unittest

class TestOrderingGraphMethods(unittest.TestCase):
	def test_detect_cycle(self):
		Elms = [Element(ID=0, name='0'), Element(ID=1, name='1'), Element(ID=2, name='2'), Element(ID=3, name='3')]
		edges = {Edge(Elms[0], Elms[1], '<'), Edge(Elms[0], Elms[2], '<'), Edge(Elms[0], Elms[3], '<'),
				 Edge(Elms[2], Elms[1], '<'), Edge(Elms[3], Elms[1], '<')}
		G = Graph(ID=10, typ='test', Elements=set(Elms), Edges=edges)
		OG = OrderingGraph(ID=5, Elements=G.elements, Edges=G.edges)
		assert (not OG.detectCycle())
		OG.edges.add(Edge(Elms[1], Elms[0], '<'))
		assert (OG.detectCycle())

	# Graph.get
	# OG.isPath()


if __name__ == '__main__':
	unittest.main()