from Ground_Compiler_Library.OrderingGraph import OrderingGraph, CausalLinkGraph
from Flaws import Flaw, FlawLib, TCLF
from uuid import uuid4
from Ground_Compiler_Library.Element import Argument, Element, Operator, Literal
from Ground_Compiler_Library.Graph import Edge
from Ground_Compiler_Library.ElementGraph import ElementGraph
import copy
import collections
from clockdeco import clock
import itertools

class Action(ElementGraph):
	# stepnumber = 2
	def __init__(self, ID=None, type_graph=None, name=None, Elements=None, root_element=None, Edges=None):

		if type_graph is None:
			type_graph = 'Action'

		if Edges is None:
			Edges = set()

		if root_element is None:
			root_element = Operator()

		if Elements is None:
			Elements = {root_element}

		self.nonequals = set()
		self.is_decomp = False
		self.height = root_element.height
		if self.height > 0:
			self.sub_dummy_init = None
			self.sub_dummy_goal = None

		super(Action, self).__init__(ID, type_graph, name, Elements, root_element, Edges)
		self.replaced_ID = root_element.replaced_ID
		self.is_cndt = True
		self.has_cndt = True


	def __hash__(self):
		return hash(arg for arg in self.Args) ^ hash(self.root.name)

	def __eq__(self, other):
		if not isinstance(other, ElementGraph):
			return False
		if self.root.name == other.root.name:
			if self.Args == other.Args:
				return True
		return False

	# @property
	# def executed(self):
	# 	return self.root.executed

	def RemoveSubgraph(self, elm):
		edges = list(self.edges)
		elm = self.getElementById(elm.ID)

		if isinstance(elm, Literal):
			self.elements.remove(elm)

		link = None
		for edge in list(self.edges):
			if edge.source == elm:
				edges.remove(edge)
			if link is None:
				if edge.sink == elm:
					link = edge
		edges.remove(link)
		self.edges = set(edges)
		return link

	@property
	def Preconditions(self):
		self.updatePreconditionsOrEffects('precond-of')
		return [Condition.subgraph(self, pre) for pre in self.preconditions]

	@property
	def Effects(self):
		self.updatePreconditionsOrEffects('effect-of')
		return [Condition.subgraph(self, eff) for eff in self.effects]

	def updatePreconditionsOrEffects(self, label):
		if label == 'effect-of':
			self.effects = self.getPreconditionsOrEffects(label)
		elif label == 'precond-of':
			self.preconditions = self.getPreconditionsOrEffects(label)

	def getPreconditionsOrEffects(self, label):
		return [edge.sink for edge in self.edges if edge.label == label and edge.source == self.root]

	def __getattr__(self, name):
		if name == 'preconditions':
			self.preconditions = self.getPreconditionsOrEffects('precond-of')
			return self.preconditions
		elif name == 'effects':
			self.effects = self.getPreconditionsOrEffects('effect-of')
			return self.effects
		elif name == 'Args':
			self.updateArgs()
			return self.Args
		else:
			raise AttributeError('no attribute {}'.format(name))

	@property
	def stepnumber(self):
		return self.root.stepnumber

	def replaceInternals(self):
		self.ID = uuid4()
		for elm in self.elements:
			if not isinstance(elm, Argument):
				if hasattr(self, "ground_subplan"):
					# then also replace sub-plan ops
					sub_plan_elm = self.ground_subplan.getElementById(elm.ID)
					elm.ID = uuid4()
					if sub_plan_elm is not None:
						sub_plan_elm.ID = elm.ID
						if elm.arg_name is not None and elm.arg_name != sub_plan_elm.arg_name:
							sub_plan_elm.arg_name = elm.arg_name
				else:
					elm.ID = uuid4()

		# need this to refresh mutable IDs
		self.elements = set(list(self.elements))
		self.edges = set(list(self.edges))
		if hasattr(self, "ground_subplan"):
			self.ground_subplan.elements = set(list(self.ground_subplan.elements))
			self.ground_subplan.edges = set(list(self.ground_subplan.edges))
			# print('check result')

	# USE THIS ONLY when creating GROUND STEPS for first time (replacing replaced_ID)
	def _replaceInternals(self):
		self.ID = uuid4()
		for elm in self.preconditions:
			elm.replaced_ID = uuid4()
		for elm in self.effects:
			elm.replaced_ID = uuid4()
		self.root.replaced_ID = uuid4()

		""" Note to self: if you have a nested literal (e.g. Bel(intends(a, has(a, j))) )
			then, the arguments won't get a new replaced_ID.
		"""

	def deepcopy(self, replace_internals=None, _replace_internals=None):
		new_self = copy.deepcopy(self)
		if replace_internals is not None:
			new_self.replaceInternals()
		if _replace_internals is not None:
			new_self._replaceInternals()
		return new_self


	# '''for debugging'''
	# def getConditions(self):
	# pres = {edge for edge in self.edges if edge.label == 'precond-of'}
	# effs = {edge for edge in self.edges if edge.label == 'effect-of'}
	# print('Preconditions:\n')
	# for pre in pres:
	# pre.sink
	# print('Effects:\n')
	# for eff in effs:
	# eff.sink

	def isConsistent(self, other):
		""" an action is consistent just when one can absolve the other"""
		if isinstance(other, ElementGraph):
			return self.isConsistentSubgraph(other)
		if isinstance(other, Operator):
			return self.root.isConsistent(other)


	def argify(self, arg):
		if isinstance(arg, Operator):
			return str(Action.subgraph(self, arg))
		elif isinstance(arg, Literal):
			return str(Condition.subgraph(self, arg))
		else:
			return arg.name

	def __repr__(self):
		self.updateArgs()
		args = str([self.argify(arg) for arg in self.Args])
		if hasattr(self.root, 'executed'):
			exe = self.root.executed
			if exe is None:
				exe = ''
			else:
				exe += '-'
		else:
			exe = 'ex'
		id = str(self.root.ID)[19:23]
		return '{}{}-{}-{}'.format(exe, self.root.name, self.root.stepnumber, id) + args


class Condition(ElementGraph):
	""" A Literal used in causal link"""

	def __init__(self, ID=None, type_graph=None, name=None, Elements=None, root_element=None, Edges=None,
				 Restrictions=None):
		if type_graph is None:
			type_graph = 'Condition'
		if ID is None:
			ID = root_element.ID
		if root_element is None:
			root_element = Literal()
		if Elements is None:
			Elements = {root_element}
		if name is None:
			name = root_element.name

		super(Condition, self).__init__(ID, type_graph, name, Elements, root_element, Edges, Restrictions)
		self.replaced_ID = root_element.replaced_ID

	def __hash__(self):
		return hash(self.ID) ^ hash(self.root.name) ^ hash(self.root.truth) ^ hash(self.root.replaced_ID)

	@property
	def truth(self):
		return self.root.truth

	def __eq__(self, other):
		if not isinstance(other, ElementGraph):
			return False
		if self.root.name == other.root.name and self.root.truth == other.root.truth:
			if self.Args == other.Args:
				return True
		return False

	def isConsistent(self, other):
		if isinstance(other, ElementGraph):
			return self.isConsistentSubgraph(other)
		if isinstance(other, Literal):
			return self.root.isConsistent(other)

	def isOpposite(self, other):
		return self.name == other.name and self.truth != other.truth and self.Args == other.Args

	def numArgs(self):
		if not hasattr(self, 'Args'):
			self.updateArgs()
		return len([arg for arg in self.Args if arg.name is not None])

	def argify(self, arg):
		if isinstance(arg, Operator):
			return Action.subgraph(self, arg).__repr__()
		elif isinstance(arg, Literal):
			return Condition.subgraph(self, arg).__repr__()
		else:
			return arg.name

	def __repr__(self):
		self.updateArgs()
		args = str([self.argify(arg) for arg in self.Args])
		t = ''
		if not self.root.truth:
			t = 'not-'
		return '{}{}'.format(t, self.root.name) + args


class PlanElementGraph(ElementGraph):
	def __init__(self, ID=None, type_graph=None, name=None, Elements=None, plan_elm=None, Edges=None,
				 Restrictions=None):

		if ID is None:
			ID = uuid4()
		if type_graph is None:
			type_graph = 'PlanElementGraph'
		if Elements is None:
			Elements = set()
		if Edges is None:
			Edges = set()
		if Restrictions is None:
			Restrictions = set()

		self.OrderingGraph = OrderingGraph()
		self.CausalLinkGraph = CausalLinkGraph()

		self.nonequals = set()
		self.flaws = FlawLib()
		self.solved = False
		self.initial_dummy_step = None
		self.final_dummy_step = None

		if plan_elm is None:
			plan_elm = Element(ID=ID, typ=type_graph, name=name)

		super(PlanElementGraph, self).__init__(ID, type_graph, name, Elements, plan_elm, Edges, Restrictions)

	def __hash__(self):
		return hash(self.name) ^ hash(self.typ) ^ hash(self.ID)

	def __getattr__(self, name):
		if name == 'Args':
			self.updateArgs()
			return self.Args
		else:
			raise AttributeError('no attribute {}'.format(name))

	@classmethod
	def Actions_2_Plan(cls, Actions, h):
		# Used by Plannify

		if not checkHeight(Actions, h):
			return None

		elements = set().union(*[A.elements for A in Actions])
		edges = set().union(*[A.edges for A in Actions])

		arg_dict = {op: op.arg_name for op in elements if type(op) == Operator}
		inv_map = {v: k for k, v in arg_dict.items()}

		new_edges = []
		for edge in edges:
			must_replace = False
			source = edge.source
			sink = edge.sink
			if type(source) == Operator:
				source = inv_map[source.arg_name]
				must_replace = True
			if type(sink) == Operator:
				sink = inv_map[sink.arg_name]
				must_replace = True
			if must_replace:
				new_edges.append(Edge(source, sink, edge.label))
			else:
				new_edges.append(edge)
		new_elements = []
		for elm in elements:
			if type(elm) == Operator:
				new_elements.append(inv_map[elm.arg_name])
			else:
				new_elements.append(elm)

		new_ords = []
		new_links = []
		for A in Actions:
			if hasattr(A, "ground_subplan"):
				""" Recursively add elements (step-typed elements added to arg_dict) Orderings, and Causal Links"""
				for ord in A.ground_subplan.OrderingGraph.edges:
					new_ords.append(Edge(inv_map[ord.source.arg_name], inv_map[ord.sink.arg_name], ord.label))
				for link in A.ground_subplan.CausalLinkGraph.edges:
					new_links.append(Edge(inv_map[link.source.arg_name], inv_map[link.sink.arg_name], link.label))

		Plan = cls(name='Action_2_Plan', Elements=set(new_elements), Edges=set(new_edges))
		Plan.OrderingGraph.edges = set(new_ords)
		Plan.CausalLinkGraph.edges = set(new_links)

		return Plan

		# # for each pair of elements that have same arg_name, merge.
		# replaced = []
		# for u, v in itertools.product(elements, elements):
		# 	if v in replaced or u in replaced:
		# 		continue
		# 	if u.ID == v.ID:
		# 		continue
		# 	# if u == v:
		# 	# 	continue
		# 	if not u.isConsistent(v):
		# 		continue
		# 	if u.arg_name == v.arg_name:
		# 		replacer = u
		# 		original = v
		# 		if type(u) == Operator:
		# 			if u.stepnumber != -1:
		# 				replacer = v
		# 				original = u
		# 				replacer.stepnumber = u.stepnumber
		# 			else:
		# 				replacer.stepnumber = v.stepnumber
		#
		# 		outgoing_edges = [edge for edge in edges if edge.source == original]
		# 		Plan.replaceArg(original, replacer)
		# 		# u.merge(v)
		# 		for edge in outgoing_edges:
		# 			# edge.source = u
		# 			Plan.edges.remove(edge)
		# 			Plan.edges.add(Edge(replacer, edge.sink, edge.label))
		#
		# 		replaced.append(original)
		#
		# if len(Plan.Step_Graphs) != len(Actions):
		# 	raise ValueError("extra steps?")



	def UnifyActions(self, P, G):
		# Used by Plannify

		NG = G.deepcopy()

		already_added_dict = dict()

		for elm in P.elements:
			print(elm.replaced_ID)
			# first, try to get operator tokens
			e = NG.getElementById(elm.replaced_ID)
			if e is None:
				# then get other kinds
				e = NG.getElmByRID(elm.replaced_ID)
			if e is None:
				continue
				# it's as good as not here
				# we can end up here because linked-by condition is on different step
				# print("HERERER")
				# raise ValueError("cannot find elm: {}".format(elm))
			already_added_dict[e] = elm

		for edge in NG.edges:
			if edge.source not in already_added_dict.keys():
				if edge.source.replaced_ID == -1:
					edge.source.replaced_ID = edge.source.ID
				already_added_dict[edge.source] = edge.source
				self.elements.add(edge.source)
			if edge.sink not in already_added_dict.keys():
				if edge.sink.replaced_ID == -1 and not isinstance(edge.sink, Argument):
					edge.sink.replaced_ID = edge.sink.ID
				already_added_dict[edge.sink] = edge.sink
				self.elements.add(edge.sink)
			self.edges.add(Edge(already_added_dict[edge.source], already_added_dict[edge.sink], edge.label))

		return True

	def deepcopy(self):
		new_self = copy.deepcopy(self)
		new_self.ID = uuid4()
		return new_self

	def AddSubgraph(self, subgraph):
		self.elements.update(subgraph.elements)
		self.edges.update(subgraph.edges)

	def isInternallyConsistent(self):
		return self.OrderingGraph.isInternallyConsistent() and self.CausalLinkGraph.isInternallyConsistent() and \
			   super(PlanElementGraph, self).isInternallyConsistent()

	@property
	def Steps(self):
		return [element for element in self.elements if type(element) is Operator]

	@property
	def Step_Graphs(self):
		return [Action.subgraph(self, step) for step in self.Steps]

	@property
	def Root_Graphs(self):
		root_steps = []
		for s in self.Steps:
			nobodys_descendant = True
			for t in self.Steps:
				if s == t:
					continue
				if s in self.rGetDescendants(t):
					nobodys_descendant = False
					break
			if nobodys_descendant:
				root_steps.append(s)
		return [Action.subgraph(self, step) for step in root_steps]

	def __repr__(self):
		c = '\ncost {} + heuristic {}'.format(self.cost, self.heuristic)
		steps = [''.join('\t' + str(step) + '\n' for step in self.Root_Graphs)]
		order = [''.join('\t' + str(ordering.source) + ' < ' + str(ordering.sink) + '\n' for ordering in
			self.OrderingGraph.edges)]
		links = [''.join('\t' + str(cl) + '\n' for cl in self.CausalLinkGraph.edges)]
		return 'PLAN: ' + str(self.ID) + c + '\n*Steps: \n' + ''.join(['{}'.format(step) for step in steps]) + \
			   '*Orderings:\n' + \
			   ''.join(['{}'.format(o) for o in order]) + '*CausalLinks:\n' + ''.join(['{}'.format(link) for link in links]) + '}'

#@clock
def test(step, causal_link):
	for eff in step.Effects:
		if eff.isOpposite(causal_link.label):
			return True
	return False

def topoSort(plan):
	OG = copy.deepcopy(plan.OrderingGraph)
	L =[]
	S = {plan.initial_dummy_step}
	while len(S) > 0:
		n = S.pop()
		L.append(n)
		for m_edge in OG.getIncidentEdges(n):
			OG.edges.remove(m_edge)
			if len({edge for edge in OG.getParents(m_edge.sink)}) == 0:
				S.add(m_edge.sink)
	return L

def checkHeight(listActions, height):
	for a in listActions:
		if a.height == height:
			return True
	return False