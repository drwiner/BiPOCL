from Ground_Compiler_Library.PlanElementGraph import Action, PlanElementGraph, Condition
from Ground_Compiler_Library.Element import Operator
from Ground_Compiler_Library.Graph import Edge
from Flaws import Flaw

from clockdeco import clock
import copy
import itertools

@clock
def Plannify(RQ, GL, h):

	print('height: {}'.format(h))
	#An ActionLib for steps in RQ - ActionLib is a container w/ all of its possible instances as ground steps
	print('...ActionLibs')
	try:
		Libs = [ActionLib(i, copy.deepcopy(RS), GL) for i, RS in enumerate(RQ.Step_Graphs)]
	except:
		return []

	#A World is a combination of one ground-instance from each step
	Worlds = productByPosition(Libs)

	print('...Planets')
	#A Planet is a plan s.t. all steps are "arg_name consistent", but a step may not be equiv to some ground step
	Planets = [PlanElementGraph.Actions_2_Plan(W, h) for W in Worlds if isArgNameConsistent(W, RQ.Args, RQ.nonequals)]
	# Planets = []
	# for i, W in enumerate(Worlds):
	# 	if not isArgNameConsistent(W):
	# 		continue
	# 	p = PlanElementGraph.Actions_2_Plan(W,h)
	# 	if p is None:
	# 		continue
	# 	Planets.append(p)

	print("...Orderings")
	# Filter "None" planets, which exist if they did not have step at level "h", and add ReQuired orderings
	Planets = filter_and_add_orderings(Planets, RQ)

	print('...Linkify')
	# Add orderings and links, remove consistent action combinations
	Plans = Linkify(Planets, RQ, GL)

	print('...returning consistent plans')
	return [Plan for Plan in Plans if Plan is not None and Plan.isInternallyConsistent()]


def unify(gs, _map):
	if _map is False:
		return False
	# if gs.height > 0:
	# 	print('check here')

	gs_copy = gs.deepcopy()
	for key, val in _map.items():
		for elm in gs_copy.elements:
			if val == elm:
				elm.arg_name = key.arg_name
				break
	gs_copy.replaceInternals()
	gs_copy.root.stepnumber = gs.stepnumber
	gs_copy.root.height = gs.height
	gs_copy.height = gs.height
	gs_copy.is_decomp = gs.is_decomp

	return gs_copy


def isArgNameConsistent(actions, args, nonequals):

	arg_name_dict = {}

	for action in actions:
		for elm in action.elements:
			if elm.arg_name is None:
				continue
			else:
				if not elm.arg_name in arg_name_dict.keys():
					arg_name_dict[elm.arg_name] = elm
				elif not elm.isConsistent(arg_name_dict[elm.arg_name]):
					return False
				elif not arg_name_dict[elm.arg_name].isConsistent(elm):
					return False

	for u, v in nonequals:
		a, b = arg_name_dict[args[u].arg_name], arg_name_dict[args[v].arg_name]
		if a.name == b.name:
			return False

	return True

# def isArgEqCons(actions, args, nonequals):
# 	for u,v in nonequals:
# 		a, b = args[u].arg_name, args[v].arg_name



def productByPosition(Libs):
	return itertools.product(*[list(Libs[T.position]) for T in Libs])


def filter_and_add_orderings(planets, RQ):
	orderings = RQ.OrderingGraph.edges
	indices = []
	for i in range(len(planets)):
		# filter None Planets, which are scratched possible worlds
		if planets[i] is None:
			continue

		# add orderings
		if len(orderings) == 0:
			continue

		GtElm = getElementByArgName
		for ord in orderings:
			source = GtElm(planets[i], ord.source.arg_name)
			sink = GtElm(planets[i], ord.sink.arg_name)
			planets[i].OrderingGraph.addLabeledEdge(source, sink, ord.label)
			if ord.label != "<":
				continue
			source_terminals = planets[i].DecompGraph.rGetDescendants(source)
			sink_terminals = planets[i].DecompGraph.rGetDescendants(sink)
			for d_src, d_snk in itertools.product(source_terminals, sink_terminals):
				if d_src == source or d_snk == sink:
					continue
				if d_src == d_snk:
					continue
				if (d_src.typ == "step-s" and d_snk.typ != 'step-s') or (d_snk.typ == 'step-s' and d_src.typ != "step-s"):
					continue
				planets[i].OrderingGraph.addEdge(d_src, d_snk)
				# if d_snk not in source_terminals:
				# 	if d_snk.typ != 'step-s':
				# 		planets[i].OrderingGraph.addEdge(source, d_snk)
				# if d_src not in sink_terminals:
				# 	if d_src.typ != 'step-s':
				# 		planets[i].OrderingGraph.addEdge(d_src, sink)

		indices.append(i)

	return [planets[i] for i in indices]


def getElementByArgName(plan, arg_name):
	same_arg_named_elements = []
	for element in plan.elements:
		if element.arg_name == arg_name:
			same_arg_named_elements.append(element)
			return element
	# if len(same_arg_named_elements) > 1:
	# 	print('check')
	# elif len(same_arg_named_elements) == 0:
	raise ValueError("element not found")
	# return same_arg_named_elements[0]


def Linkify(Planets, RQ, GL):
	"""
	:param Planets: A list of plan-element-graphs
	:param RQ: ReQuirements
	:param GL: Ground Library
	:return: List of Plan-element-graphs which include causal link and ordering graphs
	"""

	# If there's no causal link requirements, end here.
	links = RQ.CausalLinkGraph.edges
	if len(links) == 0:
		return False

	# For each link, test if the planet supports that link
	for link in links:
		indices = []
		for i in range(len(Planets)):
			src = getElementByArgName(Planets[i], link.source.arg_name)
			snk = getElementByArgName(Planets[i], link.sink.arg_name)
			cond = getElementByArgName(Action.subgraph(Planets[i], snk), link.label.root.arg_name)
			Dependency = Condition.subgraph(Planets[i], cond)

			if src.stepnumber not in GL.ante_dict[snk.stepnumber]:
				continue

			if src.stepnumber not in GL.id_dict[cond.replaced_ID]:
				continue

			# pass token, not Dependency
			Planets[i].CausalLinkGraph.addEdge(src, snk, Dependency)
			Planets[i].OrderingGraph.addEdge(src, snk)
			indices.append(i)

		# Remove planets which cannot support link
		Planets[:] = [Planets[i] for i in indices]

	if len(Planets) == 0:
		raise ValueError('no Planet could support links in {}'.format(RQ.name))

	return Planets


class ActionLib:
	"""
	A class (list) of ground step candidates for an action graph "RS"
	"""
	def __init__(self, i, RS, GL):
		"""
		:param i: position in some list for a possible world
		:param RS: Action Graph
		:param GL: Ground Library
		"""

		#RS.root.stepnumber = stepnum
		self.position = i
		RS.root.position = i
		self.RS = RS
		self.root = RS.root
		self._cndts = []

		# for each primitive ground step in the library
		for gs in GL:
			# start with checking consistency at root as shortcut
			if not gs.root.isConsistent(self.RS.root):
				continue

			if len(self.RS.elements) == 1:
				# then it only has a root
				self.append(gs, {self.RS.root: gs.root})
				continue

			# return a set of E(RS) --> E(gs) mappings, if possible
			elm_maps = gs.findConsistentSubgraph(self.RS)
			if len(elm_maps) == 0:
				continue

			for map in elm_maps:
				self.append(gs, map)

		if len(self) == 0:
			raise ValueError('no gstep compatible with RS {}'.format(self))

	def __len__(self):
		return len(self._cndts)

	def __getitem__(self, position):
		return self._cndts[position]

	def __setitem__(self, key, value):
		self._cndts[key] = value

	def append(self, gs, map):
		gs_copy = unify(gs, map)
		self._cndts.append(gs_copy)

	@property
	def edges(self):
		return self.RS.edges

	@property
	def elements(self):
		return self.RS.elements

	def __contains__(self, item):
		return item in self._cndts

	def __repr__(self):
		return self.RS.__repr__()
