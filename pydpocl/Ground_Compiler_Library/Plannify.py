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
	# Planets = [PlanElementGraph.Actions_2_Plan(W, h) for W in Worlds if isArgNameConsistent(W)]
	Planets = []
	for i, W in enumerate(Worlds):
		if not isArgNameConsistent(W):
			continue
		# if len(W) != len(RQ.Root_Graphs):
		# 	continue
		# if i > 1055:
		# 	print('here')
		p = PlanElementGraph.Actions_2_Plan(W,h)
		if p is None:
			continue
		Planets.append(p)
		# break

	print('...Linkify')
	#Linkify installs orderings and causal links from RQ/decomp to Planets, rmvs Planets which cannot support links
	has_links = Linkify(Planets, RQ, GL)

	print('...Groundify')
	#Groundify is the process of replacing partial steps with its ground step, and removing inconsistent planets
	Plans = Groundify(Planets, GL, has_links)

	print('...returning consistent plans')
	return [Plan for Plan in Plans if Plan is not None and Plan.isInternallyConsistent()]


def partialUnify(PS, _map):
	if _map is False:
		return False
#	NS = PS.deepcopy()
	NS = copy.deepcopy(PS)
	effects = [edge.sink for edge in NS.edges if edge.label == 'effect-of' and edge.source == NS.root]
	for elm in effects:
		if elm in _map:
			g_elm = _map[elm]
			elm.merge(g_elm)
			elm.replaced_ID = g_elm.replaced_ID

	NSE = list(NS.elements)
	for elm in NSE:
		if elm in _map:
			g_elm = _map[elm]
			elm.merge(g_elm)
			elm.replaced_ID = g_elm.replaced_ID
			if elm.replaced_ID == -1:
				# this is an object/constant
				ge = copy.deepcopy(g_elm)
				ge.replaced_ID = ge.ID
				ge.arg_name = elm.arg_name
				NS.assign(elm, ge)
				#elm.replaced_ID = g_elm.ID
				#elm.ID = g_elm.ID
	# NS.root.stepnumber = PS.root.stepnumber
	NS.height = PS.height
	NS.root.height = PS.root.height
	NS.updateArgs()
	return NS


def isArgNameConsistent(Partially_Ground_Steps):

	arg_name_dict = {}

	for PGS in Partially_Ground_Steps:
		for elm in PGS.elements:
			if elm.arg_name is None:
				continue
			else:
				if not elm.arg_name in arg_name_dict.keys():
					arg_name_dict[elm.arg_name] = elm
				elif not elm.isConsistent(arg_name_dict[elm.arg_name]):
					return False
				elif not arg_name_dict[elm.arg_name].isConsistent(elm):
					return False
	return True


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
		if len(orderings) > 0:
			GtElm = planets[i].getElementById
			planets[i].OrderingGraph.edges = {Edge(GtElm(ord.source.ID), GtElm(ord.sink.ID), ord.label) for ord in orderings}

		indices.append(i)

	planets[:] = [planets[i] for i in indices]


def Linkify(Planets, RQ, GL):
	"""
	:param Planets: A list of plan-element-graphs
	:param RQ: ReQuirements
	:param GL: Ground Library
	:return: List of Plan-element-graphs which include causal link and ordering graphs
	"""
	# Filter "None" planets, which exist if they did not have step at level "h", and add ReQuired orderings
	filter_and_add_orderings(Planets, RQ)

	# If there's no causal link requirements, end here.
	links = RQ.CausalLinkGraph.edges
	if len(links) == 0:
		return False

	# For each link, test if the planet supports that link
	for link in links:
		indices = []
		for i in range(len(Planets)):

			src = Planets[i].getElementById(link.source.ID)
			snk = Planets[i].getElementById(link.sink.ID)
			# This condition could be a blank element literal
			cond = Planets[i].getElementById(link.label.ID)

			Dependency = Condition.subgraph(Planets[i], cond)
			# if cond is None:
			# 	cond = RQ.getElementById(link.label.ID)

			# use the step numbers in order to reason about "ground steps" not these partial shits.
			# ante_dict == cndt_dict
			if src.stepnumber not in GL.ante_dict[snk.stepnumber]:
				continue

			if not GL.hasConsistentPrecondition(GL[snk.stepnumber], Dependency, src.stepnumber):
				continue
			# pass token, not Dependency
			Planets[i].CausalLinkGraph.addEdge(src, snk, Dependency)
			Planets[i].OrderingGraph.addEdge(src, snk)
			indices.append(i)

		# Remove planets which cannot support link
		Planets[:] = [Planets[i] for i in indices]

	if len(Planets) == 0:
		raise ValueError('no Planet could support links in {}'.format(RQ.name))

	return True


def Groundify(Planets, GL, has_links):
	print('...Groundify - Unifying Actions with GL')
	for i, Planet in enumerate(Planets):
		print("... Planet {}".format(i))
		for Step in Planet.Root_Graphs:
			print('... Unifying {} with {}'.format(Step, GL[Step.stepnumber]))
			# Unify Actions (1) swaps step graphs with ground step
			Planet.UnifyActions(Step, GL[Step.stepnumber])

	if not has_links:
		return Planets

	print('...Groundify - Creating Causal Links')
	Discovered_Planets = []

	for Plan in Planets:
		nested_links = []
		for link in Plan.CausalLinkGraph.edges:
			pre_tokens = GL.getConsistentPreconditions(GL[link.sink.stepnumber], link.label, link.source.stepnumber)
			link_alternatives = []
			for token in pre_tokens:
				_link = Edge(link.source, link.sink, token)
				link_alternatives.append(_link)
			nested_links.append(link_alternatives)

		# link_worlds = productByPosition(nested_links)
		link_worlds = itertools.product(*nested_links)

		for links in link_worlds:
			FPlan = Plan.deepcopy()
			FPlan.CausalLinkGraph.edges = set(links)
			Discovered_Planets.append(FPlan)

	return Discovered_Planets


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
				RS_copy = copy.deepcopy(self.RS)
				RS_copy.root.merge(gs.root)
				RS_copy.root.replaced_ID = gs.root.replaced_ID
				self.append(RS_copy, gs)
				continue
			# if
			# return a set of E(RS) --> E(gs) mappings, if possible
			elm_maps = gs.findConsistentSubgraph(self.RS)
			if len(elm_maps) == 0:
				continue
			""" for each map, we're going to unify JUST THOSE elements in the mapping
			 (for instance, an "operator element" might not yet be assigned a particular schema)
			 We don't just swap completely because we must respect global bindings for this world """
			for map in elm_maps:
				if len(map) == 0:
					RS_copy = copy.deepcopy(self.RS)
					RS_copy.root.merge(gs.root)
					RS_copy.root.replaced_ID = gs.root.replaced_ID
					self.append(partialUnify(RS_copy, map), gs)
				else:
					self.append(partialUnify(self.RS, map), gs)
		if len(self) == 0:
			raise ValueError('no gstep compatible with RS {}'.format(self))

	def __len__(self):
		return len(self._cndts)

	def __getitem__(self, position):
		return self._cndts[position]

	def __setitem__(self, key, value):
		self._cndts[key] = value

	def append(self, item, gs):
		item.root.stepnumber = gs.stepnumber
		item.root.height = gs.height
		item.height = gs.height
		item.is_decomp = gs.is_decomp
		self._cndts.append(item)

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
