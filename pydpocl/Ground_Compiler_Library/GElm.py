from Ground_Compiler_Library.OrderingGraph import OrderingGraph, CausalLinkGraph
from Flaws import Flaw, FlawLib, TCLF
from uuid import uuid4
from Ground_Compiler_Library.Element import Argument, Element, Operator, Literal
from Ground_Compiler_Library.Graph import Edge
from Ground_Compiler_Library.ElementGraph import ElementGraph
from Ground_Compiler_Library.PlanElementGraph import Condition
import copy
import collections
from clockdeco import clock
from collections import namedtuple
# import json
# import jsonpickle
dummyTuple = namedtuple('dummyTuple', ['init', 'final'])

# class dummyTuple:
# 	def __init__(self, init, final):
# 		self.init = init
# 		self.final = final

class GStep:
	"""
	Read-Only Ground Step
	"""

	def __init__(self, operator, args, preconditions, stepnum, height):

		# READ-ONLY ATTRIBUTES #
		# schema refers to the name of the operator
		self.schema = operator
		# Args are Argument or Actor "Element" types
		self.Args = args
		# ID used as "instance ID"
		self.ID = uuid4()
		# preconds is a list of GCond
		self.preconds = preconditions
		# stepnum is the ground step constructor type
		self.stepnum = stepnum
		self.stepnumber = stepnum
		# height is 0 when primitive
		self.height = height

		if height > 0:
			self.sub_steps = []
			self.sub_orderings = OrderingGraph()
			self.sub_links = CausalLinkGraph()
			self.dummy = dummyTuple(None, None)

		# depth starts at 0 and takes on value during planning
		self.depth = 0

		self.cndts = None
		self.cndt_map = None
		self.threat_map = None
		self.threats = None
		self.cntg_mental = None

		self.instantiable = True

		# INSTANCE ATTRIBUTES #
		# risks are number of threat instances
		self.risks = list()
		self.choices = list()
		# choices are instances of cndt antecedents
		self.choice_map = dict()
		# self.num_choices = 0
		# open preconditions which need causal link
		self.open_preconds = list(self.preconds)

	# def to_json(self):
	# 	return '{}:{}, {}'
		# return json.dumps(self, default=lambda o: o.__dict__, sort_keys=True, indent=4)

	# public methods #

	# def default(self):
	# 	def default(self, obj):
	# 		if hasattr(obj, 'to_json'):
	# 			return obj.to_json()
	# 		return json.JSONEncoder.default(self, obj)

	def setup(self, step_to_cndt, precond_to_cndt, step_to_threat, precond_to_threat, cntg_mental):
		"""
		:param step_to_cndt: dict of form GStep -> GStep^k such as D[stepnum] -> [cndt antecedent step nums]
		:param precond_to_cndt: dict of form GLiteral -> GStep^k such as D[pre.ID] -> [cndt antecedent step nums]
		:param step_to_threat: dict of form GLiteral -> Gstep^k such as D[stepnum] -> [cndt threat step nums]
		"""
		self.cndts = list(step_to_cndt[self.stepnum])
		self.cndt_map = {pre.ID: list(precond_to_cndt[pre.ID]) for pre in self.preconds}
		self.threats = list(step_to_threat[self.stepnum])
		self.threat_map = {pre.ID: list(precond_to_threat[pre.ID]) for pre in self.preconds}
		self.cntg_mental = {pre.ID: list(cntg_mental[pre.ID]) for pre in self.preconds}

	def swap_setup(self, cndts, cndtmap, threats, threatmap, cntgmap):
		self.cndts = cndts
		self.cndt_map = cndtmap
		self.threats = threats
		self.threat_map = threatmap
		self.cntg_Mental = cntgmap

	def swap_substeps(self, gsteps, GL, decomp_step):
		change_dict = {step.root: gsteps[step.stepnumber].instantiate() for step in decomp_step.ground_subplan.Root_Graphs}
		self.create_composite_gstep(gsteps, decomp_step, change_dict)

		children = []
		for root_graph in decomp_step.ground_subplan.Root_Graphs:
			tree = build_tree(gsteps, GL, root_graph.root)
			children.append(tree)
		decomp_step.root.arg_name = "dis da root"
		root_dict = {"elm": decomp_step.root, "gstep": self, "children": children}

		traverse_and_prune(root_dict, {}, {})
		# print('see result')
		# change_dict = {step: gsteps[step.stepnumber].instantiate() for step in decomp_step.ground_subplan.Root_Graphs}


	def create_composite_gstep(self, gsteps, decomp_step, change_dict):
		self.sub_steps = list(change_dict.values())
		for edge in decomp_step.ground_subplan.OrderingGraph.edges:
			source = change_dict[edge.source]
			# if source.height > 0:
			# source = change_dict[edge.source].dummy[1]
			sink = change_dict[edge.sink]
			# if sink.height > 0:
			# 	sink = change_dict[edge.sink].dummy[0]
			self.sub_orderings.addLabeledEdge(source, sink, edge.label)

		for edge in decomp_step.ground_subplan.CausalLinkGraph.edges:
			new_sink = change_dict[edge.sink]
			# Condition.subgraph(subplan, edge.label)
			g_label = GLiteral(edge.label.name, edge.label.Args, edge.label.truth, -1, None)
			for p in new_sink.preconds:
				if p != g_label:
					continue
				self.sub_links.addEdge(change_dict[edge.source], new_sink, p)
				self.sub_orderings.addEdge(change_dict[edge.source], new_sink)
				new_sink.fulfill(p)
				break

		# set these babes to not be instantiable "fo' life"
		gsteps[decomp_step.sub_dummy_init.stepnumber].instantiable = False
		gsteps[decomp_step.sub_dummy_goal.stepnumber].instantiable = False
		init_step = gsteps[decomp_step.sub_dummy_init.stepnumber].instantiate()
		final_step = gsteps[decomp_step.sub_dummy_goal.stepnumber].instantiate()

		for step in self.sub_steps:
			self.sub_orderings.addEdge(init_step, step)
			self.sub_orderings.addEdge(step, final_step)
		self.sub_orderings.addEdge(init_step, final_step)

		# reconfigure init step to be top cndt for all steps and goal

		for step in self.sub_steps:
			for other_step in self.sub_steps:
				if other_step == step:
					continue
				prioritize_cndt(other_step, step)
			prioritize_cndt(init_step, step)
			prioritize_cndt(step, final_step)
		prioritize_cndt(init_step, final_step)

		# add init_step as top cndt for all

		self.dummy = dummyTuple(init_step, final_step)

	def instantiate(self, default_refresh=None, default_None_is_to_refresh_open_preconds=None):
		new_self = copy.deepcopy(self)
		new_self.ID = uuid4()
		self.choice_map = dict()

		if default_refresh is None:
			self.risks = list()
			self.choices = list()

		if default_None_is_to_refresh_open_preconds is None:
			self.open_preconds = list(self.preconds)

		return new_self

	def fulfill(self, pre):
		if self.cndt_map is None:
			raise AttributeError('Cndt Map not found; run setup(xyz) first')
		if pre.ID not in self.cndt_map:
			raise ValueError('{} not found in cndt_map, id={}'.format(pre, pre.ID))
		if pre not in self.preconds:
			raise ValueError('{} found in cndt_map w/ id={}, but {} not found in preconds'.format(pre, pre.ID, pre))
		# remove precondition from open precond
		if pre in self.open_preconds:
			self.open_preconds.remove(pre)
		else:
			print('pre: {} not found in {} to remove, allowed in some cases'.format(pre, self))

	def update_choices(self, plan):
		choices = set()
		for pre in self.open_preconds:
			choice_nums = self.cndt_map[pre.ID]
			for step in plan.steps:
				if self.ID == step.ID:
					continue
				if plan.OrderingGraph.isPath(self, step):
					continue
				if step.stepnum in choice_nums:
					choices.add(step)
		self.choices = list(choices)

	def is_cndt(self, other):
		return other.stepnum in self.cndts

	def is_threat(self, other):
		return other.stepnum in self.threats

	# private hooks #

	def __hash__(self):
		return hash(self.ID)

	def __eq__(self, other):
		return self.ID == other.ID

	def __str__(self):
		# if len(self.Args) > 0 and type(self.Args[0]) == str:
		# 	args = ""
		# else:
		# 	args = str([arg.name if not isinstance(arg, ElementGraph) else arg for arg in self.Args])
		# return str(self.schema) + args + '_{}'.format(str(self.ID)[-4:])

		return str(self.schema) + '_{}'.format(str(self.ID)[-4:])

	def __repr__(self):
		return self.__str__()


def traverse_and_prune(root_dict, visited_dict, parent_dict):

	visited_dict.update({root_dict["elm"].arg_name: root_dict["gstep"]})

	new_children = []
	reroute_dict = {}
	for child_dict in root_dict['children']:
		child_elm = child_dict["elm"]

		if child_elm.arg_name in visited_dict.keys():
			reroute_dict[child_dict["gstep"]] = child_elm.arg_name

			continue

		traverse_and_prune(child_dict, visited_dict, parent_dict)
		parent_dict[child_dict["gstep"]] = root_dict["gstep"]
		new_children.append(child_dict)

	if len(reroute_dict) > 0:
		prune(root_dict, new_children, visited_dict, reroute_dict, parent_dict)
	else:
		root_dict["gstep"].sub_steps = [child["gstep"] for child in root_dict['children']]

	return root_dict


def prune(root_dict, new_children, visited_dict, reroute_dict, parent_dict):
	root_gstep = root_dict["gstep"]
	new_substeps = [child["gstep"] for child in new_children]
	root_gstep.sub_steps = new_substeps

	old_orderings = list(root_gstep.sub_orderings.edges)
	root_gstep.sub_orderings.edges = set()
	for edge in old_orderings:

		source_elm = reroute_dict[edge.source]
		source = visited_dict[source_elm]
		sink_elm = reroute_dict[edge.sink]
		sink = visited_dict[sink_elm]

		parent = parent_dict[source]
		if parent != parent_dict[sink]:
			raise ValueError("check this")
		parent.sub_orderings.addLabeledEdge(source, sink, edge.label)

	old_links = list(root_gstep.sub_links.edges)
	root_gstep.sub_links.edges = set()
	for edge in old_links:

		source_elm = reroute_dict[edge.source]
		source = visited_dict[source_elm]
		sink_elm = reroute_dict[edge.sink]
		sink = visited_dict[sink_elm]

		parent = parent_dict[source]
		if parent != parent_dict[sink]:
			raise ValueError("check this")

		g_label = GLiteral(edge.label.name, edge.label.Args, edge.label.truth, -1, None)
		for p in sink.preconds:
			if p != g_label:
				continue
			parent.sub_links.addEdge(source, sink, p)
			parent.sub_orderings.addEdge(source, sink)
			sink.fulfill(p)
			break

		# root_gstep.sub_links.edges.add(Edge(source, sink, edge.label))


def build_tree(gsteps, GL, root):

	root_gstep = gsteps[root.stepnumber].instantiate()
	if root_gstep.height == 0:
		return {"elm": root, "children": [], "gstep": root_gstep}

	children_dict = {child.root: build_tree(gsteps, GL, child.root) for child in GL[root.stepnumber].ground_subplan.Root_Graphs}

	children = list(children_dict.values())

	root_gstep.sub_orderings.edges = set()
	for ordering in GL[root.stepnumber].ground_subplan.OrderingGraph.edges:
		source = children_dict[ordering.source]['gstep']
		sink = children_dict[ordering.sink]['gstep']
		root_gstep.sub_orderings.addLabeledEdge(source, sink, ordering.label)

	root_gstep.sub_links.edges = set()
	for edge in GL[root.stepnumber].ground_subplan.CausalLinkGraph.edges:
		source = children_dict[edge.source]['gstep']
		sink = children_dict[edge.sink]['gstep']

		g_label = GLiteral(edge.label.name, edge.label.Args, edge.label.truth, -1, None)
		for p in sink.preconds:
			if p != g_label:
				continue
			root_gstep.sub_links.addEdge(source, sink, p)
			root_gstep.sub_orderings.addEdge(source, sink)
			sink.fulfill(p)
			break


	return {"elm": root, "children": children, "gstep": root_gstep}


class GLiteral:
	"""
	A READ-ONLY Ground Literal / Condition
	"""
	def __init__(self, pred_name, arg_tup, trudom, _id, is_static):
		self.name = pred_name
		self.Args = list(arg_tup)
		self.truth = trudom
		self.ID = _id
		self.is_static = is_static

	def instantiate(self):
		return copy.deepcopy(self)

	# def to_json(self):
	# 	return json.dumps(self, default=lambda o: o.__dict__, sort_keys=True, indent=4)
	# 	# return 'u{name}: {}}'
	#
	# def from_json(self):
	# 	pass

	def __hash__(self):
		return hash(self.ID)

	def __len__(self):
		return len(self.Args)

	def __eq__(self, other):
		if not isinstance(other, GLiteral):
			return False
		return self.name == other.name and self.Args == other.Args and self.truth == other.truth

	def __repr__(self):
		# args = str([arg if not isinstance(arg, Argument) else arg.name for arg in self.Args])
		#args = str([arg.name if not isinstance(arg, Action) else arg for arg in self.Args])
		t = ''
		if not self.truth:
			t = 'not-'
		if self.truth is None:
			t = "(-)"
		return '{}{}'.format(t, self.name)


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


def prioritize_cndt(cndt, whose):
	if cndt.stepnum in whose.cndts:
		whose.cndts.remove(cndt.stepnum)
		whose.cndts.insert(0, cndt.stepnum)
		for pre in whose.preconds:
			if cndt.stepnum not in whose.cndt_map[pre.ID]:
				continue
			whose.cndt_map[pre.ID].remove(cndt.stepnum)
			whose.cndt_map[pre.ID].insert(0, cndt.stepnum)