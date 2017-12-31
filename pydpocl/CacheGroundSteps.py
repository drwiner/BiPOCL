
import itertools
import copy
import pickle
from collections import namedtuple, defaultdict
from Ground_Compiler_Library.PlanElementGraph import Condition, Action
from clockdeco import clock
from Ground_Compiler_Library.Plannify import Plannify
from Ground_Compiler_Library.Element import Argument, Actor, Operator, Literal
from build_action_graph import parseDomAndProb
from Ground_Compiler_Library.Graph import Edge
from Flaws import FlawLib
import hashlib


def cache_ground_steps(operators, objects, obtypes, stepnum=None, gsd=None):

	if stepnum is None:
		stepnum = 0
	gsteps = []
	print('...Creating Primitive Ground Steps')
	for op in operators:
		op.updateArgs()
		cndts = [[obj for obj in objects if arg.typ == obj.typ or arg.typ in obtypes[obj.typ]] for arg in op.Args]
		tuples = itertools.product(*cndts)
		for t in tuples:

			# check for inconsistent tuple of arg types
			legaltuple = True
			for (u,v) in op.nonequals:
				if t[u] == t[v]:
					legaltuple = False
					break
			if not legaltuple:
				continue

			gstep = copy.deepcopy(op)
			gstep.replaceArgs(t)
			if gsd is not None:
				handle_step_typed_arg(gstep, gsd)
			# replace the ID of the internal elements
			gstep._replaceInternals()
			# replacing these coordinates changes
			gstep.replaceInternals()
			# assign the step number (only one of the following should be necessary)
			gstep.root.stepnumber = stepnum
			gstep.root.arg_name = stepnum
			stepnum += 1
			# append the step to our growin glist
			gsteps.append(gstep)
			print('Creating ground step {}'.format(gstep))
			# assign height of the step to the root element and
			gstep.height = 0
			gstep.root.height = 0

	return gsteps


def handle_step_typed_arg(gstep, gsd):
	for arg in gstep.Args:
		if not hasattr(arg, 'stepnumber'):
			continue
		step = gsd[arg.stepnumber]
		""" possibly can just replaceArg and add elements without making copy... since everything will
			get cloned anyway.
		"""
		# clone, but don't replace IDs because this isn't a new step, it's an existing step
		arg_clone = step.deepcopy(replace_internals=True)
		# arg_clone.root.replaced_ID = arg.ID
		arg_clone.root.replaced_ID = arg.replaced_ID
		# swap argument with step root clone
		gstep.replaceArg(arg, arg_clone.root)
		# add elements and edges to gstep graph
		gstep.elements.update(arg_clone.elements)
		gstep.edges.update(arg_clone.edges)


def groundDecompStepList(doperators, GL, stepnum=0, height=0):
	gsteps = []

	print('...Creating Ground Decomp Steps')
	for op in doperators:
		# renaming all arg_names in order to make sure they're unique
		op_template = copy.deepcopy(op)
		for arg in op_template.subplan.Args:
			if arg.arg_name is None:
				arg.arg_name = str(arg.ID)[19: 23]
			else:
				arg.arg_name = str(arg.ID)[19: 23] + arg.arg_name

		for elm in op_template.elements:
			if elm.arg_name is None:
				elm.arg_name = str(elm.ID)[19: 23]
			else:
				elm.arg_name = str(elm.ID)[19: 23] + elm.arg_name

		print('processing operator: {}'.format(op))
		try:
			sub_plans = Plannify(op_template.subplan, GL, height)
		except:
			continue

		print("num_subplans: " + str(len(sub_plans)))
		for i, sp in enumerate(sub_plans):
			print(i)
			GDO = op_template.deepcopy()
			GDO.is_decomp = True

			print("rewrite Elms")
			# rewrites operator arguments based on groundings of sub-plan, provides alternatives
			gdo, perm_list = rewriteElms(GDO, sp, GL.objects, GL.object_types, height + 1)
			if not gdo:
				continue
			# arguments were not in sub-plan, and need to be substituted for every combination
			if perm_list is not None:
				gdo_list = permutate_subs(gdo, GL.objects, GL.object_types, perm_list)
				for item in gdo_list:
					ground_composite_step = prep_singleton(GL, item, sp, height)
					stepnum = append_composite_step(gsteps, ground_composite_step, stepnum)
			# all arguments were grounded as part of plannify
			else:
				ground_composite_step = prep_singleton(GL, gdo, sp, height)
				stepnum = append_composite_step(gsteps, ground_composite_step, stepnum)

	return gsteps


def append_composite_step(gsteps, ground_composite_step, stepnum):

	gsteps.append(ground_composite_step.sub_dummy_init)
	gsteps.append(ground_composite_step.sub_dummy_goal)
	gsteps.append(ground_composite_step)

	# ground_composite_step.stepnumber = step num
	ground_composite_step.sub_dummy_init.root.stepnumber = stepnum
	# ground_composite_step.sub_dummy_init.stepnumber = stepnum+ 1
	ground_composite_step.sub_dummy_goal.root.stepnumber = stepnum + 1
	# ground_composite_step.sub_dummy_goal.stepnumber = stepnum+ 2

	ground_composite_step.root.stepnumber = stepnum + 2
	stepnum += 3
	return stepnum

def distinguished_steps(GL, gdo, height):

	dummy_init = Action(name='begin:' + str(gdo.name))
	dummy_init.has_cndt = False

	for condition in gdo.Preconditions:
		dummy_init.edges.add(Edge(dummy_init.root, condition.root, 'effect-of'))
		dummy_init.edges.update(condition.edges)
		dummy_init.elements.update(condition.elements)

	dummy_goal = Action(name='finish:' + str(gdo.name))
	dummy_goal.is_cndt = False

	for condition in gdo.Effects:
		if not GL.check_has_effect(condition, height + 1):
			# this is a pattern effect.
			continue
		dummy_goal.edges.add(Edge(dummy_goal.root, condition.root, 'precond-of'))
		dummy_goal.edges.update(condition.edges)
		dummy_goal.elements.update(condition.elements)

	gdo.sub_dummy_init = dummy_init
	gdo.sub_dummy_goal = dummy_goal


# @clock
def rewriteElms(GDO, sp, objects, obtypes, h):

	sp_arg_dict = {elm.arg_name: elm for elm in sp.elements}
	needs_substituting = []
	print(GDO)
	for i, arg in enumerate(GDO.Args):
		print("arg: " + str(arg))
		# if this arg isn't part of sub-plan (is that possible?)
		if arg.arg_name not in sp_arg_dict.keys():
			if arg.name is None:
				needs_substituting.append(i)
				continue
			# raise ValueError("just checking if this is possible")
		sp_elm = sp_arg_dict[arg.arg_name]
		print("suplan elm: " + str(sp_elm))
		if type(sp_elm) == Operator:
			A = Action.subgraph(sp, sp_elm)
			GDO.replaceArg(arg, A.root)
			# GDO.elements.remove(arg)
			GDO.elements.update(A.elements)
			GDO.edges.update(A.edges)
		elif type(sp_elm) == Literal:
			C = Condition.subgraph(sp, sp_elm)
			GDO.replaceArg(arg, C.root)
			# GDO.elements.remove(arg)
			GDO.elements.update(C.elements)
			GDO.edges.update(C.edges)
		else:
			# this is an object that should be substituted
			GDO.replaceArg(arg, sp_elm)
	print('almost out')
	GDO.updateArgs()
	for (u,v) in GDO.nonequals:
		if GDO.Args[u] == GDO.Args[v]:
			return False, None

	if len(needs_substituting) == 0:
		return GDO, None

	return GDO, needs_substituting


def permutate_subs(GDO, objects, obtypes, needs_substituting):
	#NOTE: does not _yet_ handle step-typed args that need substituting the way primitve steps are handled
	perm_list = []

	cndts = [
		[obj for obj in objects if arg.typ == obj.typ or arg.typ in obtypes[obj.typ]]
		if i in needs_substituting else
		[GDO.Args[i]] for i, arg in enumerate(GDO.Args)]

	tuples = itertools.product(*cndts)
	for t in tuples:
		legal_tuple = True
		for (u, v) in GDO.nonequals:
			if t[u] == t[v]:
				legal_tuple = False
				break
		if not legal_tuple:
			continue

		gstep = GDO.deepcopy()
		gstep.replaceArgs(t)
		perm_list.append(gstep)

	return perm_list


def prep_singleton(GL, gdo, sp, height):
	gdo.root.is_decomp = True
	print('_replacing internals')
	# swap constructor IDs and replaced_IDs
	"""
	some bad practice about to happen here: replaced_ID is not changed for operators; what's important is that they changed for preconditions and effects. replaced_IDs are then used to track down the operator tokens in the subplan (sp). the regular IDs are changed, and waiting until after they're changed affects the dictionary key hash.
	"""
	gdo._replaceInternals()
	print('replacing internals')
	# gdo.replaceInternals()

	print('init and dummy')
	# Now create dummy init step and goal step

	distinguished_steps(GL, gdo, height)
	sp_copy = copy.deepcopy(sp)
	# for elm in gdo.elements:
	# 	if not isinstance(elm, Operator):
	# 		continue
	# 	elm_in_sp = sp_copy.getElmByRID(elm.replaced_ID)
	# 	if elm_in_sp is None:
	# 		continue
	# 	elm_in_sp.ID = elm.ID
	# sp.elements = set(list(sp_copy.elements))
	# sp.edges = set(list(sp_copy.edges))

	gdo.ground_subplan = sp_copy
	# gdo.stepnumber = stepnum
	gdo.ground_subplan.root = gdo.root
	gdo.height = height + 1
	gdo.root.height = height + 1

	return gdo


import re
@clock
def upload(GL, name):
	# n = re.sub('[^A-Za-z0-9]+', '', name)
	print(name)
	with open(name, 'wb') as afile:
		pickle.dump(GL, afile)

@clock
def reload(name):
	n = re.sub('[^A-Za-z0-9]+', '', name)
	afile = open(n, "rb")
	GL = pickle.load(afile)
	afile.close()
	FlawLib.non_static_preds = GL.non_static_preds

	return GL

ALU_TERMS = ["obs-seg-alu", "obs-alu", "bel-seg-alu", "bel-alu"]


class GLib:

	def __init__(self, prim_ops, comp_ops, objects, obtypes, init_action, goal_action):
		self.non_static_preds = FlawLib.non_static_preds
		self.object_types = obtypes
		self.objects = objects

		# primitive fabula steps
		prim_fab_operators = [op for op in prim_ops if op.root.typ == "step-s"]
		self.fab_steps = cache_ground_steps(prim_fab_operators, self.objects, obtypes)

		# camera steps
		cam_operators = [op for op in prim_ops if op.root.typ == "step-c"]
		ground_objects = objects + [fab.root for fab in self.fab_steps]
		gstep_dict = {fab.stepnumber: fab for fab in self.fab_steps}
		self.cam_steps = cache_ground_steps(cam_operators, ground_objects, obtypes, self.fab_steps[-1].stepnumber+1, gstep_dict)
		# group these into sets based on only whether the preconditions and effects are different

		# axioms? need axioms such as if you believe all preconditions of a step s then you (bel (preconds s))

		self._gsteps = self.fab_steps + self.cam_steps

		self.ante_dict = defaultdict(set)
		self.threat_dict = defaultdict(set)
		self.flaw_threat_dict = defaultdict(set)
		self.id_dict = defaultdict(set)
		self.eff_dict = defaultdict(set)
		self.cntg_mental = defaultdict(set)

		print('...Creating PlanGraph base level')
		self.loadAll()

		for i in range(4):
			print('...Creating PlanGraph decompositional level {}'.format(i+1))
			try:
				D = groundDecompStepList(comp_ops, self, stepnum=len(self._gsteps), height=i)
			except:
				break
			if not D or len(D) == 0:
				break
			self.loadPartition(D)

		init_action.root.stepnumber = len(self._gsteps)
		# replacing internal replaced_IDs
		init_action._replaceInternals()
		# replace IDs
		init_action.replaceInternals()
		init_action.instantiable = False

		goal_action.root.stepnumber = len(self._gsteps) + 1
		# replace internal replaced_IDs
		goal_action._replaceInternals()
		# replace IDs
		goal_action.replaceInternals()
		goal_action.reusable = False

		# check if init and goal have potential causal relationships
		self.loadPartition([init_action, goal_action])

		print('{} ground steps created'.format(len(self)))
		# print('uploading')
		# d_name = domain.split('/')[1].split('.')[0]
		# p_name = problem.split('/')[1].split('.')[0]
		# self.name = d_name + '.' + p_name

	def loadAll(self):
		self.load(self._gsteps, self._gsteps)

	def loadPartition(self, particles):
		#print('... for each decompositional operator ')
		self.load(particles, self._gsteps)
		self.load(self._gsteps, particles)
		self.load(particles, particles)
		self._gsteps.extend(particles)

	@clock
	def load(self, antecedents, consequents):
		for ante in antecedents:
			# steps which have no preconditions needn't have any candidates
			if not ante.has_cndt:
				continue
			for pre in ante.Preconditions:
				print('... Processing antecedents for {} \t\tof step {}'.format(pre, ante))
				self._loadAntecedentPerConsequent(consequents, ante, pre)

	# @clock
	def _loadAntecedentPerConsequent(self, antecedents, _step, _pre):
		for gstep in antecedents:
			# skip steps which cannever be a candidate (such as goal)
			if not gstep.is_cndt:
				continue
			if self._parseEffects(gstep, _step, _pre) > 0:
				self.ante_dict[_step.stepnumber].add(gstep.stepnumber)

	# @clock
	def _parseEffects(self, gstep, _step, _pre):
		count = 0
		pre_name = _pre.name
		if pre_name in ALU_TERMS:
			pre_name = pre_name[:-4]
		for Eff in gstep.Effects:

			if Eff.name != pre_name:
				continue
			if len(Eff.Args) != len(_pre.Args):
				continue
			if not is_equal_args(Eff.Args, _pre.Args, gstep, _step):
				continue
			if Eff.truth != _pre.truth:
				self.threat_dict[_step.stepnumber].add(gstep.stepnumber)
				self.flaw_threat_dict[_pre.replaced_ID].add(gstep.stepnumber)
			else:
				self.eff_dict[_pre.replaced_ID].add(Eff.replaced_ID)
				self.id_dict[_pre.replaced_ID].add(gstep.stepnumber)
				if _pre.name in ALU_TERMS:
					self.cntg_mental[_pre.replaced_ID].add(gstep.stepnumber)

				count += 1
		return count

	def check_has_effect(self, condition, height):
		pre_name = condition.name
		if pre_name in ALU_TERMS:
			pre_name = pre_name[:-4]

		for gstep in self:
			if gstep.height < height:
				continue
			for Eff in gstep.Effects:

				if Eff.name != pre_name.name:
					continue
				if len(Eff.Args) != len(condition.Args):
					continue
				if Eff.truth != condition.truth:
					continue
				if not is_equal_args(Eff.Args, condition.Args, gstep, condition):
					continue
				return True
		return False

	# def getPotentialLinkConditions(self, src, snk):
	# 	cndts = []
	# 	for pre in self[snk.stepnumber].preconditions:
	# 		if src.stepnumber not in self.id_dict[pre.replaced_ID]:
	# 			continue
	# 		cndts.append(Edge(src,snk, copy.deepcopy(pre)))
	# 	return cndts

	def getPotentialEffectLinkConditions(self, src, snk):
		"""
		Given source and sink steps, return {eff(src) \cap pre(snk)}
		But, let those conditions be those of the src.
		"""
		cndts = []
		for eff in self[src.stepnumber].effects:
			for pre in self[snk.stepnumber].preconditions:
				if eff.replaced_ID not in self.id_dict[pre.replaced_ID]:
					continue
				cndts.append(Edge(src, snk, copy.deepcopy(eff)))

		return cndts

	# not currently used, would need to consider cntg-mental
	def getConsistentEffect(self, S_Old, precondition):
		effect_token = None
		for eff in S_Old.effects:
			if eff.replaced_ID in self.eff_dict[precondition.replaced_ID] or \
					self.eff_dict[eff.replaced_ID] == self.eff_dict[precondition.replaced_ID]:
				effect_token = eff
				break
		if effect_token is None:
			raise AttributeError('story_GL.eff_dict empty but id_dict has antecedent')
		return effect_token

	def getConsistentPreconditions(self, Source, Sink, Effect):

		consistent_effects = []
		for Eff in Source.Effects:
			if Eff.name != Effect.name:
				continue
			if not Eff.root.isConsistent(Effect.root) or not Effect.root.isConsistent(Eff.root):
				continue
			if is_consistent_args(Eff.Args, Effect.Args, Eff, Effect):
				consistent_effects.append(Eff.replaced_ID)

		if len(consistent_effects) == 0:
			return False

		consistent_dependencies = [Pre for eff_rid in consistent_effects
		                            for Pre in Sink.Preconditions
		                           if eff_rid in self.eff_dict[Pre.root.replaced_ID]]
		# for Pre in Sink.Preconditions:
		# 	for eff_rid in consistent_effects:
		# 		if eff_rid in self.eff_dict[Pre.root.replaced_ID]:
		# 			consistent_dependencies.append(eff_rid)
		return consistent_dependencies

	def hasConsistentPrecondition(self, SinkNum, Effect):
		# consistent_effects = []
		# for Eff in Source.Effects:
		# 	if Eff.name != Effect.name:
		# 		continue
		# 	if not Eff.root.isConsistent(Effect.root) or not Effect.root.isConsistent(Eff.root):
		# 		continue
		# 	if is_consistent_args(Eff.Args, Effect.Args, Eff, Effect):
		# 		consistent_effects.append(Eff.replaced_ID)
		#
		# if len(consistent_effects) == 0:
		# 	return False

		for Pre in self[SinkNum].Preconditions:
			if Effect.replaced_ID in self.eff_dict[Pre.root.replaced_ID]:
				# if eff_rid in self.eff_dict[Pre.root.replaced_ID]:
				return True
		return False

	def getConsistentPrecondition(self, Sink, effect):
		pre_token = None
		for pre in Sink.preconditions:
			if effect.replaced_ID in self.eff_dict[pre.replaced_ID]:
				pre_token = pre
				break
		if pre_token is None:
			raise AttributeError('effect {} not in story_GL.eff_Dict for Sink {}'.format(effect, Sink))
		return pre_token

	def __len__(self):
		return len(self._gsteps)

	def __getitem__(self, position):
		return self._gsteps[position]

	def __contains__(self, item):
		return item in self._gsteps

	def __repr__(self):
		return 'Grounded Step Library: \n' +  str([step.__repr__() for step in self._gsteps])


def is_equal_args(a_list, b_list, agraph, bgraph):
	for a, b in zip(a_list, b_list):
		if not (a.isConsistent(b) and b.isConsistent(a)):
			return False
		if isinstance(a, Argument):
			if a.name != b.name:
				return False
		elif isinstance(a, Operator):
			if a.stepnumber != b.stepnumber:
				return False
		elif isinstance(a, Literal):
			if a.name != b.name:
				return False
			if a.truth != b.truth:
				return False
			a_cond = Condition.subgraph(agraph, a)
			b_cond = Condition.subgraph(bgraph, b)
			if not is_equal_args(a_cond.Args,b_cond.Args, a_cond, b_cond):
				return False
	return True


def is_consistent_args(a_list, b_list, agraph, bgraph):
	for a, b in zip(a_list, b_list):
		if not (a.isConsistent(b) and b.isConsistent(a)):
			return False
		if isinstance(a, Literal):
			a_cond = Condition.subgraph(agraph, a)
			b_cond = Condition.subgraph(bgraph, b)
			if not is_equal_args(a_cond.Args, b_cond.Args, a_cond, b_cond):
				return False
	return True


def load_from_pickle(pickle_name):
	ground_steps = []
	i = 0
	while True:
		try:
			print(i)
			with open(pickle_name + str(i), 'rb') as ugly:
				ground_steps.append(pickle.load(ugly))
			i += 1
			if ground_steps[-1].schema == "dummy_goal":
				break

		except:
			break
	return ground_steps


def create_pickles(pickle_name):
	operators, decomps, objects, object_types, initAction, goalAction = parseDomAndProb(domain_file, problem_file)

	print("creating ground actions......\n")
	GL = GLib(operators, decomps, objects, object_types, initAction, goalAction)


	ground_step_list = precompile.deelementize_ground_library(GL)
	for i, gstep in enumerate(ground_step_list):
		with open(pickle_name + str(i), 'wb') as ugly:
			try:
				pickle.dump(gstep, ugly)
			except:
				print('where?')

	return ground_step_list


# def append_cache(pickle_name):

def view(condition, literal):
	c = Condition.subgraph(condition, literal)
	print(c)
	for arg in c.Args:
		if type(arg) == Literal:
			view(condition, arg)
		else:
			print(arg)


def plan_single_example(domain_file, problem_file):
	d_name = domain_file.split('/')[-1].split('.')[0]
	p_name = problem_file.split('/')[-1].split('.')[0]
	uploadable_pickle_name = d_name + '.' + p_name
	pname = "pickles/" + uploadable_pickle_name + "_"
	gsteps = load_from_pickle(pname)
	planner = GPlanner(gsteps)
	planner.solve(k=1)

def run_single_example(domain_file, problem_file, run_planner=None):

	# domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_VirtualCam.pddl'
	# problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_VirtualCam_Problem.pddl'
	d_name = domain_file.split('/')[-1].split('.')[0]
	p_name = problem_file.split('/')[-1].split('.')[0]
	uploadable_pickle_name = d_name + '.' + p_name

	pname = "pickles/" + uploadable_pickle_name + "_"

	# gsteps = load_from_pickle(pname)
	gsteps = create_pickles(pname)
	print('test')

	with open('gs_' + uploadable_pickle_name, 'w') as gs:
		# gs.write('\n\n')
		for i, step in enumerate(gsteps):
			gs.write('\n')
			gs.write(str(i) + '\n')
			gs.write(str(step))
			gs.write('\n\tpreconditions:')
			for pre in step.preconds:
				gs.write('\n\t\t' + str(pre))
				if step.cndt_map is not None:
					if pre.ID in step.cndt_map.keys():
						gs.write('\n\t\t\tcndts:\t{}'.format(str(step.cndt_map[pre.ID])))
				if step.threat_map is not None:
					if pre.ID in step.threat_map.keys():
						gs.write('\n\t\t\trisks:\t{}'.format(str(step.threat_map[pre.ID])))
				if step.cntg_mental is not None:
					if pre.ID in step.cntg_mental.keys():
						gs.write("\n\t\t\tcntg-mental:\t{}".format(str(step.cntg_mental[pre.ID])))

			if step.height > 0:
				gs.write('\n\tsub_steps:')
				for sub in step.sub_steps:
					gs.write('\n\t\t{}'.format(str(sub)))
				gs.write('\n\tsub_orderings:')
				for ord in step.sub_orderings.edges:
					gs.write('\n\t\t{}'.format(str(ord.source) + ' < ' + str(ord.sink)))
				gs.write('\n\tsub_links:')
				for link in step.sub_links.edges:
					gs.write('\n\t\t{}'.format(str(link)))
			gs.write('\n\n')

	planner = GPlanner(gsteps)

	if run_planner is not None:
		planner.solve(k=1)



def run_all_tests():

	domain_file_template = "D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/{}_Domain_{}{}.pddl"
	problem_file_template = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/{}_{}_Problem{}.pddl'

	# simple domain (_2)
	df = domain_file_template.format("Unity", "Simple", "_2")
	pf = problem_file_template.format("Unity", "Simple", "_2")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "Simple", "_3")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "Simple", "_4")
	run_single_example(df, pf)

	# virtual cam domain
	df = domain_file_template.format("Unity", "VirtualCam", "")
	pf = problem_file_template.format("Unity", "VirtualCam", "")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "VirtualCam", "_2")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "VirtualCam", "_3")
	run_single_example(df, pf)

	# virtual cam domain (composite steps with height 2)
	df = domain_file_template.format("Unity", "VirtualCam", "2")
	pf = problem_file_template.format("Unity", "VirtualCam", "")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "VirtualCam", "_2")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "VirtualCam", "_3")
	run_single_example(df, pf)

	# virtual cam domain (composite steps with height 2, 2 sub-steps, and links)
	df = domain_file_template.format("Unity", "VirtualCam", "3")
	pf = problem_file_template.format("Unity", "VirtualCam", "")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "VirtualCam", "_2")
	run_single_example(df, pf)
	pf = problem_file_template.format("Unity", "VirtualCam", "_3")
	run_single_example(df, pf)

if __name__ ==  '__main__':
	# domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_VirtualCam3.pddl'
	# problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_VirtualCam_Problem_2.pddl'
	# problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_InitialStateTest_Problem.pddl'
	# domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_Match2_2.pddl'
	domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_ContAct2.pddl'
	problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Cntg_Problem.pddl'
	# domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_Cntg2.pddl'
	# problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Cntg_Problem.pddl'

	from PyDPOCL import GPlanner
	from Ground_Compiler_Library import precompile

	# run_all_tests()

	# plan_single_example(domain_file, problem_file)
	run_single_example(domain_file, problem_file, True)