
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
from Ground_Compiler_Library.Flaws_unused import FlawLib
import hashlib

#GStep = namedtuple('GStep', 'action pre_dict pre_link')
Antestep = namedtuple('Antestep', 'action eff_link')


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

			# replace the ID of the internal elements
			gstep._replaceInternals()

			# assign the step number (only one of the following should be necessary)
			gstep.root.stepnumber = stepnum
			gstep.root.arg_name = stepnum
			stepnum += 1

			# swap the leaves of the step with the objects in tuple "t"
			gstep.replaceArgs(t)

			# do only in cases when there are step-typed arguments (what about literal-typed arguments?
			if gsd is not None:
				for arg in gstep.Args:
					if arg in gsd.keys():
						step = gsd[arg]
						""" possibly can just replaceArg and add elements without making copy... since everything will
							get cloned anyway.
						"""
						# clone, but don't replace IDs because this isn't a new step, it's an existing step
						arg_clone = step.deepcopy(replace_internals=True)
						# swap argument with step root clone
						gstep.replaceArg(arg, arg_clone.root)
						# add elements and edges to gstep graph
						gstep.elements.update(arg_clone.elements)
						gstep.edges.update(arg_clone.edges)


			# if one of the args is an operator token

			# append the step to our growin glist
			gsteps.append(gstep)

			print('Creating ground step {}'.format(gstep))

			# not sure why one would need the following:
			# gstep.replaceInternals()

			# assign height of the step to the root element and
			gstep.height = 0
			gstep.root.height = 0

	return gsteps


def groundDecompStepList(doperators, GL, stepnum=0, height=0):
	gsteps = []

	print('...Creating Ground Decomp Steps')
	for op in doperators:
		#Subplans = Plannify(op.subplan, GL)

		print('processing operator: {}'.format(op))
		try:
			sub_plans = Plannify(op.subplan, GL, height)
		except:
			continue
		for sp in sub_plans:

			GDO = copy.deepcopy(op)
			GDO.is_decomp = True

			# rewrites operator arguments based on groundings of sub-plan, provides alternatives
			gdo = rewriteElms(GDO, sp, GL.objects, GL.object_types, height + 1)
			if not gdo:
				continue

			# gdos = []
			# if type(possible_alternatives) == bool:
			# 	gdos.append(GDO)
			# else:
			# 	for gdo in possible_alternatives:
			# 		gdos.append(gdo)
			#
			# for gdo in gdos:

			gdo.root.is_decomp = True

			# swap constructor IDs and replaced_IDs
			gdo._replaceInternals()
			gdo.replaceInternals()

			# Now create dummy init step and goal step
			dummy_init = Action(name='begin:' + str(gdo.name))
			dummy_init.has_cndt = False
			dummy_init.root.stepnumber = stepnum
			dummy_init.stepnumber = stepnum
			for condition in gdo.Preconditions:
				dummy_init.edges.add(Edge(dummy_init.root, condition.root, 'effect-of'))
				dummy_init.edges.update(condition.edges)
				dummy_init.elements.update(condition.elements)
			gsteps.append(dummy_init)
			stepnum+=1

			dummy_goal = Action(name='finish:' + str(gdo.name))
			dummy_goal.is_cndt = False
			dummy_goal.root.stepnumber = stepnum
			dummy_goal.stepnumber = stepnum
			for condition in gdo.Effects:
				dummy_goal.edges.add(Edge(dummy_goal.root, condition.root, 'precond-of'))
				dummy_goal.edges.update(condition.edges)
				dummy_goal.elements.update(condition.elements)
			gsteps.append(dummy_goal)
			stepnum+=1

			gdo.sub_dummy_init = dummy_init
			gdo.sub_dummy_goal = dummy_goal

			gdo.ground_subplan = copy.deepcopy(sp)
			gdo.root.stepnumber = stepnum
			gdo.stepnumber = stepnum
			gdo.ground_subplan.root = gdo.root
			stepnum += 1
			gdo.height = height + 1
			gdo.root.height = height + 1

			# important to add init and goal steps first
			gsteps.append(gdo)
				# print('Creating ground step w/ height {}, h={}'.format(gdo, height))

	return gsteps


# @clock
def rewriteElms(GDO, sp, objects, obtypes, h):

	sp_arg_dict = {elm.arg_name: elm for elm in sp.elements}
	needs_substituting = []
	for arg in GDO.Args:
		# if this arg isn't part of sub-plan (is that possible?)
		if arg.arg_name not in sp_arg_dict.keys():
			if arg.name is None:
				needs_substituting.append(arg)
			raise ValueError("just checking if this is possible")
		sp_elm = sp_arg_dict[arg.arg_name]
		if type(sp_elm) == Operator:
			A = Action.subgraph(sp, sp_elm)
			GDO.replaceArg(arg, A.root)
			GDO.elements.remove(arg)
			GDO.elements.update(A.elements)
			GDO.edges.update(A.edges)
		elif type(sp_elm) == Literal:
			C = Condition.subgraph(sp, sp_elm)
			GDO.replaceArg(arg, C.root)
			GDO.elements.remove(arg)
			GDO.elements.update(C.elements)
			GDO.edges.update(C.edges)
	GDO.updateArgs()
	for (u,v) in GDO.nonequals:
		if GDO.Args[u] == GDO.Args[v]:
			return False
	return GDO


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
		gstep_dict = {fab.root: fab for fab in self.fab_steps}
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
		# self.loadAll()

		for i in range(3):
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
				# self.eff_dict[_pre.replaced_ID].add(Eff.replaced_ID)
				self.id_dict[_pre.replaced_ID].add(gstep.stepnumber)
				if _pre.name in ALU_TERMS:
					self.cntg_mental[_pre.replaced_ID].add(gstep.stepnumber)

				count += 1
		return count



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

	def getConsistentEffect(self, S_Old, precondition):
		effect_token = None
		for eff in S_Old.effects:
			if eff.replaced_ID in self.eff_dict[precondition.replaced_ID] or self.eff_dict[eff.replaced_ID] == \
					self.eff_dict[precondition.replaced_ID]:
				effect_token = eff
				break
		if effect_token is None:
			raise AttributeError('story_GL.eff_dict empty but id_dict has antecedent')
		return effect_token

	def hasConsistentPrecondition(self, Sink, effect):
		for pre in Sink.preconditions:
			if effect.replaced_ID in self.eff_dict[pre.replaced_ID]:
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

def load_from_pickle(pickle_name):
	ground_steps = []
	i = 0
	while True:
		try:
			print(i)
			with open(pickle_name + str(i), 'rb') as ugly:
				ground_steps.append(pickle.load(ugly))
			i += 1
		except:
			break
	return ground_steps


def load_pickles(pickle_name):
	operators, decomps, objects, object_types, initAction, goalAction = parseDomAndProb(domain_file, problem_file)

	print("creating ground actions......\n")
	GL = GLib(operators, decomps, objects, object_types, initAction, goalAction)

	from Ground_Compiler_Library import precompile
	ground_step_list = precompile.deelementize_ground_library(GL)
	for i, gstep in enumerate(ground_step_list):
		with open(pickle_name + str(i), 'wb') as ugly:
			pickle.dump(gstep, ugly)

	return ground_step_list


# def append_cache(pickle_name):



if __name__ ==  '__main__':
	domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_Simple.pddl'
	problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Simple_Problem.pddl'
	d_name = domain_file.split('/')[-1].split('.')[0]
	p_name = problem_file.split('/')[-1].split('.')[0]
	uploadable_pickle_name = d_name + '.' + p_name

	from PyDPOCL import GPlanner

	pname = "pickles/" + uploadable_pickle_name + "_"


	# gsteps = load_from_pickle(pname)
	gsteps = load_pickles(pname)
	print('test')

	planner = GPlanner(gsteps)
	planner.solve(k=1)
	# load_pickles(pname)

	# domain_file = 'domains/ark-domain.pddl'
	# problem_file = 'domains/ark-problem.pddl'

