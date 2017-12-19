
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


def cache_ground_steps(operators, objects, obtypes, stepnum=None):

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

			# append the step to our growin glist
			gsteps.append(gstep)

			print('Creating ground fabula step {}'.format(gstep))

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
			possible_alternatives = rewriteElms(GDO, sp, op, GL.objects, GL.object_types, height + 1)
			if not possible_alternatives:
				continue

			gdos = []
			if type(possible_alternatives) == bool:
				gdos.append(GDO)
			else:
				for gdo in possible_alternatives:
					gdos.append(gdo)

			for gdo in gdos:

				gdo.root.is_decomp = True

				# swap constructor IDs and replaced_IDs
				gdo._replaceInternals()
				gdo.replaceInternals()

				# Now create dummy init step and goal step
				dummy_init = Action(name='begin:' + str(gdo.name))
				dummy_init.has_cndt = False
				dummy_init.root.stepnumber = stepnum
				for condition in gdo.Preconditions:
					dummy_init.edges.add(Edge(dummy_init.root, condition.root, 'effect-of'))
					dummy_init.edges.update(condition.edges)
					dummy_init.elements.update(condition.elements)
				gsteps.append(dummy_init)
				stepnum+=1

				dummy_goal = Action(name='finish:' + str(gdo.name))
				dummy_goal.is_cndt = False
				dummy_goal.root.stepnumber = stepnum
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
				gdo.ground_subplan.root = gdo.root
				stepnum += 1
				gdo.height = height + 1
				gdo.root.height = height + 1

				# important to add init and goal steps first
				gsteps.append(gdo)
				# print('Creating ground step w/ height {}, h={}'.format(gdo, height))

	return gsteps, cndt_comparison_sets


@clock
def rewriteElms(GDO, sp, op, objects, obtypes, h):

	for elm in sp.elements:
		EG = elm
		if type(elm) == Operator or type(elm) == Literal:
			EG = eval(elm.typ).subgraph(sp, elm)
			if EG.arg_name is None:
				EG.arg_name = EG.root.arg_name

		assignElmToContainer(GDO, EG, list(op.elements))
	GDO.updateArgs()
	for (u,v) in op.nonequals:
		if GDO.Args[u] == GDO.Args[v]:
			return False

	# all_finished = True
	# for arg in GDO.Args:
	# 	if arg.name is None:
	# 		all_finished = False
	# 		break
	# if all_finished:
	# 	return True
	subplan_params = [item.arg_name for item in sp.elements if item.arg_name is not None]

	needs_substituting = []
	for i, arg in enumerate(GDO.Args):
		if isinstance(arg, Argument):
			# if the arg is none and its not a subplan
			if arg.name is None:
				if arg.arg_name in subplan_params:
					# all sub-plan args must be substituted by ground elements
					return False
				else:
					needs_substituting.append(i)

					# this is an argument of the operator, not the decomposition
	if len(needs_substituting) == 0:
		return True

	new_gdo_list = []
	cndts = [[obj for obj in objects if arg.typ == obj.typ or arg.typ in obtypes[obj.typ]] if i in needs_substituting else [GDO.Args[i]] for i, arg in enumerate(GDO.Args)]
	tuples = itertools.product(*cndts)
	for t in tuples:
		legaltuple = True
		for (u, v) in op.nonequals:
			if t[u] == t[v]:
				legaltuple = False
				break
		if not legaltuple:
			continue

		gstep = copy.deepcopy(GDO)

		# swap the leaves of the step with the objects in tuple "t"
		gstep.replaceArgs(t)

		# append the step to our growin glist
		new_gdo_list.append(gstep)
		print("creating alternative ground step {}".format(gstep))

	return new_gdo_list




def assignElmToContainer(GDO, EG, ex_elms):

	for ex_elm in ex_elms:
		if ex_elm.arg_name is None:
			continue
		if EG.arg_name != ex_elm.arg_name:
			if isinstance(EG, Argument):
				if EG.name != ex_elm.name:
					continue
			else:
				continue

		GDO.assign(ex_elm, EG)

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
		prim_fab_operators = [op for op in operators if op.root.typ == "step-s"]
		self.fab_steps = cache_ground_steps(prim_fab_operators, self.objects, obtypes)

		# camera steps
		cam_operators = [op for op in operators if op.root.typ == "step-c"]
		ground_objects = objects + [fab.root for fab in self.fab_steps]
		self.cam_steps = cache_ground_steps(cam_operators, ground_objects, obtypes, self.fab_steps[-1].stepnumber+1)
		# group these into sets based on only whether the preconditions and effects are different

		# axioms? need axioms such as if you believe all preconditions of a step s then you (bel (preconds s))

		self._gsteps = self.fab_steps + self.cam_steps

		self.ante_dict = defaultdict(set)
		self.threat_dict = defaultdict(set)
		self.flaw_threat_dict = defaultdict(set)
		self.id_dict = defaultdict(set)
		self.eff_dict = defaultdict(set)

		print('...Creating PlanGraph base level')
		self.loadAll()

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

	def insert(self, _pre, antestep, eff):
		self.id_dict[_pre.replaced_ID].add(antestep.stepnumber)
		self.eff_dict[_pre.replaced_ID].add(eff.replaced_ID)

	def loadAll(self):
		self.load(self._gsteps, self._gsteps)

	def loadPartition(self, particles):
		#print('... for each decompositional operator ')
		self.load(particles, self._gsteps)
		self.load(self._gsteps, particles)
		self.load(particles, particles)
		self._gsteps.extend(particles)

	def load(self, antecedents, consequents):
		for ante in antecedents:
			# steps which have no preconditions needn't have any candidates
			if not ante.has_cndt:
				continue
			for pre in ante.Preconditions:
				print('... Processing antecedents for {} \t\tof step {}'.format(pre, ante))
				self._loadAntecedentPerConsequent(consequents, ante, pre)

	@clock
	def _loadAntecedentPerConsequent(self, antecedents, _step, _pre):
		for gstep in antecedents:
			# skip steps which cannever be a candidate (such as goal)
			if not gstep.is_cndt:
				continue
			if self._parseEffects(gstep, _step, _pre) > 0:
				self.ante_dict[_step.stepnumber].add(gstep.stepnumber)


	def _parseEffects(self, gstep, _step, _pre):
		count = 0
		pre_name = _pre.name
		if pre_name in ALU_TERMS:
			pre_name = pre_name[:-4]
		for Eff in gstep.Effects:

			if Eff.name != pre_name:
				continue
			if False in [ea.name == pa.name for ea, pa in zip(Eff.Args, _pre.Args)]:
				continue
			if Eff.truth != _pre.truth:
				self.threat_dict[_step.stepnumber].add(gstep.stepnumber)
				self.flaw_threat_dict[_pre.replaced_ID].add(gstep.stepnumber)
			else:
				self.insert(_pre, gstep.deepcopy(replace_internals=True), Eff)
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


if __name__ ==  '__main__':
	# domain_file = 'domains/ark-domain.pddl'
	# problem_file = 'domains/ark-problem.pddl'
	domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_Simple.pddl'
	problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Simple_Problem.pddl'
	d_name = domain_file.split('/')[-1].split('.')[0]
	p_name = problem_file.split('/')[-1].split('.')[0]
	uploadable_pickle_name = d_name + '.' + p_name

	operators, decomps, objects, object_types, initAction, goalAction = parseDomAndProb(domain_file, problem_file)

	print("creating ground actions......\n")
	GL = GLib(operators, decomps, objects, object_types, initAction, goalAction)

	from Ground_Compiler_Library import precompile
	ground_step_list = precompile.deelementize_ground_library(GL)
	for i, gstep in enumerate(ground_step_list):
		with open("pickles/" + uploadable_pickle_name + "_" + str(i), 'wb') as ugly:
			pickle.dump(gstep, ugly)


	print('\n')
	print(GL)