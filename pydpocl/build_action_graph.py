from collections import defaultdict
import copy
from uuid import uuid4
import itertools
from clockdeco import clock

# import Ground_Compiler_Library.pddl
from Ground_Compiler_Library.PlanElementGraph import Action, PlanElementGraph, Condition
from Ground_Compiler_Library.Graph import Edge
from Ground_Compiler_Library.Element import Argument, Operator, Literal, Element, Actor
from Ground_Compiler_Library.pddl.parser import Parser, BipartiteStmt, Variable, parse_formula

from Flaws import FlawLib

# from Ground_Compiler_Library.pddlToGraphs import problemToGraphs

CHAR_TYPES = {'character', 'actor', 'person', 'agent'}


def get_arg_from_op(arg_formula, schema):
	if hasattr(schema, "Args"):
		schema.updateArgs()
		for arg in schema.Args:
			if arg_formula.name == arg.arg_name:
				return arg
		raise ValueError("missing arg from schema?")

	for arg in schema.elements:
		if arg_formula.name == arg.arg_name:
			return arg
	raise ValueError("missing arg from schema?")


def get_arg_from_op_with_string(_arg, schema):
	if hasattr(schema, "constants"):
		if _arg in schema.constants.keys():
			return schema.constants[_arg]
	if hasattr(schema, "Args"):
		schema.updateArgs()
		for arg in schema.Args:
			if _arg == arg.name or _arg == arg.typ:
				return arg
		return None
		# ValueError("missing arg from schema?")
	for arg in schema.elements:
		if _arg == arg.name:
			return arg
	return None
	# ValueError("missing arg from schema?")


def convert_params(params, obj_types):
	args = []
	for i, parameter in enumerate(params):
		ptype = parameter.types[0]
		ptypes = [ptype] + obj_types[ptype]

		# if it's a step-typed variable...
		if "step" in ptypes:
			arg = Operator(typ=ptype, stepnumber=-1, arg_name=parameter.name)
		elif "literal" in ptypes:
			arg = Literal(typ=ptype, arg_name=parameter.name, ptypes=ptypes)
		elif "person" in ptypes or "character" in ptypes or "actor" in ptypes:
			arg = Actor(typ=ptype, arg_name=parameter.name, ptypes=ptypes)
		else:
			arg = Argument(typ=ptype, arg_name=parameter.name, ptypes=ptypes)
		args.append(arg)

	return args


def compile_nonequality(lit_elmnt, schema):
	children_dict = {edge.label: edge.sink for edge in schema.edges if edge.source.ID == lit_elmnt.ID}
	t1 = children_dict[0]
	t2 = children_dict[1]
	indices = [-1, -1]
	for i, arg in enumerate(schema.Args):
		if arg == t1:
			indices[0] = i
		if arg == t2:
			indices[1] = i
		if indices[0] >= 0 and indices[1] >= 0:
			break
	if indices[0] == -1 and indices[1] == -1:
		raise ValueError("args not found")
	schema.nonequals.add(tuple(indices))


def build_literal(literal, schema):
	predicate = literal.key

	# base case - its a var!
	if type(predicate) is not str:
		arg = get_arg_from_op(predicate, schema)

		return arg

	if len(literal.children) == 0 and predicate != '-':
		arg = get_arg_from_op_with_string(literal.key, schema)
		if arg is not None:
			return arg
		# return arg

	if hasattr(schema, "constants"):
		# pass
		if predicate in schema.constants.keys():
			arg = schema.constants[predicate]
			return arg

	# recursive case - it's not a var!
	term_list = []
	for child in literal.children:
		term = build_literal(child, schema)
		if term is None:
			continue
		term_list.append(term)

	# check negate and remove link as needed
	if len(term_list) == 1 and predicate == "not":
		lit = term_list[0]

		# special rules for non-equality constraints
		if lit.name in {'equals', '=', 'equal'}:
			compile_nonequality(lit, schema)
			return None

		lit.truth = False
		return lit

	lit = Literal(name=predicate, num_args=len(term_list), truth=True)

	schema.elements.add(lit)
	for i, term in enumerate(term_list):
		schema.edges.add(Edge(lit, term, i))

	return lit


def build_operator(action, schema, args):
	print("building \t{}".format(action.name))

	for i, arg in enumerate(args):
		schema.elements.add(arg)
		schema.edges.add(Edge(schema.root, arg, i))

	if action.precond is not None:
		precond_list = []
		if action.precond.formula.key == "and":
			for child in action.precond.formula.children:
				prec = build_literal(child, schema)
				if prec is None:
					continue
				precond_list.append(prec)
				schema.edges.add(Edge(schema.root, prec, "precond-of"))
		else:
			prec = build_literal(action.precond.formula, schema)
			schema.edges.add(Edge(schema.root, prec, "precond-of"))

	if action.effect is not None:
		effect_list = []
		if action.effect.formula.key == "and":
			for child in action.effect.formula.children:
				eff = build_literal(child, schema)
				effect_list.append(eff)
				schema.edges.add(Edge(schema.root, eff, "effect-of"))
		else:
			eff = build_literal(action.effect.formula, schema)
			schema.edges.add(Edge(schema.root, eff, "effect-of"))
	return schema


def get_arg_from_arg_name(arg_name, schema):
	for arg in schema.Args:
		if arg.arg_name == arg_name:
			return arg
	raise ValueError("arg name not found: {}".format(arg_name))


def get_op_from_op_name(schema_name, schemata):
	for schema in schemata:
		if schema.name == schema_name:
			return schema
	raise ValueError("schema name not found: {}".format(schema_name))


def build_op_from_arg(condition, decomp_graph):
	"""
	e.g. (= ?call (call ?c))
	e.g. (= ?n2 (run ?c2 ?p4 ?p3))
	e.g. (= ?end-master (virtual-shot scene-master-shot))
	"""

	# the original decomposition step argument
	step_var = get_arg_from_arg_name(condition.Args[0].arg_name, decomp_graph)

	# the literal assigning the decomposition step variable
	step_as_literal = Condition.subgraph(decomp_graph, condition.Args[1])

	step_var.name = step_as_literal.name
	for i, step_arg in enumerate(step_as_literal.Args):
		decomp_graph.edges.add(Edge(step_var, step_arg, i))


def compile_decomp_literal(literal, dschema, op_graphs):
	c = Condition.subgraph(dschema, literal)

	if literal.name == "=":
		if not literal.truth:
			print("pbreak")
		build_op_from_arg(c, dschema)

	elif literal.name == "<":
		src = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		snk = get_arg_from_arg_name(c.Args[1].arg_name, dschema)
		dschema.OrderingGraph.addEdge(src, snk)

	elif literal.name == "linked-by":
		src = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		snk = get_arg_from_arg_name(c.Args[1].arg_name, dschema)
		link_condition = Condition.subgraph(dschema, c.Args[2])
		if link_condition.root.arg_name is None:
			link_condition.root.arg_name = 'lc-' + str(uuid4())[19:23]
		dschema.CausalLinkGraph.addEdge(src, snk, link_condition)
		dschema.edges.add(Edge(c.Args[0], link_condition.root, "effect-of"))
		dschema.edges.add(Edge(c.Args[1],link_condition.root, "precond-of"))

	elif literal.name == "linked":
		src = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		snk = get_arg_from_arg_name(c.Args[1].arg_name, dschema)
		link_condition = Condition(root_element=Literal(arg_name='lc-' + str(uuid4())[19:23]))
		dschema.elements.add(link_condition.root)
		dschema.edges.add(Edge(c.Args[0], link_condition.root, "effect-of"))
		dschema.edges.add(Edge(c.Args[1], link_condition.root, "precond-of"))
		dschema.CausalLinkGraph.addEdge(src, snk, link_condition)

	elif literal.name == "type":
		step_var = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		step_var.name = c.Args[1].name
		# swap_var_for_schema(c.Args[1].name, step_var, dschema, op_graphs)

	elif literal.name == "not-occurs":
		pass

	elif literal.name == "master-shot":
		pass

	elif literal.name == "has-scale":
		"""
		[note] if no argument is type scale, then raise TypeError.
		[note] must have declared type already (there is no special edge type called scale)
		"""
		if c.Args[0].name is None:
			raise ValueError("need to declare operator type of step-typed variable with \'type\' predicate, {}".format(literal))

		schema_template = get_op_from_op_name(c.Args[0].name, op_graphs)
		args_with_scale = [i for i, arg in enumerate(schema_template.Args) if arg.typ == "scale"]

		if len(args_with_scale) > 1:
			raise ValueError('too many args typed as scale')
		if len(args_with_scale) == 0:
			raise ValueError("no args in type {} that are scale typed".format(c.Args[0].name))

		arg_num = args_with_scale[0]
		dschema.edges.add(Edge(c.Args[0], c.Args[1], arg_num))

	elif literal.name == "has-orient":
		if c.Args[0].name is None:
			raise ValueError("need to declare operator type of step-typed variable with \'type\' predicate, {}".format(literal))
		schema_template = get_op_from_op_name(c.Args[0].name, op_graphs)
		args_with_ort = [i for i, arg in enumerate(schema_template.Args) if arg.typ == "orient"]

		if len(args_with_ort) > 1:
			raise ValueError('too many args typed as orient')
		if len(args_with_ort) == 0:
			raise ValueError("no args in type {} that are orient typed".format(c.Args[0].name))

		arg_num = args_with_ort[0]
		dschema.edges.add(Edge(c.Args[0], c.Args[1], arg_num))

	elif literal.name == "effect":
		dschema.edges.add(Edge(c.Args[0], c.Args[1], "effect-of"))

	elif literal.name == "precond":
		dschema.edges.add(Edge(c.Args[0], c.Args[1], "precond-of"))

	elif literal.name == "arg":
		"""
		e.g.
		(arg 0 ?est ?n0)
		(arg 1 ?est mid) <-- literal only here if it is a name
		"""
		arg_num = int(c.Args[0].name)
		step_var = c.Args[1]
		if type(c.Args[2]) == "Literal":
			step_var_operator_name = c.Args[1].name

			schema_template = get_op_from_op_name(step_var_operator_name, op_graphs)
			arg_template = schema_template.Args[arg_num]
			arg = arg_template.deepcopy()
			arg.name = c.Args[2].name
			dschema.elements.add(arg)
			dschema.edges.add(Edge(step_var, arg, arg_num))
		else:
			dschema.edges.add(Edge(step_var, c.Args[2], arg_num))
	elif literal.name == "play" or literal.name == "play-seg":
		pass
	elif literal.name == "truth":
		c.Args[0].truth = bool(int(c.Args[1].name))
	elif literal.name == "cntg":
		dschema.OrderingGraph.addCntg(c.Args[0], c.Args[1])
	else:
		raise ValueError("unknown predicate type\t{}".format(literal.name))

	debug = str(literal.name) + "\t[" + ", ".join([str(a.arg_name) if a.arg_name is not None else str(c) for a in c.Args]) + "]"
	print("processing decomp literal\t{}".format(debug))


def build_decomp(dformula, dparams, dschema, op_graphs):
	existing_args = 0
	if hasattr(dschema, "Args"):
		existing_args = len(dschema.Args)

	for i, arg in enumerate(dparams):
		dschema.elements.add(arg)
		dschema.edges.add(Edge(dschema.root, arg, existing_args + i))

	if dformula.key != "and":
		literal = build_literal(dformula, dschema)
		if literal is None:
			raise ValueError("literal is None")
		compile_decomp_literal(literal, dschema, op_graphs)
		return dschema

	for child in dformula.children:
		literal = build_literal(child, dschema)
		if literal is None:
			continue
		compile_decomp_literal(literal, dschema, op_graphs)

	return dschema


def make_decomp(action_name, dparams, dformula, schemata):
	decomp_graph = PlanElementGraph(name=action_name, type_graph="decomp")
	decomp_schema = build_decomp(dformula, dparams, decomp_graph, schemata)
	decomp_schema.updateArgs()
	return decomp_schema


def build_operators(actions, obj_types, cnsts):
	primitive_operators = []
	composite_operators = []
	all_operators = []

	for action in actions:

		# create operator token (a step-typed variable)
		step_typed_var = Operator(name=action.name, typ=action.action_type, stepnumber=-1, num_args=len(action.parameters))
		# create operator with step-typed variable as root
		operator_template = Action(name=action.name, root_element=step_typed_var)
		# convert args
		args = convert_params(action.parameters, obj_types)
		# if action.decomp is not None:
		# 	args = convert_params(action.decomp.sub_params, obj_types) + args
		operator_template.constants = {cnst.name: cnst for cnst in cnsts}
		schema = build_operator(action, operator_template, args)

		if action.decomp is None:
			primitive_operators.append(schema)
		else:
			dargs = convert_params(action.decomp.sub_params, obj_types) + args
			# initially use all parameters to become decomposition schema args
			dschema = make_decomp(action.name, dargs, action.decomp.formula, all_operators)
			dschema.constants = operator_template.constants
			# bipartite has second decomposition method
			if type(action.decomp) == BipartiteStmt:
				disc_params = convert_params(action.decomp.disc_params, obj_types)
				# use same decomp schema, and just add new parameters

				build_decomp(action.decomp.disc_formula, disc_params, dschema, all_operators)

			schema.subplan = dschema
			composite_operators.append(schema)

		all_operators.append(schema)

	return primitive_operators, composite_operators


def addStatics(operators):
	for op in operators:
		for eff in op.effects:
			FlawLib.non_static_preds.add((eff.name, eff.truth))


def obTypesDict(object_types):
	obtypes = dict()
	not_found_yet = []
	obtypes["object"] = []
	for t in object_types:

		if t.parent in obtypes.keys():
			obtypes[t.name] = [t.parent] + obtypes[t.parent]
		else:
			not_found_yet.append(t)

	while len(not_found_yet) > 0:

		for item in not_found_yet:
			if item.parent in obtypes.keys():
				obtypes[t.name] = [t.parent] + obtypes[t.parent]
				not_found_yet.remove(t)
				break

	return obtypes


def has_equal_args(a_list, b_list, agraph, bgraph):
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
			if not has_equal_args(a_cond.Args,b_cond.Args, a_cond, b_cond):
				return False
	return True


def addNegativeInitStates(formulae, initAction, init_effects, objects, obj_types):
	"""
	for each predicate, satisfy arguments with objects. if literal not in initial state, add negation
	"""

	# collect initial states as tuples
	ie_args_collection = [Condition.subgraph(initAction, init_eff.sink) for init_eff in init_effects]

	# for init_eff in init_effects:
	# 	ie = Condition.subgraph(initAction, init_eff.sink)
	# 	ie_args
	# 	ie.updateArgs()
	#
	# 	ie_args = tuple([ie.name] + [arg.name for arg in ie.Args])
	# 	ie_args_collection.append(ie_args)

	# for each predicate formula in domain
	for f, p in formulae:
		if f.key in ["distance-between", "arg", "less-than", "play", "play-seg", "alu", "fol", "dur", "=", "obs-seg", "bel-alu", "obs-alu", "obs-seg-alu", "obs", "obs-seg-cntg", "cntg", "effect", "precond", "type", "linked", "linked-by", "<", "has-scale", "has-angle", "has-fov", "has-orient", "preconds"]:
			continue
		# create a predicate schema template
		# if it's a step element or a plan element, then we need to consider all literal arguments
		literal_template = Condition(root_element=Literal(name=f.key, num_args=len(p.parameters)))

		# get consistent-typed object signatures
		cndts = [[obj for obj in objects if pchild.types[0] in obj.p_types] for pchild in p.parameters]

		# create tokens for variables in template
		for i, p_arg, in enumerate(p.parameters):
			if p_arg.types[0] == "person":
				arg_token = Actor(arg_name=p_arg.name,typ=p_arg.types[0])
			else:
				arg_token = Argument(arg_name=p_arg.name, typ=p_arg.types[0])
			literal_template.edges.add(Edge(literal_template.root, arg_token, i))
			literal_template.elements.add(arg_token)

		param_tuples = [i for i in itertools.product(*cndts)]

		# for each candidate signature
		for pt in param_tuples:

			# create negative literal to add as negative initial step effect
			literal_template_copy = literal_template.deepcopy()
			# lit = build_literal(f, initAction)
			# literal_template_copy = Condition(root_element=Literal(name=f.key, num_args=len(p.parameters)))
			build_literal(f, literal_template_copy)
			literal_template_copy.root.truth = True
			literal_template_copy.root.ID = uuid4()
			literal_template_copy.elements = set(list(literal_template_copy.elements))
			literal_template_copy.edges = set(list(literal_template_copy.edges))
			literal_template_copy.updateArgs()
			# swap arguments of template
			literal_template_copy.replaceArgs(pt)

			in_initial_state = False
			for ie in ie_args_collection:
				if ie.name != literal_template_copy.name:
					continue
				if ie.truth != literal_template_copy.truth:
					continue
				if len(ie.Args) != len(literal_template_copy.Args):
					continue
				if not has_equal_args(ie.Args, literal_template_copy.Args, ie, literal_template_copy):
					continue
				in_initial_state = True

			if in_initial_state:
				continue

			# ignore if discovered in initial state
			# ie = tuple([f.key] + [t.name for t in list(pt)])
			# if ie in ie_args_collection:
			# 	continue

			# now set it false

			literal_template_copy.root.truth = False

			# update initial Action
			print("building ground literal\t{}".format(literal_template_copy))
			initAction.elements.update(list(literal_template_copy.elements))
			initAction.edges.update(list(literal_template_copy.edges))
			initAction.edges.add(Edge(initAction.root, literal_template_copy.root, 'effect-of'))
			# print("new initial effect: {}".format(literal_template_copy))


def compile_problem_objs(problem, obj_types):
	objs = []
	for i, object in enumerate(problem.objects):
		ptypes = [object.typeName] + obj_types[object.typeName]
		if object.typeName.lower() in CHAR_TYPES:
			obj = Actor(name=object.name, typ=object.typeName, ptypes=ptypes)
		else:
			obj = Argument(name=object.name, typ=object.typeName, ptypes=ptypes)
		objs.append(obj)
	return objs


def compile_domain_constants(items, obj_types):
	constants = []

	for i, const in enumerate(items):
		ptypes = [const.typeName] + obj_types[const.typeName]
		if const.typeName.lower() in CHAR_TYPES:
			obj = Actor(name=const.name, typ=const.typeName, ptypes=ptypes)
		else:
			obj = Argument(name=const.name, typ=const.typeName, ptypes=ptypes)
		constants.append(obj)
	return constants


def build_problem_goal(problem, args):
	goal_op = Operator(name='dummy_goal', stepnumber=1, num_args=0)
	goal_graph = Action(name='dummy_goal', root_element=goal_op)
	for i, object in enumerate(args):
		goal_graph.elements.add(object)
		goal_graph.edges.add(Edge(goal_op, object, i))

	if problem.goal.formula.key != "and":
		build_literal(problem.goal.formula, goal_graph)
	else:
		precond_list = []
		for child in problem.goal.formula.children:
			prec = build_literal(child, goal_graph)
			if prec is None:
				continue
			precond_list.append(prec)
			goal_graph.edges.add(Edge(goal_op, prec, "precond-of"))
	return goal_graph


def build_problem_init(problem, args):
	init_op = Operator(name='dummy_init', stepnumber=0, num_args=0)
	init_graph = Action(name='dummy_init', root_element=init_op)

	for i, object in enumerate(args):
		init_graph.elements.add(object)
		init_graph.edges.add(Edge(init_op, object, i))

	effect_edges = []
	for condition in problem.init.predicates:
		effect = build_literal(condition, init_graph)
		if effect is None:
			continue
		eff_edge = Edge(init_op, effect, 'effect-of')
		init_graph.edges.add(eff_edge)
		effect_edges.append(eff_edge)

	return init_graph, effect_edges


""" Convert pddl problem file to usable structures"""
@clock
def build_problem(problem):
	objs = compile_problem_objs(problem)

	goal_graph = build_problem_goal(problem, objs)
	init_graph = build_problem_init(problem, objs)

	return objs, init_graph, goal_graph


def parseDomAndProb(dom_file, prob_file):

	parser = Parser(dom_file, prob_file)
	domain = parser.parse_domain()
	problem = parser.parse_problem()

	# GC.object_types.update()
	obj_types = obTypesDict(domain.types)

	omega_args = compile_problem_objs(problem, obj_types)
	constants = compile_domain_constants(domain.constants, obj_types)
	objs = omega_args + constants
	goal = build_problem_goal(problem, objs)
	init, init_effects = build_problem_init(problem, objs)

	predicates = zip(domain.predicates.formulas, domain.predicates.predicates)
	addNegativeInitStates(predicates, init, init_effects, objs, obj_types)

	primitive_ops, composite_ops = build_operators(domain.actions, obj_types, constants)

	addStatics(primitive_ops)
	addStatics(composite_ops)

	return primitive_ops, composite_ops, objs, obj_types, init, goal


if __name__ == '__main__':

	domain_file = 'domains/Unity_Western_domain.pddl'
	prob = 'domains/unity_western_problem.pddl'

	primitive_ops, composite_ops, objects, obj_types, init, goal = parseDomAndProb(domain_file, prob)


