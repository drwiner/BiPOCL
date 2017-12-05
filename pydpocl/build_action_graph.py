from collections import defaultdict
import copy
from uuid import uuid4
from clockdeco import clock

from Ground_Compiler_Library.PlanElementGraph import Action, PlanElementGraph, Condition
from Ground_Compiler_Library.Graph import Edge
from Ground_Compiler_Library.Element import Argument, Operator, Literal, Element, Actor
from Ground_Compiler_Library.pddl.parser import Parser, BipartiteStmt, Variable

from Ground_Compiler_Library.Flaws_unused import FlawLib

from Ground_Compiler_Library.pddlToGraphs import obTypesDict, problemToGraphs, addNegativeInitStates, \
	getFormulaGraph, createElementByType


STEP_PREDICATES = ["play", "play-seg", "effect", "precond", "linked-by", "arg", "linked", "<", "=", "actor",
                   "has-scale", "has-orient", "has-angle", "has-fov", "preconds", "obs", "bel"]


def get_arg_from_schema(arg_formula, schema):
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


def convert_params(params, obj_types):
	args = []
	for i, parameter in enumerate(params):
		ptype = parameter.types[0]
		ptypes = [ptype] + obj_types[ptype]

		# if it's a step-typed variable...
		if "step" in ptypes:
			arg = Operator(typ="Action", arg_name=parameter.name)
		elif "literal" in ptypes:
			arg = Literal(typ="Condition", arg_name=parameter.name)
		elif "person" in ptypes or "character" in ptypes or "actor" in ptypes:
			arg = Actor(typ=ptype, arg_name=parameter.name)
		else:
			arg = Argument(typ=ptype, arg_name=parameter.name)
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
		try:
			arg = get_arg_from_schema(predicate, schema)
		except:
			print('check')
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


def build_schema(action, schema, args):
	print("building \t{}".format(action.name))

	for i, arg in enumerate(args):
		schema.elements.add(arg)
		schema.edges.add(Edge(schema.root, arg, i))

	if action.precond is not None:
		precond_list = []
		for child in action.precond.formula.children:
			prec = build_literal(child, schema)
			if prec is None:
				continue
			precond_list.append(prec)
			schema.edges.add(Edge(schema.root, prec, "precond-of"))

	if action.effect is not None:
		effect_list = []
		for child in action.effect.formula.children:
			eff = build_literal(child, schema)
			effect_list.append(eff)
			schema.edges.add(Edge(schema.root, eff, "effect-of"))
	return schema


def get_arg_from_arg_name(arg_name, schema):
	for arg in schema.Args:
		if arg.arg_name == arg_name:
			return arg
	raise ValueError("arg name not found: {}".format(arg_name))


def get_schema_from_schema_name(schema_name, schemata):
	for schema in schemata:
		if schema.name == schema_name:
			return schema
	raise ValueError("schema name not found: {}".format(schema_name))


def build_schema_from_arg(condition, decomp_graph, schemata_types):
	"""
	e.g. (= ?call (call ?c))
	e.g. (= ?n2 (run ?c2 ?p4 ?p3))
	"""

	# the original decomposition step argument
	step_var = get_arg_from_arg_name(condition.Args[0].arg_name, decomp_graph)

	# the literal assigned to the decomposition step variable
	step_literal = Condition.subgraph(decomp_graph, condition.Args[1])

	swap_var_for_schema(step_literal.name, step_var, decomp_graph, schemata_types)


def swap_var_for_schema(arg_name, step_var, dschema, op_graphs):
	schema_template = get_schema_from_schema_name(arg_name, op_graphs)
	schema = schema_template.deepcopy()
	schema.root.arg_name = step_var.arg_name
	schema.arg_name = step_var.arg_name
	dschema.replaceArg(step_var, schema.root)
	dschema.elements.remove(step_var)
	# replace schema args with prescribed literal args
	old_args = schema.Args
	for old_arg in old_args:
		schema.elements.remove(old_arg)

	# add new edges to decomposition
	dschema.edges.update(schema.edges)
	# add new elements to decomposition
	dschema.elements.update(schema.elements)


def compile_decomp_literal(literal, dschema, op_graphs):
	c = Condition.subgraph(dschema, literal)

	if literal.name == "=":
		build_schema_from_arg(c, dschema, op_graphs)

	elif literal.name == "<":
		src = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		snk = get_arg_from_arg_name(c.Args[1].arg_name, dschema)
		dschema.OrderingGraph.addEdge(src, snk)

	elif literal.name == "linked-by":
		src = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		snk = get_arg_from_arg_name(c.Args[1].arg_name, dschema)
		link_condition = Condition.subgraph(dschema, c.Args[2])
		dschema.CausalLinkGraph.addEdge(src, snk, link_condition)

	elif literal.name == "linked":
		pass

	elif literal.name == "type":
		step_var = get_arg_from_arg_name(c.Args[0].arg_name, dschema)
		swap_var_for_schema(c.Args[1].name, step_var, dschema, op_graphs)

	elif literal.name == "not-occurs":
		pass

	elif literal.name == "has-scale":
		pass

	elif literal.name == "effect":
		pass

	elif literal.name == "precond":
		pass

	elif literal.name == "arg":
		pass

	else:
		raise ValueError("unknown predicate type\t{}".format(literal.name))
	print("processing decomp literal\t{}".format(c))


def build_decomp(dformula, dparams, dschema, op_graphs):
	existing_args = 0
	if hasattr(dschema, "Args"):
		existing_args = len(dschema.Args)

	for i, arg in enumerate(dparams):
		dschema.elements.add(arg)
		dschema.edges.add(Edge(dschema.root, arg, existing_args + i))

	if dformula.key != "and":
		build_literal(dformula, dschema)
		return dschema


	for child in dformula.children:
		literal = build_literal(child, dschema)
		if literal is None:
			continue
		compile_decomp_literal(literal, dschema, op_graphs)

	return dschema


def build_actions(action, obj_types):
	opGraphs = []
	dopGraphs = []
	all_ops = []
	for action in domain.actions:
		op = Operator(name=action.name, num_args=len(action.parameters))
		op_graph = Action(name=action.name, root_element=op)
		args = convert_params(action.parameters, obj_types)
		schema = build_schema(action, op_graph, args)

		if action.decomp is not None:

			if type(action.decomp) == BipartiteStmt:

				ddg = PlanElementGraph(name=action.name, type_graph='decomp_decomp')

				fabula_params = convert_params(action.decomp.fab_params, obj_types) + args
				decomp_schema = build_decomp(action.decomp.fab_formula, fabula_params, ddg, all_ops)
				decomp_schema.updateArgs()

				disc_params = convert_params(action.decomp.disc_params, obj_types)
				build_decomp(action.decomp.disc_formula, disc_params, decomp_schema, all_ops)

			else:

				decomp_graph = PlanElementGraph(name=action.name, type_graph='decomp')
				params = convert_params(action.decomp.sub_params, obj_types) + args
				decomp_schema = build_decomp(action.decomp.formula, params, decomp_graph, opGraphs)

			schema.subgraphs = decomp_schema
			dopGraphs.append(schema)
		else:
			opGraphs.append(schema)
		all_ops.append(schema)

	return opGraphs, dopGraphs


if __name__ == '__main__':
	domain_file = 'domains/Unity_Western_domain.pddl'
	prob = 'domains/unity_western_problem.pddl'

	parser = Parser(domain_file, prob)
	domain, dom = parser.parse_domain_drw()
	problem, v = parser.parse_problem_drw(dom)

	# GC.object_types.update()
	obj_types = obTypesDict(domain.types)

	args, init, goal = problemToGraphs(problem)
	objects = set(args.values())

	addNegativeInitStates(domain.predicates.predicates, init, objects)

	Operators, DOperators = build_actions(domain, obj_types)
