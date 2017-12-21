import sys

from Ground_Compiler_Library.Ground import GLib, upload
from Ground_Compiler_Library.GElm import GLiteral, GStep
from Ground_Compiler_Library.Element import Operator, Literal, Argument
from Ground_Compiler_Library.PlanElementGraph import Condition, Action

def decompile(arg, p):
	if isinstance(arg, Argument):
		return arg
	elif isinstance(arg, Operator):
		arg.arg_name = str(Action.subgraph(p, arg))
	elif isinstance(arg, Literal):
		arg.arg_name = str(Condition.subgraph(p, arg))
	return arg


def deelementize_ground_library(GL):
	g_steps = []
	for step in GL._gsteps[0:-2]:
		preconds = [GLiteral(p.name, [decompile(arg, p) for arg in p.Args],
						p.truth, p.replaced_ID, (p.name, p.truth) not in GL.non_static_preds)
							for p in step.Preconditions]
		gstep = GStep(step.name, [decompile(arg, step) for arg in step.Args], preconds, step.stepnumber, step.height)
		gstep.setup(GL.ante_dict, GL.id_dict, GL.threat_dict, GL.flaw_threat_dict, GL.cntg_mental)

		# all primitive steps (except for dummies) are in _gsteps before all decomp steps, where each level is totally ordered
		if gstep.height > 0:
			gstep.swap_substeps(g_steps, step, len(GL._gsteps))

		g_steps.append(gstep)

	init_preconds = [GLiteral(p.name, [decompile(arg, p) for arg in p.Args],
	                          p.truth, p.replaced_ID, (p.name, p.truth) not in GL.non_static_preds)
	                 for p in GL[-2].Effects]

	dummy_init = GStep(GL[-2].name, ["0"],
	                   init_preconds, GL[-2].stepnumber, GL[-2].height)
	dummy_init.instantiable = False

	goal_preconds = [GLiteral(p.name, [decompile(arg, p) for arg in p.Args],
	                          p.truth, p.replaced_ID, (p.name, p.truth) not in GL.non_static_preds) for p in
	                 GL[-1].Preconditions]
	dummy_goal = GStep(GL[-1].name, ["1"], goal_preconds, GL[-1].stepnumber, GL[-1].height)
	dummy_goal.setup(GL.ante_dict, GL.id_dict, GL.threat_dict, GL.flaw_threat_dict, GL.cntg_mental)
	dummy_goal.instantiable = False

	g_steps.append(dummy_init)
	g_steps.append(dummy_goal)

	return g_steps

if __name__ == '__main__':
	num_args = len(sys.argv)
	if num_args >1:
		domain_file = sys.argv[1]
		if num_args > 2:
			problem_file = sys.argv[2]
	else:
		domain_file = 'domains/Unity_Western_Domain.pddl'
		problem_file = 'domains/travel-to-la.pddl'

	GL = GLib(domain_file, problem_file)
	with open('ground_steps.txt', 'w') as gs:
		for step in GL:
			gs.write(str(step))
			gs.write('\n')
	ground_step_list = deelementize_ground_library(GL)
	with open('ground_steps.txt', 'a') as gs:
		gs.write('\n\n')
		for step in ground_step_list:
			gs.write(str(step))
			gs.write('\n')
	upload(ground_step_list, GL.name)