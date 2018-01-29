"""
Read plan solution, use time table to coordinate times
"""
import json
from CacheGroundSteps import plan_single_example
from plan_to_lists import make_partial_ordered_list

# from Ground_Compiler_Library.GElm import GStep, GLiteral
dist_dict = {}
with open("distances.txt", 'r') as fol:
	for line in fol:
		fol_sp = line.split()
		dist_dict[(fol_sp[0], fol_sp[2])] = float(fol_sp[-1])

NAV_MOVE_RATE = {"strut": 1.5}
NAV_ARGS = {"strut": (1,2)}

FAB_SEGMENTS = {"strut": dict()}

FAB_SEGMENTS["strut"]["start"] = (0, .4)
FAB_SEGMENTS["strut"]["mid"] = (.4, .6)
FAB_SEGMENTS["strut"]["end"] = (.6, 1)
FAB_SEGMENTS["strut"]["slow-max"] = 3.5
FAB_SEGMENTS["strut"]["fast-max"] = 2

FAB_GAMEOBJECT_ARG = {"strut": 0, "turn-to": 0}

FAB_STEPS = ["strut", "turn-to"]
# ANIM_MAP = {"strut": "Stroll"}
FAB_TYPES = {"strut": "navigate"}

ORIENTS = {"front": '0', "behind": "180", "behind-right": 210, "behind-left": 150}

# FAB_TYPES = {"strut": nav_step_to_xml, "turn-to": "animate"}
CAM_STEPS = ["cam"]
# NAV_ACTIONS = ["strut"]


def step_extraction(plan_steps):
	fab_steps = []
	cam_steps = []
	for step in plan_steps:
		t = step.schema.split("-")[0]
		if t in FAB_STEPS:
			fab_steps.append(step)
		elif t in CAM_STEPS:
			cam_steps.append(step)
	return fab_steps, cam_steps

### FABULA ### action for navigating
def nav_act_to_json(state, step, step_token, begin_time):
	# state: state space representation provided to each fabula action to determine location
	which_arg = FAB_GAMEOBJECT_ARG[step_token]
	gameobj = step.Args[which_arg].name

	# NAV ARGS: for each step type, we would need to specifically annotate origina and destination locations
	origin, dest = NAV_ARGS[step_token]

	# the duration is based on the distance plus the move rate. This is "real world" move rate, not how long shown
	duration = dist_dict[(step.Args[origin].name, step.Args[dest].name)] / NAV_MOVE_RATE[step_token]

	location = "None"
	# find starting location in current state
	for lit in state:
		if lit.name != "at" or lit.truth is False:
			continue
		if lit.Args[0] != step.Args[which_arg]:
			continue
		location = lit.Args[1].name
		break

	ending_loc = "None"
	# WARNING: hack used here is that any navigation step has a single true "at" literal describing end location
	for eff in step.effects:
		if eff.name == "at" and eff.Args[0].name == gameobj and eff.truth is True:
			ending_loc = eff.Args[1].name
			break

	json_obj = {
		"method_used": "nav_act",
		"name": step.schema,
		"step_id": step.schema.split("-")[2].split("[")[0],
		"step_num": step.stepnumber,
		"type": FAB_TYPES[step_token],
		"start": begin_time,
		"duration": duration,
		"start_pos_name": location,
		"end_pos_name": ending_loc,
		"animation_name": step_token,
		"gameobject_name": gameobj
	}

	return json_obj, duration


def stationary_act_to_json():
	pass


def transition_state(state, step):
	new_state = []
	do_not_transition = []
	for effect in set(step.effects):
		same_condition = [condition for condition in state if condition.sameProposition(effect)]
		if len(same_condition) > 1:
			raise ValueError("should not be 2 of the same proposition. "
			    "\n\n A proposition is a predicate name and equivalent arguments, but where truth value can differ.")
		if len(same_condition) == 0:
			# this proposition isn't one found in previous states
			new_state.append(effect)
			continue
		new_state.append(effect)
		do_not_transition.append(same_condition[0])
	for condition in state:
		if condition in do_not_transition:
			continue
		new_state.append(condition)
	return set(new_state)


def fabula_to_json(init, steps):
	before_time = 0

	before_state = init
	clips = []
	for step in steps:
		step_tokens = step.schema.split("-")[:2]
		# step_with_num = step_tokens[0] + "-" + step_tokens[1]
		xml_method = FAB_METHODS[step_tokens[0]]

		# e.g.:  nav_step_to_xml   (state, step, step_token, begin_time, duration)
		sub_root, step_duration = xml_method(before_state, step, step_tokens[0], before_time)
		before_state = transition_state(before_state, step)
		before_time += step_duration
		clips.append(sub_root)

	return clips


def fabula_to_json_po(init, nested_po_steps):
	before_time = 0
	before_state = init
	clips = []
	for po_list in nested_po_steps:
		max_step_duration = 0
		for step in po_list:
			step_tokens = step.schema.split("-")[:2]
			# step_with_num = step_tokens[0] + "-" + step_tokens[1]
			xml_method = FAB_METHODS[step_tokens[0]]

			# e.g.:  nav_step_to_xml   (state, step, step_token, begin_time, duration)
			sub_root, step_duration = xml_method(before_state, step, step_tokens[0], before_time)
			before_state = transition_state(before_state, step)
			clips.append(sub_root)
			if step_duration > max_step_duration:
				max_step_duration = step_duration

		before_time += step_duration
	return clips


def get_ref_to_fab_json_obj(fab_step_ref, fab_clips):
	fab_step_id = str(fab_step_ref.root.ID)[19:23]
	fab_json = None
	same_step_num = []
	for clip in fab_clips:
		fs_id = clip["step_id"]
		if fs_id == fab_step_id:
			# this match implies we have found the clip corresponding to the reference fabula step
			fab_json = clip
			break
		if clip["step_num"] == fab_step_ref.stepnumber:
			same_step_num.append(clip)
	if fab_json is None:
		# idea 1: find the step reference in the past discourse step, and start search from there
		# WARNING: instead, hack used: juust find first step with same stepnumber
		try:
			fab_json = same_step_num[0]
		except:
			raise ValueError("no fab step with same stepnum found")
		# find the "nearest" clip with same stepnumber
	return fab_json


def discourse_to_json(steps, fab_clips):

	clips = []
	before_time = 0
	for step in steps:

		# cam - shot - segment [fab-step, orientation]
		# cam - virtual - shot [cam-name, fab-step, segment]

		step_tokens = step.schema.split("-")

		# gets the first fabula step reference in the arguments
		fab_step_ref = get_steps_in_args(step.Args)[0]

		# get a reference to the fabula json object
		fab_json = get_ref_to_fab_json_obj(fab_step_ref, fab_clips)

		type_of_action_being_filmed = fab_json["type"]
		type_of_camera_being_used = step_tokens[1]

		# json method depends on type of action filmed (stationary or navigate) and type of camera (cam or virtual)
		json_method = DISC_METHODS[type_of_action_being_filmed][type_of_camera_being_used]

		step_root, this_duration = json_method(before_time, step_tokens, fab_json, step.Args[0].name)
		# step_root = xml_method(step.schema, before_time, this_duration, this_fab_start_time, orient, target, fab_xml)
		clips.append(step_root)

		before_time += this_duration
	return clips


def get_steps_in_args(args):
	return [arg for arg in args if hasattr(arg, "stepnumber")]


def nav_virtual_shot_to_json(before_time, step_tokens, fab_json, camName):
	# cam - virtual - shot [cam-name, fab-step, segment]
	segment = step_tokens[-1].split('\'')[-2]
	target = fab_json['gameobject_name']
	s, f = FAB_SEGMENTS[fab_json["animation_name"]][segment]
	fab_duration = fab_json["duration"]
	this_duration = f * float(fab_duration) - s * float(fab_duration)
	this_fab_start_time = fab_json["start"] + s * float(fab_duration)
	step_root = {
		"method_used": "nav_virtual_shot_to_json",
		"name": " ".join(step_tokens),
		"type": "nav_virtual",
		"start": before_time,
		"duration": this_duration,
		"fab_step": fab_json["name"],
		"fab_start": this_fab_start_time,
		"aim_target": target,
		"camera_name": camName
	}

	return step_root, this_duration


def nav_cam_shot_to_json(before_time, step_tokens, fab_json, camName=None):
	# cam - shot - segment [fab-step, orientation]
	segment = step_tokens[2]
	orient = step_tokens[2].split('[')[0]
	target = fab_json["gameobject_name"]

	# fab_with_num = fab_tokens[0] + "-" + fab_tokens[1]
	step_type = fab_json["animation_name"]
	s, f = FAB_SEGMENTS[step_type][segment]
	fab_duration = fab_json["duration"]
	this_duration = f * float(fab_duration) - s * fab_duration
	this_fab_start_time = fab_json["start"] + s * fab_duration

	fab_location_start = fab_json["start_pos_name"]
	fab_location_end = fab_json["end_pos_name"]
	dist = dist_dict[(fab_location_start, fab_location_end)]


	step_root = {
		"method_used": "nav_cam_shot_to_json",
		"name": ' '.join(step_tokens),
		"type": "nav_cam",
		"start": before_time,
		"duration": this_duration,
		"fab_step_name": fab_json["name"],
		"fab_start": this_fab_start_time,
		"start_pos_name": fab_location_start,
		"start_dist_offset": s * dist,
		"end_pos_name": fab_location_end,
		"end_dist_offset": f * dist,
		"orient": orient,
		"aim_target": target,
		"camera_name": camName
	}

	return step_root, this_duration


def fab_step_to_id(gstep):
	return gstep.schema.split("-")[2].split("[")[0]


import pickle


def upload(plan_steps, name):
	# n = re.sub('[^A-Za-z0-9]+', '', name)
	print(name)
	with open(name, 'wb') as afile:
		pickle.dump(plan_steps, afile)

def reload(name):
	# n = re.sub('[^A-Za-z0-9]+', '', name)
	afile = open(name, "rb")
	plan_steps = pickle.load(afile)
	afile.close()
	return plan_steps


FAB_METHODS = {
	"strut": nav_act_to_json,
	"turn-to": stationary_act_to_json
}

DISC_METHODS = {
	"navigate":
		{
			"virtual": nav_virtual_shot_to_json,
		    "shot": nav_cam_shot_to_json
		},
	"stationary":
		{
			"virtual": None,
			"shot": None
		}
}

if __name__ ==  '__main__':

	domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_Arrive1.pddl'
	problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Arrive_Problem.pddl'

	# plan_output, gsteps = plan_single_example(domain_file, problem_file)
	# plan_steps = [step for step in plan_output[0].OrderingGraph.topoSort()]

	# upload(plan_steps, "plan")
	# plan_steps = reload("cached_plan_CA5.pkl")
	# plan_steps = reload("cached_plan_Arrive.pkl")
	plan = reload("full_plan_Arrive.pkl")
	fab_partial_ordering = make_partial_ordered_list(plan, FAB_STEPS)

	#
	# print("organize into partial order")
	# # plan_steps = [step for step in plan_output.OrderingGraph.topoSort()]
	# with open("arrival_plan.txt", 'w') as wtp:
	# 	for step in plan_steps:
	# 		wtp.write(str(step))
	# 		wtp.write("\n")
	#
	# print("ok")

	plan_steps = [step for step in plan.OrderingGraph.topoSort()]
	fab_steps, disc_steps = step_extraction(plan_steps)

	fab_list = fabula_to_json_po(set(plan_steps[0].effects), fab_partial_ordering)
	# fab_list = fabula_to_json(set(plan_steps[0].effects), fab_steps)

	disc_list = discourse_to_json(disc_steps, fab_list)

	# tree_string = etree.tostring(root, pretty_print=True)
	# fab_string = json.dumps(fab_xml)

	# fab_string = etree.tostring(fab_xml, pretty_print=True)
	with open("fabula.json", 'w') as tout:
		tout.write(json.dumps(fab_list, indent=4))

	# disc_string = etree.tostring(disc_xml, pretty_print=True)
	with open("discourse.json", 'w') as tout:
		tout.write(json.dumps(disc_list, indent=4))