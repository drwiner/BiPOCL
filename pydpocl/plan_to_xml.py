"""
Read plan solution, use time table to coordinate times
"""
from lxml import etree
from CacheGroundSteps import plan_single_example

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

FAB_GAMEOBJECT_ARG = {"strut": 0, "turn-to": 0}

FAB_STEPS = ["strut", "turn-to"]
# ANIM_MAP = {"strut": "Stroll"}
FAB_TYPES = {"strut": "navigate"}

ORIENTS = {"front": '0', "behind": "180", "behind-right": 150}

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

# FAB_STEPS = ["strut", "turn-to"]
# ANIM_MAP = {"strut": "Stroll"}
# FAB_TYPES = {"strut": "navigate"}

def nav_step_to_xml(state, step, step_token, begin_time):
	which_arg = FAB_GAMEOBJECT_ARG[step_token]
	gameobj = step.Args[which_arg].name
	origin, dest = NAV_ARGS[step_token]
	duration = dist_dict[(step.Args[origin].name, step.Args[dest].name)] / NAV_MOVE_RATE[step_token]
	location = "None"
	for lit in state:
		if lit.name != "at" or lit.truth is False:
			continue
		if lit.Args[0] != step.Args[which_arg]:
			continue
		location = lit.Args[1].name
		break
	ending_loc = "None"
	for eff in step.effects:
		if eff.name == "at" and eff.Args[0].name == gameobj and eff.truth is True:
			ending_loc = eff.Args[1].name
			break

	step_root = etree.Element("Clip", name=step.schema, type=FAB_TYPES[step_token])
	etree.SubElement(step_root, "start").text = str(begin_time)
	etree.SubElement(step_root, "duration").text = str(duration)
	etree.SubElement(step_root, "startingPos_string").text = location
	etree.SubElement(step_root, "endingPos_string").text = ending_loc
	etree.SubElement(step_root, "animation_string").text = step_token
	etree.SubElement(step_root, "gameobject_name").text = gameobj
	return step_root, duration



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


def fabula_to_xml(init, steps):
	fab_timeline = []
	collection_root = etree.Element("FabulaCollection")
	plan_root = etree.Element("Clips")
	collection_root.append(plan_root)
	before_time = 0

	before_state = init
	for step in steps:
		step_tokens = step.schema.split("-")[:2]
		# step_with_num = step_tokens[0] + "-" + step_tokens[1]
		xml_method = FAB_METHODS[step_tokens[0]]

		# e.g.:  nav_step_to_xml   (state, step, step_token, begin_time, duration)
		sub_root, step_duration = xml_method(before_state, step, step_tokens[0], before_time)
		fab_timeline.append((before_time, fab_step_to_id(step), step, sub_root))
		before_state = transition_state(before_state, step)
		before_time += step_duration
		plan_root.append(sub_root)

	return collection_root, fab_timeline


def discourse_to_xml(steps, fab_timeline):
	collection_root = etree.Element("DiscourseCollection")
	plan_root = etree.Element("Clips")
	collection_root.append(plan_root)
	before_time = 0
	for step in steps:
		# cam - shot - segment
		step_tokens = step.schema.split("-")
		segment = step_tokens[2]
		# if "cam-shot" then the argument signature is step +
		fab_step_ref = step.Args[0]
		step_id_query = str(fab_step_ref.root.ID)[19:23]
		fab_start_time, fab_gstep, fab_xml = get_fabxml_from_timeline(step_id_query, fab_timeline)
		target = list(fab_xml.getiterator("gameobject_name"))[0].text

		arg_dict = {}
		for arg in step.Args:
			if arg.typ == "Action":
				arg_dict[arg.root.p_types[0]] = arg.root.name
			else:
				arg_dict[arg.p_types[0]] = arg.name

		""" Customized Extraction - need to standardize for when multiple values, or when values not present
		"""
		orient = ORIENTS[arg_dict["orient"]]
		# fab_xml.

		xml_method = DISC_METHODS[fab_xml.attrib["type"]]
		step_root, this_duration = xml_method(before_time, fab_gstep, orient, segment, target, fab_start_time, fab_xml)
		# step_root = xml_method(step.schema, before_time, this_duration, this_fab_start_time, orient, target, fab_xml)
		plan_root.append(step_root)

		before_time += this_duration
	return collection_root


def nav_cam_shot_to_xml(before_time, fab_gstep, orient, segment, target, fab_start_time, fab_xml):
# schema_name, before_time, shot_duration, fab_start, orient, aim_target, fab_xml):
	fab_tokens = fab_gstep.schema.split("-")
	# fab_with_num = fab_tokens[0] + "-" + fab_tokens[1]
	s, f = FAB_SEGMENTS[fab_tokens[0]][segment]
	fab_duration = list(fab_xml.getiterator("duration"))[0].text
	this_duration = f * float(fab_duration) - s * float(fab_duration)
	this_fab_start_time = fab_start_time + s * float(fab_duration)

	step_root = etree.Element("Clip", name=fab_gstep.schema, type="nav_cam")
	etree.SubElement(step_root, "start").text = str(before_time)
	etree.SubElement(step_root, "duration").text = str(this_duration)
	etree.SubElement(step_root, "fov").text = str(25)
	etree.SubElement(step_root, "fabulaStart").text = str(this_fab_start_time)

	# first, get the start and end locations of the navigate fabula step
	fab_location_start = list(fab_xml.getiterator("startingPos_string"))[0].text
	fab_location_end = list(fab_xml.getiterator("endingPos_string"))[0].text
	# then, calculate the offset into the fabula step to calculate where the agent will be at the start and end of the shot
	dist = dist_dict[(fab_location_start, fab_location_end)]
	# dist_covered = f*dist - s*dist

	etree.SubElement(step_root, "startingPos_string").text = fab_location_start
	etree.SubElement(step_root, "start_dist_offset").text = str(s*dist)
	etree.SubElement(step_root, "endingPos_string").text = fab_location_end
	etree.SubElement(step_root, "end_dist_offset").text = str(f*dist)
	# starting pos
	# ending pos
	etree.SubElement(step_root, "targetOrientation").text = str(orient)
	etree.SubElement(step_root, "aimTarget").text = str(target)
	return step_root, this_duration


def get_fabxml_from_timeline(fab_step_id, fab_timeline):
	fab_step_in_fab_timeline = None
	for bt, fab_id, fab_step, fab_step_xml in fab_timeline:
		if fab_id == fab_step_id:
			fab_step_in_fab_timeline = fab_step_xml
			break
	if fab_step_in_fab_timeline is None:
		print('initiaiting a hack')
		fab_step_in_fab_timeline = fab_timeline[0][3]
		fab_step = fab_timeline[0][2]
		bt = fab_timeline[0][0]
	return bt, fab_step, fab_step_in_fab_timeline


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



FAB_METHODS = {"strut": nav_step_to_xml, "turn-to": "animate"}
DISC_METHODS = {"navigate": nav_cam_shot_to_xml}

if __name__ ==  '__main__':

	domain_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Domain_ContAct3.pddl'
	problem_file = 'D:/documents/python/cinepydpocl/pydpocl/Ground_Compiler_Library/domains/Unity_Cntg_Problem.pddl'

	# plan_output, gsteps = plan_single_example(domain_file, problem_file)
	# plan_steps = [step for step in plan_output[0].OrderingGraph.topoSort()]

	# upload(plan_steps, "plan")
	plan_steps = reload("cached_plan_CA5.pkl")
	# plan_steps = [step for step in plan_output.OrderingGraph.topoSort()]
	print("ok")


	fab_steps, disc_steps = step_extraction(plan_steps)
	fab_xml, fab_timeline = fabula_to_xml(set(plan_steps[0].effects), fab_steps)

	disc_xml = discourse_to_xml(disc_steps, fab_timeline)

	# tree_string = etree.tostring(root, pretty_print=True)
	fab_string = etree.tostring(fab_xml, pretty_print=True)
	with open("fabula.xml", 'wb') as tout:
		tout.write(fab_string)

	disc_string = etree.tostring(disc_xml, pretty_print=True)
	with open("discourse.xml", 'wb') as tout:
		tout.write(disc_string)