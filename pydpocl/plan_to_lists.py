# two typed lists: partial order list and total order list, that way they both behave like lists

from collections import namedtuple
import pickle

PartialOrderList = namedtuple("PO", "list")
TotalOrderList = namedtuple("TO", "list")

def reload(name):
	afile = open(name, "rb")
	plan_steps = pickle.load(afile)
	afile.close()
	return plan_steps

# FAB_STEPS = ["strut", "turn-to"]

def make_partial_ordered_list(plan, FAB_STEPS):
	fab_steps = [step for step in plan.steps if step.schema.split("-")[0] in FAB_STEPS]

	po_pairs = []
	to_pairs = []

	for fs in fab_steps:
		for os in fab_steps:

			if os == fs:
				continue
			if (fs, os) in po_pairs or (os, fs) in po_pairs or (fs, os) in to_pairs or (os, fs) in to_pairs:
				continue

			if plan.OrderingGraph.isPath(fs, os):
				to_pairs.append((fs, os))
			elif plan.OrderingGraph.isPath(os, fs):
				to_pairs.append((os, fs))
			else:
				po_pairs.append((fs, os))

	plan_steps = [step for step in plan.OrderingGraph.topoSort() if step.schema.split("-")[0] in FAB_STEPS]
	partial_ordering = []
	for step in plan_steps:
		po_partners = []
		for s, t in po_pairs:
			if s != step and t != step:
				continue
			if s == step:
				if len(partial_ordering) > 0 and t in partial_ordering[-1]:
					continue
				po_partners.append(t)
				for existing_step in po_partners:
					if plan.OrderingGraph.isPath(existing_step, t):
						continue
					elif plan.OrderingGraph.isPath(t, existing_step):
						po_partners.remove(existing_step)
			elif t == step:
				if len(partial_ordering) > 0 and s in partial_ordering[-1]:
					continue
				po_partners.append(s)
				for existing_step in po_partners:
					if plan.OrderingGraph.isPath(existing_step, s):
						continue
					elif plan.OrderingGraph.isPath(s, existing_step):
						po_partners.remove(existing_step)
		if len(po_partners) == 0 and len(partial_ordering[-1]) > 0 and step in partial_ordering[-1]:
			continue
		partial_ordering.append(po_partners + [step])
	return partial_ordering

if __name__ == "__main__":
	plan = reload("full_plan_Arrive.pkl")
	po = make_partial_ordered_list(plan, FAB_STEPS=["strut", "turn-to"])