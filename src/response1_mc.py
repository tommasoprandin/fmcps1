# based on Elia, logic-related bugs, can be fixed
import sys
from collections import deque
import pynusmv
from pynusmv_lower_interface.nusmv.parser import parser

SPEC_TYPES = {
    'LTLSPEC': parser.TOK_LTLSPEC,
    'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES,
    'IFF': parser.IFF,
    'OR': parser.OR,
    'XOR': parser.XOR,
    'XNOR': parser.XNOR,
    'AND': parser.AND,
    'NOT': parser.NOT,
    'ATOM': parser.ATOM,
    'NUMBER': parser.NUMBER,
    'DOT': parser.DOT,
    'NEXT': parser.OP_NEXT,
    'OP_GLOBAL': parser.OP_GLOBAL,
    'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL,
    'NOTEQUAL': parser.NOTEQUAL,
    'LT': parser.LT,
    'GT': parser.GT,
    'LE': parser.LE,
    'GE': parser.GE,
    'TRUE': parser.TRUEEXP,
    'FALSE': parser.FALSEEXP
}

BASIC_TYPES = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
               parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}

BOOLEAN_OPS = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}

# BDD conversion cache
_bdd_cache = {}

def spec_to_bdd(model, spec):
    # boolean formula with no temporal operators -> BDD
    key = str(spec)
    if key not in _bdd_cache:
        _bdd_cache[key] = pynusmv.mc.eval_simple_expression(model, key)
    return _bdd_cache[key]

def is_boolean_formula(spec) -> bool:
    # Checks if formula is a boolean combination of basic formulas (no temporal operators)
    if spec.type in BASIC_TYPES:
        return True
    if spec.type == SPEC_TYPES['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in BOOLEAN_OPS:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False

def get_GF_formula(spec):
    # Returns inner formula of GF f if spec is of the form GF f, else None
    if spec.type != SPEC_TYPES['OP_GLOBAL']:
        return None
    inner = spec.car
    if inner.type != SPEC_TYPES['OP_FUTURE']:
        return None
    inner = inner.car
    return inner if is_boolean_formula(inner) else None

def get_implication(spec):
    # Returns (f, g) if spec is GF f -> GF g, else None
    if spec.type != SPEC_TYPES['IMPLIES']:
        return None
    f = get_GF_formula(spec.car)
    g = get_GF_formula(spec.cdr)
    if f is None or g is None:
        return None
    return f, g

def parse_react(spec):
    # Parses a reactivity formula of the form (GF f1 -> GF g1) & ... & (GF fn -> GF gn)
    # !!! Elia's approach, not the one that stated in the problem
    if spec.type != SPEC_TYPES['CONTEXT']:
        return None
    main_formula = spec.cdr
    working = deque([main_formula])
    conjuncts = []

    while working:
        head = working.pop()
        if head.type == SPEC_TYPES['AND']:
            working.append(head.car)
            working.append(head.cdr)
        else:
            imp = get_implication(head)
            if imp is None:
                return None
            conjuncts.append(imp)
    return conjuncts

# Symbolic reachability and counterexample
def compute_reach(fsm_model):
    # Reachable states and frontier sets
    reach = fsm_model.init
    new = fsm_model.init
    reached_frontiers = [new]

    while not new.is_false():
        post = fsm_model.post(new)
        new = post - reach
        reached_frontiers.append(new)
        reach = reach + new

    return reach, reached_frontiers

def find_knot(fsm_model, recur, pre_reach):
    # Finds a knot state for building lasso-shaped counterexamples
    attempts = 0
    max_attempts = 100
    s = fsm_model.pick_one_state(recur)
    R = pynusmv.dd.BDD.false()

    while attempts < max_attempts:
        post = fsm_model.post(s)
        new = post & pre_reach
        loop_frontiers = [new]

        while not new.is_false():
            R = R + new
            post = fsm_model.post(new)
            new = post & pre_reach
            new = new - R
            loop_frontiers.append(new)

        R = R & recur
        if s.entailed(R):
            return s, loop_frontiers

        s = fsm_model.pick_one_state(R)
        attempts += 1

    raise RuntimeError("No knot found within maximum attempts")

def build_counterexample(fsm_model, recur, pre_reach, reached_frontiers):
    # lasso-shaped counterexample from recur and pre_reach
    knot, loop_frontiers = find_knot(fsm_model, recur, pre_reach)

    # Loop construction
    valid_loop_frontiers = [f for f in loop_frontiers if knot.entailed(f)]
    cycle_trace = [knot.get_str_values()]
    curr_state = knot

    for loop_frontier in reversed(valid_loop_frontiers[:-1]):
        pre_states = fsm_model.pre(curr_state) & loop_frontier
        picked_pre_state = fsm_model.pick_one_state(pre_states)
        possible_inputs = fsm_model.get_inputs_between_states(pre_states, curr_state)
        picked_input = fsm_model.pick_one_inputs(possible_inputs) if not possible_inputs.is_false() else {}
        cycle_trace.insert(0, picked_input.get_str_values() if picked_input else {})
        cycle_trace.insert(0, picked_pre_state.get_str_values())
        curr_state = picked_pre_state

    # Prefix construction
    valid_reach_frontiers = [f for f in reached_frontiers if knot.entailed(f)]
    prefix_trace = []
    curr_state = knot
    for reach_frontier in reversed(valid_reach_frontiers[:-1]):
        pre_states = fsm_model.pre(curr_state) & reach_frontier
        picked_pre_state = fsm_model.pick_one_state(pre_states)
        possible_inputs = fsm_model.get_inputs_between_states(picked_pre_state, curr_state)
        picked_input = fsm_model.pick_one_inputs(possible_inputs) if not possible_inputs.is_false() else {}
        prefix_trace.insert(0, picked_input.get_str_values() if picked_input else {})
        prefix_trace.insert(0, picked_pre_state.get_str_values())
        curr_state = picked_pre_state

    return prefix_trace + cycle_trace

def check_repeatability(fsm_model, bdd_f, bdd_not_g, reach, reached_frontiers):
    # Checks if F and not G is repeatable in the reachable states
    recur = reach & bdd_f & bdd_not_g

    while not recur.is_false():
        pre = fsm_model.pre(recur)
        new = pre & bdd_not_g
        pre_reach = pynusmv.dd.BDD.false()

        while not new.is_false():
            pre_reach = pre_reach + new
            if recur.entailed(pre_reach):
                counterexample = build_counterexample(fsm_model, recur, pre_reach, reached_frontiers)
                return False, counterexample
            pre = fsm_model.pre(new)
            new = (pre & bdd_not_g) - pre_reach

        recur = recur & pre_reach

    return True, None

# Reactivity check
def check_explain_react_spec(spec):
    # Checks whether a reactivity formula is satisfied and returns a counterexample
    fsm_model = pynusmv.glob.prop_database().master.bddFsm
    conjuncts = parse_react(spec)
    if conjuncts is None:
        return None

    reach, reached_frontiers = compute_reach(fsm_model)

    for f, g in conjuncts:
        bdd_f = spec_to_bdd(fsm_model, f)
        bdd_g = spec_to_bdd(fsm_model, g)
        bdd_not_g = ~bdd_g

        reachable, counterexample = check_repeatability(fsm_model, bdd_f, bdd_not_g, reach, reached_frontiers)
        if not reachable:
            return False, counterexample

    return True, None

def print_counterexample(trace):
    if not trace:
        print("No counterexample.")
        return
    for i, step in enumerate(trace):
        if i % 2 == 0:
            print(f"State {i//2}: {step}")
        else:
            print(f"  Input: {step}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        print(spec)
        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        res = check_explain_response_spec(spec)
        if res == None:
            print('Property is not a response formula, skipping')
        elif res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])

    pynusmv.init.deinit_nusmv()
