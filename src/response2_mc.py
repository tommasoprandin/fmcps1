# 
import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser
from typing import Tuple, Optional, Dict, List, Any

specTypes = {'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
             'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
             'AND': parser.AND, 'NOT': parser.NOT, 'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,
             'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE,
             'UNTIL': parser.UNTIL,
             'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL, 'LT': parser.LT, 'GT': parser.GT,
             'LE': parser.LE, 'GE': parser.GE, 'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP
             }

basicTypes = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
              parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}
booleanOp = {parser.AND, parser.OR, parser.XOR,
             parser.XNOR, parser.IMPLIES, parser.IFF}

def spec_to_bdd(model, spec):
    # expression (no temporal operators) -> BDD
    return pynusmv.mc.eval_simple_expression(model, str(spec))

def is_boolean_formula(spec):
    # Checks if spec is a boolean combination of basic formulas
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False

def parse(spec):
    # Parser for Response properties: G(f -> F g)
    # Returns (f_formula, g_formula) if 'spec' matches, else None
    if spec.type != specTypes['CONTEXT']:
        return None
    spec = spec.cdr

    if spec.type != specTypes['OP_GLOBAL']: # Must be G(...)
        return None
    spec = spec.car

    if spec.type != specTypes['IMPLIES']: # Must be f -> ...
        return None

    f_formula = spec.car
    if not is_boolean_formula(f_formula):
        return None

    g_formula = spec.cdr
    if g_formula.type != specTypes['OP_FUTURE']: # Must be F g
        return None
    g_formula = g_formula.car

    if not is_boolean_formula(g_formula):
        return None

    return (f_formula, g_formula)

def _compute_reachable(fsm_model) -> Tuple[pynusmv.dd.BDD, List[pynusmv.dd.BDD]]:
    # Set of reachable states (R) using forward BFS
    # Returns (R, trace_layers).
    R = fsm_model.init
    F = fsm_model.init
    trace_layers = [F]

    while not F.is_false():
        F_next = fsm_model.post(F) - R
        if F_next.is_false():
            break
        trace_layers.append(F_next)
        R = R + F_next
        F = F_next

    return R, trace_layers

def _compute_eg(fsm_model, bdd_prop) -> pynusmv.dd.BDD:
    # Set of states satisfying EG(bdd_prop).
    # Fixed Point: Z = bdd_prop & EX(Z)
    Z = bdd_prop
    while True:
        pre_Z = fsm_model.pre(Z)
        next_Z = bdd_prop & pre_Z

        if next_Z == Z:
            return Z
        Z = next_Z

def _build_prefix_trace(fsm_model, trace_layers, violating_state_bdd) -> List[Dict[str, str]]:
    # Prefix of a counterexample from Init to violating_state_bdd
    last_state = violating_state_bdd
    counterexample_list = [last_state.get_str_values()]

    has_inputs = len(fsm_model.bddEnc.inputsVars) > 0
    curr_state_bdd = last_state

    # Iterate backwards to find the path
    for layer in reversed(trace_layers[:-1]):
        # predecessor of 'curr' in current 'layer'
        possible_predecessors = fsm_model.pre(curr_state_bdd) & layer

        if possible_predecessors.is_false():
            continue

        prev_state_bdd = fsm_model.pick_one_state(possible_predecessors)

        if has_inputs:
            inputs_between = fsm_model.get_inputs_between_states(prev_state_bdd, curr_state_bdd)
            picked_inputs = fsm_model.pick_one_inputs(inputs_between)
            counterexample_list.insert(0, picked_inputs.get_str_values())
        else:
            counterexample_list.insert(0, {})

        counterexample_list.insert(0, prev_state_bdd.get_str_values())
        curr_state_bdd = prev_state_bdd

    return counterexample_list


def check_explain_response_spec(spec):
    # Checks a Response property G(f -> F g)
    fsm_model = pynusmv.glob.prop_database().master.bddFsm

    parsed = parse(spec)
    if parsed is None:
        return None

    f_formula, g_formula = parsed

    bdd_f = spec_to_bdd(fsm_model, f_formula)
    bdd_g = spec_to_bdd(fsm_model, g_formula)
    bdd_not_g = ~bdd_g

    bdd_eg_not_g = _compute_eg(fsm_model, bdd_not_g)

    bdd_bad_states = bdd_f & bdd_eg_not_g

    if bdd_bad_states.is_false():
        return (True, None)

    reachable_states, trace_layers = _compute_reachable(fsm_model)
    violation_states = reachable_states & bdd_bad_states

    if violation_states.is_false():
        return (True, None)


    # Pick reachable violation
    s_violation_bdd = fsm_model.pick_one_state(violation_states)

    # prefix trace (Init -> ... -> s_violation)
    prefix_trace_list = _build_prefix_trace(fsm_model, trace_layers, s_violation_bdd)

    # loop (s_violation -> ... -> s_loop)
    has_inputs = len(fsm_model.bddEnc.inputsVars) > 0
    loop_list = []
    curr_bdd = s_violation_bdd

    states_on_path = [prefix_trace_list[i] for i in range(0, len(prefix_trace_list), 2)]

    while True:
        # Find a successor in EG(¬g)
        possible_successors = fsm_model.post(curr_bdd) & bdd_eg_not_g

        if possible_successors.is_false():
            print("Strange")
            return (False, tuple(prefix_trace_list))

        next_bdd = fsm_model.pick_one_state(possible_successors)
        next_dict = next_bdd.get_str_values()

        # Inputs
        if has_inputs:
            inputs_between = fsm_model.get_inputs_between_states(curr_bdd, next_bdd)
            picked_inputs = fsm_model.pick_one_inputs(inputs_between)
            loop_list.append(picked_inputs.get_str_values())
        else:
            loop_list.append({})

        loop_list.append(next_dict)

        # loop closed check
        if next_dict in states_on_path:
            full_trace = prefix_trace_list + loop_list
            return (False, tuple(full_trace))

        states_on_path.append(next_dict)
        curr_bdd = next_bdd

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    try:
        pynusmv.glob.load_from_file(filename)
        pynusmv.glob.compute_model()
    except OSError as e:
        print(f"Error loading file: {e}")
        pynusmv.init.deinit_nusmv()
        sys.exit(1)

    type_ltl = pynusmv.prop.propTypes['LTL']

    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        print(f"\n Checking property: {spec} ")

        if prop.type != type_ltl:
            print("not LTLSPEC, skip")
            continue

        res = check_explain_response_spec(spec)

        if res is None:
            print("Result: NOT a Response formula, skip")
        elif res[0] == True:
            print("Result: RESPECTED")
        elif res[0] == False:
            print("Result: NOT RESPECTED")
            print("Counterexample:")

            trace = res[1]
            loop_start_index = -1
            last_state = trace[-1]

            for i in range(0, len(trace) - 2, 2):
                if trace[i] == last_state:
                    loop_start_index = i
                    break

            for i, step in enumerate(trace):
                if loop_start_index != -1 and i == loop_start_index:
                    print("Loop starts here")

                if i % 2 == 0:
                    print(f"  State {i//2}: {step}")
                else:
                    print(f"  Input:    {step}")
            if loop_start_index != -1:
                print(f"  -- Loops back to State {loop_start_index//2} --")

    pynusmv.init.deinit_nusmv()
