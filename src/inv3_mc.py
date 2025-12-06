# check outputs, probably i missed smth
import pynusmv
import sys
from typing import Tuple, Optional, Dict, List, Any

def spec_to_bdd(model, spec):
    return pynusmv.mc.eval_ctl_spec(model, spec)

def check_explain_inv_spec(spec) -> Tuple[bool, Optional[Tuple[Dict[str, str], ...]]]:
    """
    BFS reachability to check invariant on all states satisfy the invariant specification

    Return:
        Tuple:
        - True if all reachable states satisfy the invariant, False otherwise
        - trace is None if True, counterexample execution if False

        Execution trace is a tuple of states and inputs, starting and ending with a state.
        Each state and input is represented as a dictionary mapping variable names to their string values.
    """
    fsm_model = pynusmv.glob.prop_database().master.bddFsm

    spec_as_bdd = spec_to_bdd(fsm_model, spec)
    negated_spec = ~spec_as_bdd

    def satisfy_spec(states):
        return states.intersection(negated_spec).is_false()

    reached = fsm_model.init
    current_states = fsm_model.init
    trace_layers = [reached]

    while not current_states.is_false() and satisfy_spec(current_states):
        successors = fsm_model.post(current_states)
        current_states = successors - reached
        reached = reached + current_states
        trace_layers.append(current_states)

    if satisfy_spec(current_states):
        return True, None

    invalid_states = current_states.intersection(negated_spec)
    last_state = fsm_model.pick_one_state(invalid_states)

    counterexample = [last_state.get_str_values()]
    has_inputs = len(fsm_model.bddEnc.inputsVars) > 0
    next_state = last_state
    possible_predecessors = fsm_model.pre(next_state)

    # Build counterexample backwards using trace layers
    for layer in reversed(trace_layers[:-1]):
        intersect = layer.intersection(possible_predecessors)
        if intersect.is_false():
            continue

        chosen_pre = fsm_model.pick_one_state(intersect)

        if has_inputs:
            inputs_between = fsm_model.get_inputs_between_states(chosen_pre, next_state)
            picked_inputs = fsm_model.pick_one_inputs(inputs_between)
            counterexample.insert(0, picked_inputs.get_str_values())
        else:
            counterexample.insert(0, {})

        counterexample.insert(0, chosen_pre.get_str_values())

        next_state = chosen_pre
        possible_predecessors = fsm_model.pre(next_state)

    return False, tuple(counterexample)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]

    try:
        pynusmv.glob.load_from_file(filename)
    except OSError as e:
        print(f"Error: Could not load file '{filename}': {e}")
        pynusmv.init.deinit_nusmv()
        sys.exit(1)

    pynusmv.glob.compute_model()
    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            res, trace = check_explain_inv_spec(spec)
            if res == True:
                print("Invariant is respected")
            else:
                print("Invariant is not respected")
                print(trace)
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

    pynusmv.init.deinit_nusmv()
