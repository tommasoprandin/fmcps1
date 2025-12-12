# slightly different approach
import pynusmv
import sys
from typing import Tuple, Optional, Dict, List, Any

def spec_to_bdd(model, spec):
    # Return the set of states of `model` satisfying `spec`, as a BDD.
    return pynusmv.mc.eval_ctl_spec(model, spec)

def check_explain_inv_spec(spec) -> Tuple[bool, Optional[Tuple[Dict[str, str], ...]]]:
    # Check whether the loaded SMV model satisfies the invariant `spec`.
    # Returns: (result, trace)
    fsm_model = pynusmv.glob.prop_database().master.bddFsm

    spec_as_bdd = spec_to_bdd(fsm_model, spec)
    negated_spec = ~spec_as_bdd

    def satisfy_spec(states):
        # Check if all states in the given BDD satisfy the invariant.
        return states.intersection(negated_spec).is_false()

    reached = fsm_model.init
    current_states = fsm_model.init
    trace_layers = [reached]

    # Keep exploring state space until either there are no new successors or
    # there are states violating the spec
    while not current_states.is_false() and satisfy_spec(current_states):
        successors = fsm_model.post(current_states)
        current_states = successors - reached
        reached = reached + current_states
        # Add the visited successive regions to a list so we can do backtracking later
        trace_layers.append(current_states)

    # Exited the loop because we reached a fixpoint => The spec is an invariant
    if satisfy_spec(current_states):
        return True, None

    # There are states violating the property. We need to find a witness.
    invalid_states = current_states.intersection(negated_spec)
    last_state = fsm_model.pick_one_state(invalid_states)

    # Initialize witness trace
    counterexample = [last_state.get_str_values()]
    has_inputs = len(fsm_model.bddEnc.inputsVars) > 0
    next_state = last_state

    # Backtrack using the traversed layers during forward traversal
    for layer in reversed(trace_layers[:-1]):
        # Intersect chosen state predecessors with the layers at depth n-1, so we avoid entering loops and
        # we get a shortest trace from init to a final state violating the spec.
        possible_predecessors = fsm_model.pre(next_state)
        intersect = layer.intersection(possible_predecessors)

        # It should not happen in a valid back-traversal
        if intersect.is_false():
            continue

        chosen_pre = fsm_model.pick_one_state(intersect)

        # Pick any set of inputs (if some) that resulted in a transaction between the chosen predecessor and the current state.
        if has_inputs:
            inputs_between = fsm_model.get_inputs_between_states(chosen_pre, next_state)
            picked_inputs = fsm_model.pick_one_inputs(inputs_between)
            # Cover the case where there were no picked inputs (should not happen for a valid transition)
            if picked_inputs:
                counterexample.insert(0, picked_inputs.get_str_values())
            else:
                counterexample.insert(0, {})
        else:
            counterexample.insert(0, {})

        counterexample.insert(0, chosen_pre.get_str_values())

        next_state = chosen_pre

    # Return the witness execution
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
