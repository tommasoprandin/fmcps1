# Elia
import pynusmv
import sys

def spec_to_bdd(model, spec):
    """
    Return the set of states of model satisfying spec, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def check_explain_inv_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the invariant spec,
    that is, whether all reachable states of the model satisfies spec or not.
    Return also an explanation for why the model does not satisfy spec, if it is the case.
    The result is a tuple (bool, trace) as described in the assignment.
    """
    fsm_model = pynusmv.glob.prop_database().master.bddFsm
    spec_as_bdd = spec_to_bdd(fsm_model, spec)
    negated_spec = -spec_as_bdd

    def satisfy_spec(states):
        # True if all states in 'states' satisfy the spec
        return not states.intersected(negated_spec)

    reached = fsm_model.init
    current_states = fsm_model.init
    trace = [reached]

    while current_states.isnot_false() and satisfy_spec(current_states):
        current_states = fsm_model.post(current_states) - reached
        reached = reached + current_states
        trace.append(current_states)

    is_satisfied = satisfy_spec(current_states)

    if is_satisfied:
        return True, None

    invalid_states = current_states.intersection(negated_spec)
    last_state = fsm_model.pick_one_state(invalid_states)
    counter_example = [last_state.get_str_values()]

    has_inputs = len(fsm_model.bddEnc.inputsVars) > 0
    next_state = last_state
    possible_previous_states = fsm_model.pre(next_state)

    for current in reversed(trace[:-1]):
        intersect = current.intersection(possible_previous_states)
        chosen_pre = fsm_model.pick_one_state(intersect)

        if has_inputs:
            inputs = fsm_model.get_inputs_between_states(chosen_pre, next_state)
            counter_example.insert(0, fsm_model.pick_one_inputs(inputs).get_str_values())
        else:
            counter_example.insert(0, {})

        counter_example.insert(0, chosen_pre.get_str_values())

        next_state = chosen_pre
        possible_previous_states = fsm_model.pre(next_state)

    return False, tuple(counter_example)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
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
