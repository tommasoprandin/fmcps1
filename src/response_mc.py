
import sys
import pynusmv
from pynusmv_lower_interface.nusmv.parser import parser 

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
booleanOp = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}

def spec_to_bdd(model, spec):
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec

def is_boolean_formula(spec):
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False

def parse(spec):
    """
    Visit the syntactic tree of the formula `spec` to check if it is a response formula,
    that is wether the formula is of the form

                    G (f -> F g)

    where f and g are boolean combination of basic formulas.

    If `spec` is a response formula, the result is a pair where the first element is the 
    formula f and the second element is the formula g. If `spec` is not a response 
    formula, then the result is None.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # the root of a response formula should be of type OP_GLOBAL 
    if spec.type != specTypes['OP_GLOBAL']:
        return None
    # The formula in the scope of the G operator must be of type IMPLIES
    spec = spec.car
    if spec.type != specTypes['IMPLIES']:
        return None
    # Check if lhs of the implication is a formula with no temporal operators
    f_formula = spec.car
    if not is_boolean_formula(f_formula):
        return None
    # Check if rhs of the implication is a F g formula
    g_formula = spec.cdr
    if g_formula.type != specTypes['OP_FUTURE']:
        return None
    g_formula = g_formula.car
    if not is_boolean_formula(g_formula):
        return None
    return (f_formula, g_formula)

def check_explain_response_spec(spec):
    """
    Return whether the loaded SMV model satisfies or not the GR(1) formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. 
    """
    # Parse the formula to check whether they are a response formula
    formulas = parse(spec)
    if formulas == None:
        return None
    f, g = formulas

    # We only need to check a response property G(f -> F g), where f and g are simple expressions with
    # no temporal operators. Hence we need to check that the negation F(f & G(!g)) happens.
    # If this is the case, then we know that the system does not satisfy the spec and we need to return a witness.

    # Get the model
    model = pynusmv.glob.prop_database().master.bddFsm

    # Obtain all states of the model that satisfy f and g
    states_f = spec_to_bdd(model, f)
    states_not_g = spec_to_bdd(model, ~g)

    # Now compute all reachable states, starting from init
    reach = model.init
    current = model.init
    reach_frontiers = [model.init]

    while not (model.post(current) - reach).is_false():
        new = model.post(current) - reach
        reach_frontiers.append(new)
        reach = reach + new
        current = new

    # At this point get all reachable states where f is satisfied and g is not.
    # This region will be our starting point for cycle detection
    reach_states_f_not_g = reach & states_f & states_not_g
    if reach_states_f_not_g.is_false(): # Trivially holds
        return True, None

    # We now need to check if, starting from the found states, there are cycles where g never holds
    # To do so we keep expanding the recur set until we reach a fix-point or the empty set
    recur = reach_states_f_not_g
    compliant = True
    while not recur.is_false() and compliant:
        pre_reach = pynusmv.dd.BDD.false() # empty set
        new = model.pre(recur) & states_not_g
        while not new.is_false():
            pre_reach = pre_reach + new
            if recur.entailed(pre_reach): # recur is included in pre_reach
                compliant = False # Recur is a fix-point => There is a cycle where in all states not g holds
                break
            new = (model.pre(new) & states_not_g) - pre_reach
        recur = recur & pre_reach

    if compliant:
        return True, None

    # We have found a violation, we now need to provide a witness.
    has_inputs = len(model.bddEnc.inputsVars) > 0

    # First we need to find a state in the obtained recur such that we can build a loop to 
    # itself only using states in PreReach, keeping track of frontiers
    candidates = recur # need to remove failed attempts 
    s = model.pick_one_state(candidates)
    found = False
    while not found:
        frontiers = [] # Reset frontiers for each attempt
        r = pynusmv.dd.BDD.false()
        new = model.post(s) & pre_reach
        while not new.is_false():
            frontiers.append(new)
            r = r + new
            new = model.post(new) & pre_reach
            new = new - r
        r = r & recur
        if s.entailed(r): # s in R
            found = True
        else:
            s = model.pick_one_state(r)


    # Now we find the frontier to which the found s belongs, and going backwards
    # we then build a loop to itself
    k = 0
    for i, frontier in enumerate(frontiers):
        if s.entailed(frontier): # s in frontier
            k = i
            break
    # Go back from s to s using the frontiers
    trace = [ s.get_str_values() ]
    current_state = s
    for frontier in reversed(frontiers[:k]): # exclude the k-th element where s already is
        predecessors = model.pre(current_state) & frontier
        pred = model.pick_one_state(predecessors)
        if has_inputs:
            inputs = model.get_inputs_between_states(pred, current_state)
            picked_inputs = model.pick_one_inputs(inputs)
            # Cover the case where there were no picked inputs (can't happen for a valid transition)
            trace.insert(0, picked_inputs.get_str_values() if picked_inputs else {})
        else:
            trace.insert(0, {})
        trace.insert(0, pred.get_str_values())
        current_state = pred
    # finally append s at the end (start) of the loop
    if has_inputs:
        inputs = model.get_inputs_between_states(s, current_state)
        picked_inputs = model.pick_one_inputs(inputs)
        # Cover the case where there were no picked inputs (can't happen for a valid transition)
        trace.insert(0, picked_inputs.get_str_values() if picked_inputs else {})
    else:
        trace.insert(0, {})
    trace.insert(0, s.get_str_values())

    # Now we are only left with building a trace from Init to s
    # First find to which reachability frontier s belongs
    k = 0
    for i, frontier in enumerate(reach_frontiers):
        if s.entailed(frontier): # s in frontier
            k = i
            break
    current_state = s
    for frontier in reversed(reach_frontiers[:k]): # exclude the k-th element where s already is
        predecessors = model.pre(current_state) & frontier
        pred = model.pick_one_state(predecessors)
        if has_inputs:
            inputs = model.get_inputs_between_states(pred, current_state)
            picked_inputs = model.pick_one_inputs(inputs)
            # Cover the case where there were no picked inputs (can't happen for a valid transition)
            trace.insert(0, picked_inputs.get_str_values() if picked_inputs else {})
        else:
            trace.insert(0, {})
        trace.insert(0, pred.get_str_values())
        current_state = pred

    return False, tuple(trace)

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
