# FM4CPS Assignment 1

## Quick Start

### Prerequisites
- **Docker**: Required to run the `pynusmv` model checking environment.
- **uv**: Required for Python dependency management. [Install uv](https://github.com/astral-sh/uv).

### Setup
1. Clone the repository.
2. Install dependencies:
   ```bash
   uv sync
   ```
3. Install git filters for notebooks (prevents committing large outputs):
   ```bash
   uv run nbstripout --install
   ```

### Running the Project
- **VS Code**: Open `FM4CPS.ipynb`, select the kernel provided by `uv` (look for `.venv`), and run cells.
- **Terminal**:
  ```bash
  uv run jupyter notebook
  ```

---

## Part 1: safety properties

In the first part of the assignment you will implement the symbolic algorithm for invariant verification, using BDDs as data structure to represent and manipulate regions.

The attached `inv_mc.py` file contains a python script that uses the pynusmv library to verify invariants of SMV programs.

Using the `inv_mc.py` script as a starting point, implement a function `check_explain_inv_spec (spec)` that respects the following specifications:

- The function checks if spec is an invariant for the SMV model or not, that is, whether all the reachable states of the model satisfy spec or not.
- The function must return an explanation for why the model does not satisfy spec, if it is the case;
- The return value is a tuple where the first element is True and the second element is None if the invariant is true. When the invariant is not verified, the first element is False and the second element is an execution of the SMV model that violates spec;
- The execution is a tuple of alternating states and inputs, starting and ending with a state. States and inputs are represented by dictionaries where keys are state and inputs variable of the loaded SMV model, and values are their value.
### Examples
The archive react_examples.zip contains some SMV programs to test your implementation.

## Part 2: response properties
In the second part of the assignment you will implement a symbolic algorithm for the verification of a special class of LTL formulas, using BDDs as data structure to represent and manipulate regions. The formulas considered by the algorithm are called response formulas, and have the special form

$$
\square(f \rightarrow \lozenge f)
$$

where each $f$ and $g$ are Boolean combinations of base formulas with no temporal operators. Response is a rich fragment of LTL, that can express many useful liveness requirements. Some examples of liveness properties for the Railroad Controller that can be written as response formulas are listed below.

A west train that is waiting will eventually be allowed on the bridge:
$$
\square(train_w.mode=wait \rightarrow \lozenge train_w.mode=bridge)
$$

If the west train is waiting then either the corresponding signal will be green or the east train will be on the bridge:
$$
\square(train_w.mode=wait \rightarrow \lozenge (signal_w = green \lor train_e.mode = bridge))
$$

If the west train is waiting with the east train off the bridge, then the west train will be allowed on the bridge:
$$
\square(\neg(train_e.mode = bridge) \land train_w.mode = bridge \rightarrow \lozenge train_w.mode=bridge)
$$
The following formulas are not response formulas, and should be discarded by the algorithm:

- $\square\lozenge train_w.mode=wait \rightarrow \square\lozenge signal_w=green$
- $\square(\neg(train_e.mode=bridge)\rightarrow\lozenge train_w.mode=wait\rightarrow\lozenge train_w.mode=bridge)$
- $\square(train_w.mode=wait\rightarrow\lozenge (signal_w=green \land\bigcirc train_w.mode=bridge))$

The attached `response_mc.py` file contains a python script that uses the pynusmv library to verify Reactivity properties of SMV programs. The script uses the function `parse(spec)` to check if spec is a response formula, and skips all formulas that are not of the desired form. 

Using the `response_mc.py` script as a starting point, implement the function `check_explain_response_spec(spec)`, respecting the following specifications:

- The function checks if the response formula spec is satisfied by the loaded SMV model or not, that is, whether all the executions of the model satisfy spec or not.
- The return value of `check_explain_response_spec(spec)` is a tuple where the first element is True and the second element is None if the formula is true. When the formula is not verified, the first element is False and the second element is an execution of the SMV model that violates spec. The function returns None if spec is not a response formula;
- The execution is a tuple of alternating states and inputs, starting and ending with a state. States and inputs are represented by dictionaries where keys are state and inputs variable of the loaded SMV model, and values are their value;
- The execution is looping: the last state should be somewhere else in the sequence to indicate the starting point of the loop. 
### Examples
The archive response_examples.zip contains some SMV programs to test your implementation.

The pynusmv library
pynusmv is a python wrapper to NuSMV model checking algorithms.The library consists of several modules. To implement the project you can use only the following modules:

- init
- glob
- fsm, except for method reachable_states
- prop
- dd 
- the helper function spec_to_bdd (model, spec) included in the scripts, to convert a formula with no temporal operators to a BDD
- the helper function parse(spec) that checks if spec is a response formula or not. You can modify the helper function if you desire.

You can find more information about the pynusmv library at the websites http://lvl.info.ucl.ac.be/Tools/PyNuSMV and https://pynusmv.readthedocs.io.

Binary files to install pynusmv on recent Python versions are available at https://github.com/davidebreso/pynusmv/releases/latest