# Three cyclic matchings need at least thirteen gates

For L-meta-652 let Fₖ = ORᵢ (xᵢ AND yᵢ₊ₖ), with indices modulo three. The circuit basis is binary AND/OR and unary NOT with arbitrary sharing. **The unrestricted minimum lies between 13 and 15 inclusive.** Furthermore, in a smallest circuit of size at most 14, every output must have at least seven gates in its own dependency cone.

## Pinning one raw input

Fix x₀ = 1. The three functions on the remaining five inputs are

    yₖ OR (x₁ AND yₖ₊₁) OR (x₂ AND yₖ₊₂).

The exact synthesis check at budget ten returns UNSAT. It imposes all 32 input rows, allows every output to select any computed wire, and checks CaDiCaL's proof internally. Twelve gates suffice by the displayed formulas. All single-true restrictions of the original circuit are equivalent under input and output permutations.

Some single-true restriction always removes **at least two gates** from a circuit computing the original ordered outputs. First discard dead gates, propagate constants, remove copies and drop ignored NOT operands. If the first gate is NOT, fixing its input makes it constant. It must have a consumer since none of the outputs is a literal; a consuming gate can be eliminated as well. If the first gate is binary, its two operands are distinct raw inputs. If they were both read solely at this gate, interchanging them would preserve all three outputs. No such transposition does. For two inputs on the same side, turn on a single opposite-side input and swap which one of the pair is on: different output indices light up. For inputs on different sides, turn on one further input on the side of the first. One setting of the pair then activates no edge, and the swapped setting activates an edge. Consequently at least one operand has a second distinct reader. Fixing that operand to true lets both consuming gates be folded or bypassed. The resulting restricted circuit needs at least eleven gates, giving 11 + 2 = 13 before the restriction.

## Exhausting small output cones

A dependency cone is the subcircuit feeding one particular output, including gates it shares with other outputs. Each matching depends essentially and increasingly on all six raw bits. After simplification, any connected cone needs at least five binary gates to connect the six inputs. With five gates it is a read-once binary tree. With six gates and one NOT, the remaining five binary gates would again form a tree. Any leaf below the NOT would be decreasing, contradicting essential increasing dependence. Thus a six-gate cone has six binary gates and no NOT.

In this last case there are twelve operand reads, but the six inputs and five non-output gates use eleven reads to reach the output. Exactly one source or gate is read twice. Below that signal is a read-once tree on a nonempty set of raw leaves. Above it is a read-once tree on the remaining leaves and two occurrences of the shared signal. The program enumerates both trees under every partition and tests the resulting truth table against a matching. If the shared signal uses all six raw leaves the upper tree would merely combine it with itself, a removable copy. Five-gate cones are enumerated as single trees. Duplicate wire functions can be reused without increasing size; order the chosen cone before the rest of the circuit when simplifying it.

For output zero there are three distinct five-gate signal sets, equivalent under symmetry, and 54 six-gate signal sets in seven symmetry classes. Simultaneous permutations of the two sides preserving matching zero, and exchanging the two sides, preserve the family of three outputs. Treat each representative's computed signals as free and synthesize the two other outputs within the remaining budget. The five-gate representative with nine remaining gates returns UNSAT. All seven six-gate representatives with eight remaining gates also return UNSAT. An arbitrary topological ordering of any circuit containing such a cone may put the whole cone first, so this excludes the entire stated class.

## Reproduction

From the repository root with the Lean toolchain's CaDiCaL on PATH:

```sh
python3 -B notes/search-three-matchings.py cadical --first-input-one --gates 10 --seconds 120 --check
python3 -B notes/search-three-matchings.py cadical --fixed 1 --gates 14 --seconds 120 --check
python3 -B notes/matching-small-cones.py --solver cadical --seconds 120
```

The SAT encoding permits arbitrary later uses of all available wires. For each output it tests whether flipping a raw bit can change that output with all supplied prefix signals fixed. Such a bit must occur in the suffix itself, which gives redundant reachability and gate-count constraints. A smaller satisfying circuit can be padded with output copies, and independent gates can be ordered by larger operand then smaller operand. The first raw gate is reduced only by symmetries preserving the problem. A SAT result is independently tested as a circuit on the full truth table. A timeout gives no exclusion. These are externally reproducible solver results; the unrestricted 14-gate question remains open.

### Smaller restrictions used for further pruning

After x₀ = 1, pinning either remaining x to zero or one gives lower bounds of six or seven gates respectively. Pinning any y to zero or one gives lower bounds of seven or six. The four exact searches at budgets 5, 6, 6 and 5 respectively return UNSAT. Constant or raw outputs are omitted in these subproblems; this preserves a lower bound. Here is a reproduction for the four symmetry representatives:

```sh
python3 -B - <<'PY'
from runpy import run_path
search = run_path("notes/search-three-matchings.py")["synthesize"]
for i, value, limit in [(1,0,5), (1,1,6), (3,0,6), (3,1,5)]:
    search("cadical", 0, limit, 30, True, pins={0: 1, i: value})
PY
```

The optional `--cofactor-bounds` flag uses these lower bounds on the five-input problem. On the unrestricted six-input problem it uses the eleven-gate lower bound after fixing any input true. Under a restriction, the circuit may reuse any earlier identical truth table and may propagate constants. Hence at least the known lower bound in distinct new nonconstant wire functions must survive. A direct twelve-gate implementation passes all ten five-input inequalities. The strengthened searches at eleven gates for the five-input problem and thirteen for the full problem both timed out. Separately splitting the former search by the first gate excluded NOT of a y bit and both AND and OR of two different y bits; the five other classes timed out.
