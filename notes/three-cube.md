# The three-cube edge function needs thirteen monotone binary gates

The desk's L-meta-969 asks for an eleven-gate AND/OR circuit. Exhaustive synthesis excludes every budget through twelve. A thirteen-gate circuit attains the bound. Its behavior, size and gate types are [verified in Lean](ThreeCube.lean). The lower bound comes from a separate [exhaustive C++ search](check-three-cube.cpp).

## Construction

The cube is bipartite. Its even-parity vertices are 0, 3, 5 and 6. Each is adjacent to three of the four odd-parity vertices 1, 2, 4 and 7. First compute the disjunctions of inputs 1 and 2, and of inputs 4 and 7. Each of the four required three-input disjunctions then takes one additional OR. Intersect each result with its corresponding even-parity input and OR the four terms together. This uses nine OR gates and four AND gates. The Lean theorem `ThreeCube.desk_evaluation` checks the exact twelve edges in the desk statement.

## Search

The program represents a wire by its complete truth table. A minimum circuit has only binary gates with distinct parents: constants, unary gates, default-false references and gates equal to an earlier signal can be simplified without increasing size. Every gate must reach the output. Independent ready gates can be scheduled in order of larger operand index, breaking ties by smaller index. Newly enabled gates have larger operand indices, so this gives a nondecreasing order. For the full cube, minimize this order also over cube symmetries. The first pair can then be chosen from (0,1), (0,3) and (0,7), one for each Hamming distance. All first pairs are allowed for the vertex deletion.

The minimal true inputs are the graph edges. The maximal false inputs are the maximal independent sets. For monotone circuits these boundary inputs determine the function. An earlier wire dominates a gate if it is at least the gate on all the positive boundary inputs and at most the gate on all the negative boundary inputs. Substituting the earlier wire preserves a correct output by monotonicity. Thus a minimum circuit never contains such a gate. The same argument permits constant propagation.

After a prefix, every computed gate that has yet to be read must reach the output. A raw input must also be read again if two assignments differing only in that input have different target values and agree on every prefix gate. Connecting all those distinct sources to the output needs at least one fewer binary gates than sources.

First run the enumeration on the seven-vertex graph obtained by removing vertex 0, without any assumed cofactor bound. All budgets below ten fail and ten succeeds. Budgets below six are impossible because every input is essential and a binary gate connects at most two components. Vertex transitivity gives the same minimum when any one of the eight cube inputs is pinned to zero.

On each such zero slice, the full-cube search can count prefix gates dominated by an earlier signal or a constant on the restricted boundary. All can be eliminated simultaneously: process them in order, maintaining replacement wires that dominate their originals. Any raw input still requiring a later reader forces one further elimination when that input is pinned to zero. Prune only when fewer than ten gates could remain on that slice. The full cube depends on all eight inputs, giving a starting budget of seven.

| Inputs | Gate budgets | Result |
| ---: | --- | --- |
| 7 | 6, 7, 8, 9 | UNSAT |
| 7 | 10 | SAT |
| 8 | 7, 8, 9, 10, 11, 12 | UNSAT |
| 8 | 13 | Explicit Lean-checked construction |

Compile with a C++17 compiler at optimization level 3 and run the executable without arguments. The twelve-gate exclusion visits 122,822 prefix nodes. A separate run omitting all cofactor bounds also excluded eleven gates in 1,259,881 visits. The Lean file certifies the upper bound. The computational exclusion uses the enumeration and pruning arguments above.
