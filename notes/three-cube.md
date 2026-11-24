# The three-cube edge function needs thirteen monotone binary gates

The desk's L-meta-969 asks for an eleven-gate AND/OR circuit. Exhaustive synthesis excludes every budget through twelve. A thirteen-gate circuit attains the bound. Its behavior, size and gate types are [verified in Lean](ThreeCube.lean). The lower bound comes from a separate [exhaustive C++ search](check-three-cube.cpp).

The project's [checked opposite step, L-meta-970](https://data.pequalnp.com/data/lemma/L-meta-970.1681babb9428.json), already excludes eleven gates. The checker credits the fleet on November 23, 2026. The independent enumeration here also excludes twelve gates, and the construction reaches thirteen.

## Construction

The cube is bipartite. Its even-parity vertices are 0, 3, 5 and 6. Each is adjacent to three of the four odd-parity vertices 1, 2, 4 and 7. First compute the disjunctions of inputs 1 and 2, and of inputs 4 and 7. Each of the four required three-input disjunctions then takes one additional OR. Intersect each result with its corresponding even-parity input and OR the four terms together. This uses nine OR gates and four AND gates. The Lean theorem `ThreeCube.desk_evaluation` checks the exact twelve edges in the desk statement.

## Search

The program represents a wire by its complete truth table. A minimum circuit has only binary gates with distinct parents: constants, unary gates, default-false references and gates equal to an earlier signal can be simplified without increasing size. Every gate must reach the output. Independent ready gates can be scheduled in order of larger operand index, breaking ties by smaller index. Newly enabled gates have larger operand indices, so this gives a nondecreasing order. The enumerator tries every first pair for both graphs.

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

Compile with a C++17 compiler at optimization level 3 and run the executable without arguments. The twelve-gate exclusion visits 736,331 prefix nodes. A separate run omitting all cofactor bounds also excluded eleven gates in 10,107,769 visits. The Lean file certifies the upper bound. The computational exclusion uses the enumeration and pruning arguments above.

## Independent check by deleting and restoring a vertex

The [second enumerator](check-three-cube-lifts.cpp) starts from the six-cycle formed by deleting opposite cube vertices 0 and 7. It uses only exact truth tables, the ordering of independent gates, and the count of wires that still need a reader. It uses neither boundary domination nor lower bounds on the restricted functions to prune the enumeration.

A minimum circuit can be taken to have distinct binary operands at every gate, with every gate contributing to the output. Fixing an input to zero removes every direct reader of that input by constant propagation. When a reader is an AND, its output becomes zero, so its consumer can be removed too. The graphs below contain edges after the restriction, so a direct AND reader of the pinned input cannot itself be the output.

**From six vertices to seven.** The six-cycle needs eight gates. The base search checks every smaller feasible size and gives six ordered eight-gate circuits. If a nine-gate circuit computed the seven-vertex function, fixing vertex 7 to zero would leave at least eight gates. Vertex 7 is essential, so it could have exactly one reader, necessarily an OR. Otherwise at least two gates would disappear. Thus the nine-gate circuit would be obtained from an eight-gate cycle circuit by inserting one OR of vertex 7 and an existing wire, then redirecting a nonempty subset of that wire's uses. An inserted OR cannot be the output since the singleton vertex 7 must be rejected. Of all 114 such insertions, none works. The same argument excludes a circuit with eight gates or fewer. The [Lean restriction lemmas](ThreeCubeRestrictions.lean) identify this induced six-cycle, derive its exact size from the project's cycle theorem, and verify the ten-gate upper bound for the seven-vertex function.

**From seven vertices to eight.** Both operands of the first gate are raw inputs. If it is an AND of vertices x and y, x must have a second reader: with y zero, an edge between x and a different neighbor still detects x. Fixing x to zero removes both readers and a consumer of the first AND. That consumer must be distinct from the second reader, since a gate taking both x and the first AND just computes x or the first AND by absorption. This would leave at most nine gates from a twelve-gate circuit, contradicting the seven-vertex bound.

If the first gate is an OR of x and y, x again needs another reader. There is a neighbor z of x distinct from y and nonadjacent to y. The two inputs with true vertices {y,z} and {x,y,z} have different target values and give the same value to the first OR. For adjacent or antipodal x,y their neighborhoods are disjoint. For x,y at distance two they share exactly two of their three neighbors. This argument excludes eleven gates immediately: pinning x to zero removes at least two gates and the remaining graph needs ten.

A twelve-gate circuit would have exactly two readers of x, both ORs. Indeed, any third direct reader disappears on the zero slice. If the second reader were an AND, one of its consumers would also disappear and is distinct from the first gate. After pinning x, the remaining ten gates must form an optimal seven-vertex circuit. Both removed ORs had x as an operand, and one had a raw input y as its other operand. The ORs cannot feed directly into one another or take the same second operand, since then one is redundant. Thus every candidate is recovered by choosing two distinct base wires, at least one a raw input, and diverting nonempty subsets of their uses through the restored ORs. Vertex symmetry lets us use x = 0.

| Base circuit | Ordered base circuits | Insertions tested | Correct restored circuits |
| --- | ---: | ---: | ---: |
| Six-cycle, eight gates | 6 | 114 | 0 |
| Seven-vertex cube deletion, ten gates | 48 | 10,140 | 0 |

These counts keep the input labels fixed and sort gates by their operand indices. They count gate sequences, without identifying all graph symmetries. On the zero slice every insertion already agrees with the base circuit. The program checks all 64 or 128 remaining truth assignments on the one slice. Compile the second enumerator with a C++17 compiler at optimization level 3 and run it without arguments.
