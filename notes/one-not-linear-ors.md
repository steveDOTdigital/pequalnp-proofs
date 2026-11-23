# One NOT gate and ORs of linear set families

L-meta-955 asks for a binary AND/OR circuit with at most one NOT that computes all the disjunctions of a family of sets using fewer than `Σ(|S|−1)` gates. Every set must have at least two points and two different sets can share at most one point. The following argument, [small-case search](check-one-not-linear-ors.py) and [SAT checks through ten inputs](check-ten-input-linear-ors.py) exclude every instance on at most ten inputs. The family of arbitrary monotone outputs in [the six-input counterexample](six-input-negation.md) includes conjunctions and therefore solves a different problem.

## A counting argument for one NOT

Choose a largest output set S, of size k, in a family of m nonempty sets. Compare the all-zero input with each singleton input in S. A wire separates an index if it is false at zero and true at the corresponding singleton. A raw input or any of the other required outputs separates at most one index in S. The other outputs are distinct nonconstant functions different from every raw input, so they require at least m−1 distinct gates.

If there is a NOT gate, its operand is monotone because every preceding gate is monotone. The NOT output separates no indices for these comparisons. It also differs from every required output: it is antitone, and a disjunction of a set of at least two inputs is nonconstant and monotone.

Trace the S output backwards in reverse gate order. Stop at input wires, the other required outputs and the NOT gate. At each AND or OR gate, every index separated by the gate is separated by at least one parent. Each expansion increases the number of wires on the frontier by at most one, counting a shared wire once. The frontier must cover all k indices. At least k−1 additional gates must therefore be expanded. In total, any circuit using exactly one NOT has at least `m+k−1` gates. This excludes a saving whenever the sum of `|T|−2` over the other output sets T is at most one.

For a circuit without NOT gates, the full `Σ(|S|−1)` bound follows by a related charge. For each S, compare its singleton inputs with the single input that turns on exactly the points outside S. Charge S a gate when the gate is false on that outside input and true on at least two of S's singletons. Frontier expansion gives at least `|S|−1` charges for S, since each uncharged wire separates at most one index. A monotone wire that is false on the outside input cannot be true on a singleton outside S. Its two true singleton indices therefore prevent it from being charged to any other set. Summing gives the claimed bound.

## Remaining circuits on six inputs

Size-two sets do not affect the condition on `|T|−2`. On at most five inputs the counting condition handles every linear family. On six inputs there are two remaining types after removing pairs and relabelling the inputs. One has three triples, and the other has four. Identify the six inputs with the edges of the complete graph on four vertices. The triples are respectively three or all four of the vertex stars. Exhaustive enumeration finds 120 labelled three-triple families and 30 labelled four-triple families.

Give the circuit the raw inputs, both constants and every compatible two-point disjunction for free. This covers every choice of pair outputs, since every requested pair normally consumes its own gate. Also allow any required triple output to be added for free whenever two available signals compute it by AND or OR. A NOT cannot directly produce a nonconstant monotone output: with at most one NOT its operand is monotone. With t triple outputs, a strict saving leaves at most t−1 additional gates after subtracting one gate per required output. The program exhausts the choices of their truth tables, including a possible NOT. It permits all fanout, and giving both constants for free covers the evaluator's zero-input gates and out-of-range wires.

| Triple outputs | Free compatible pair outputs | States by number of additional gates | Saving found |
| ---: | ---: | --- | --- |
| 3 | 6 | 1, 97, 6,013 | No |
| 4 | 3 | 1, 66, 2,928, 111,127 | No |

For a positive control, private two-input OR prefixes supply all the required targets using exactly the ordinary budget. Run `python3.11 notes/check-one-not-linear-ors.py` on the research branch to reproduce the counts.

## A distinct predecessor for each large output

Let t be the number of targets with at least three points. Take the first gate that computes each target. Its value is distinct from the other target values and from every raw input. With exactly one NOT gate, none of these target gates is a NOT: the operand of the unique NOT is monotone, so its complement cannot be a nonconstant monotone disjunction.

Each target S of size at least three also needs a separate earlier gate, as follows.

- If the final gate is OR, both parents are pointwise bounded above by the disjunction on S. One parent must be true on two or more singletons of S to cover its at least three singleton inputs. This parent differs from every raw input. It cannot qualify for another OR target because two targets share at most one point.
- If the final gate is AND, both parents are pointwise at least the disjunction on S. On the input that turns on exactly the points outside S the target is false, so choose a parent that is false there. It cannot qualify for another AND target T: this same input turns on a point of T. It cannot be a raw input because it is true on each of at least three different singletons.
- An OR predecessor for S cannot be an AND predecessor for another target T. It is false on a singleton of T outside S, where an AND predecessor for T must be true.

None of these selected parents equals another required output, including a two-point output. For an OR predecessor, two of its true singleton points would have to belong to both sets. For an AND predecessor, the other set would have to contain S. The choice of the first occurrence of S rules out the parent being S itself. Empty or unary final gates cannot be the first occurrence of one of these targets. A nonconstant NOT of a monotone function is true at the all-zero input and false at the all-one input, so it cannot be any selected parent. Constant NOT outputs cannot qualify either.

Counting the m target gates, the t different additional parents, and the NOT gives a lower bound of `m+t+1`. In particular, a single NOT cannot save a gate for any linear family of pairs and triples on any number of inputs. This bound also covers one four-point target alongside any number of pairs and triples.

## Seven inputs

There are thirteen core types on seven inputs after the largest-output bound. The predecessor bound covers twelve. The remaining type has two four-point sets meeting in one point. All nine compatible two-point disjunctions were supplied for free. A strict saving would leave at most three additional gates beyond the mandatory outputs. The search found no witness, with 1 initial state, 166 one-gate states, 16,947 two-gate states and 3,431,667 terminal visits. Terminal visits in this larger run include repeated states to bound memory. Together the counting argument and the exhaustive check exclude every system on at most seven inputs. Both also allow arbitrary subsets of the compatible pair outputs.

## Exhausting the gate budget

Write E for the sum of |S|−3 over the t sets of size at least three. The separate-construction budget is m+t+E. The predecessor bound handles E≤1. If E=2, any strict saving with one NOT uses precisely the m first target gates, the t selected predecessors and the NOT. Each gate has exactly one of those roles.

Suppose a large target S first appears at an AND. It needs two distinct parents that dominate its disjunction. Equal parents, or a constant-true parent, would give an earlier copy of S. Besides its own chosen predecessor, none of the available wires can dominate S. A raw input misses a singleton of S. Another target T and any selected OR predecessor for T miss a singleton of S outside T. An AND predecessor for T is false when exactly the points outside T are on, whereas S is true there. A nonconstant NOT is false at the all-one input. This excludes AND as the first gate for every large target.

Every selected predecessor is now bounded above by its own target and true on at least two of that target's singletons. Choose a target S of size at least four, which exists since E=2. Both parents of its final OR are bounded above by S. Earlier wires of this kind consist only of S's own selected predecessor H, singletons in S and the constant false. Every other target or selected predecessor is true on some singleton outside S. Thus H is true on at least three singletons of S. An OR computing H could use only earlier wires bounded above by S, which together cover at most two singletons. An AND computing H would require both parents true on at least three singletons of S. At least one parent must also be false at zero, since H is false there. Before H, any such wire is a raw input, another target, another selected predecessor or constant false, each covering at most one singleton of S. A NOT false at zero is identically false because its operand is monotone. This contradiction excludes E=2 for any number of inputs.

## A connectivity bound

Retain a nonempty subfamily I of targets. Let v count its points and c count its connected components, joining points that belong to a common retained set. Replace the first output gate of each omitted target T by a free constant true. On the slice where all points outside a retained S are on, every omitted disjunction is true, because T has a point outside S. Induction through the gates shows that the modified circuit still computes the disjunction of S on that entire slice. Its output therefore has a path from each input in S.

Start with one component per raw input. For each wire, track the raw inputs with a path to it, giving constants empty support. At a binary gate, joining the two nonempty parent supports merges at most two current components. Unary gates merge none. At the end all points of each retained S belong to one component. Even allowing paths through extra inputs, this takes at least v−c merges. Add back the m−|I| replaced gates. If the original circuit used one NOT, it contributes one further gate because it merges no components and cannot itself be a target. This gives at least m−|I|+v−c+1 gates. In particular, with exactly two large sets, retain both and omit all pairs. Whether the large sets meet in one point or are disjoint, v−c equals the sum of their two individual disjunction costs. No saving is possible.

## Eight inputs

If the largest set has at least six points, at most two points lie outside it. Every other large set needs at least two outside points, so there can be at most one, of size three. The largest-output bound applies. If the largest set has five points, E≥3 requires another set of size at least four. It must have size four and meet the five-point set in one point. Together they cover all eight points. A third large set cannot meet each in at most one point, so the two-set connectivity bound applies. If all sizes are at most four, E≥3 requires three four-point sets. Their pairwise intersections have total size at most three, so their union has at least nine points. These cases exclude every witness on at most eight inputs.

## Nine inputs

A finite SAT check extends the exclusion to nine inputs. Generate the large sets in decreasing size, keeping one representative per relabelling of the nine ground points. Two families have the same input-column signatures up to row order exactly when they are isomorphic. Permuting only rows that have the same size and the same multiset of point degrees suffices. Every extension of a discarded representative has an isomorphic extension of the retained representative. After the largest-set and E≤2 bounds, the remaining 15 types account for 467,145 labelled families of large sets. The connectivity bound rules out seven types.

Each of the eight remaining types has E=3. A strict saving can therefore use only the following gates after supplying every compatible pair disjunction for free: a first gate and distinct selected parent per large target, one NOT and at most one further binary gate. Supplying compatible pairs for free covers any choice of the original pair outputs, since their first gates were included in the original output count. An unused spare gate can be padded. The selected parent is distinct from the other parent of the target, because otherwise the target would have appeared earlier.

The [reproducible encoding](check-nine-input-linear-ors.py) imposes a total order on these named gates and allows a gate to use any earlier wire, raw input, compatible pair or constant, subject to its role. It tests the all-zero and all-one inputs, each singleton and the input with exactly the points outside each large set on. At an OR target the selected parent must cover two singleton points. At an AND target it must be false with all outside points on. All gates must use the same operations and parents across all tested inputs. Any actual circuit with a strict saving gives a satisfying assignment. Unsatisfiability on this sample suffices to exclude a circuit on the full truth table.

CaDiCaL returned UNSAT for all eight cases with internal proof checking enabled. As a positive control, allowing three further binary gates in place of one admits the ordinary separate constructions and an unused NOT. The same encoding returned SAT for all eight controls. Run `python3.11 notes/check-nine-input-linear-ors.py /path/to/cadical` to reproduce both checks. This is a computational lower bound. The desk assignment asks for an example on an unrestricted number of inputs.

## Ten inputs

The same enumeration leaves 317 ten-input families of large sets after the three counting bounds. There are 287 with E=3, 29 with E=4 and one with E=5. A strict saving leaves at most E−2 binary gates in addition to the targets, the selected parents and the NOT. The spare gates may be named in their actual topological order.

For each large target S, its parent other than its selected predecessor must be a spare gate or a raw input of S. For an OR target that parent is bounded above by S. No different target T or its selected parent meets this condition: an OR predecessor for T is true on at least two singletons of T, and an AND predecessor dominates T. For an AND target the other parent must dominate S. A different target or OR predecessor misses a singleton in S, and an AND predecessor for T is false when exactly the points outside T are on. The unique nonconstant NOT is true at zero and false at the all-one input, excluding it in either role. A constant parent either makes the target constant or means that the other parent was already the target. These restrictions also apply after supplying the compatible pair outputs for free.

With these parent choices, CaDiCaL returned UNSAT with proof checking enabled for 316 of the 317 families. The last one admits a short argument using the nine-input bound. Its five large sets each contain four points, and each of the ten points belongs to exactly two large sets.

Suppose this family saves a gate. Compute all its requested pair disjunctions directly at the beginning, replacing each old first pair gate by a reference to its new value. This preserves the budget. Fix one point x and call its two large sets S and T. If x belongs to k requested pairs, setting x to zero removes k pair gates: each becomes its other raw input. The ordinary budget falls by exactly k+2. Thus removing even two more gates would yield a strict saving on nine inputs. The remaining sets of size at least two are distinct, since two original sets share at most one point.

On the slice where exactly the inputs outside S are fixed to one, S still depends on x and every pair output is constant true. The same holds on the T slice. Consequently x has a direct consumer outside the pair gates. It can have only one such gate q, since two direct consumers would both simplify when x is fixed to zero. Every change from x to either of the two outputs passes through q on the corresponding slice. The gate q is therefore distinct from every output: each output is constant on at least one slice. If q is AND or NOT, it becomes constant at x=0. A subsequent non-pair gate on a path to S then also simplifies, again removing two gates. We can drop redundant unary copies. The only remaining possibility is an OR directly consuming x.

Two points x and y cannot have the same such consumer. That gate would be the raw disjunction of x and y. At least one of S and T misses y, and its slice fixes y to one, preventing this gate from carrying any change in x. All ten points therefore need different non-output OR gates. A strict saving allows at most t+E−2=8 non-output gates besides the unique NOT. This excludes the last family. The [ten-input reproduction script](check-ten-input-linear-ors.py) checks the family inventory and the other 316 exclusions. Run it after the nine-input checker with the same CaDiCaL executable.

The unrestricted assignment remains open.
