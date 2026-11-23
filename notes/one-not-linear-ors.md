# One NOT gate and ORs of linear set families

L-meta-955 asks for a binary AND/OR circuit with at most one NOT that computes all the disjunctions of a family of sets using fewer than `Σ(|S|−1)` gates. Every set must have at least two points and two different sets can share at most one point. The following argument and [exhaustive search](check-one-not-linear-ors.py) exclude every instance on at most six inputs. The family of arbitrary monotone outputs in [the six-input counterexample](six-input-negation.md) includes conjunctions and therefore solves a different problem.

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

For a positive control, private two-input OR prefixes supply all the required targets using exactly the ordinary budget. On seven inputs, thirteen core types remain after the counting argument. The search also excludes all three types with exactly three triples and no larger set. Run `python3.11 notes/check-one-not-linear-ors.py` on the research branch to reproduce the list and these exclusions. These are computational exclusions. The unrestricted assignment remains open.
