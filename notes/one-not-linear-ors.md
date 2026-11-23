# One NOT gate and ORs of linear set families

L-meta-955 asks for a binary AND/OR circuit with at most one NOT that computes all the disjunctions of a family of sets using fewer than `Σ(|S|−1)` gates. Every set must have at least two points and two different sets can share at most one point. The following argument and [exhaustive search](check-one-not-linear-ors.py) exclude every instance on at most seven inputs. The family of arbitrary monotone outputs in [the six-input counterexample](six-input-negation.md) includes conjunctions and therefore solves a different problem.

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

The unrestricted assignment remains open.
