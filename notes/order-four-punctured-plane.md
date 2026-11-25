# One missing line in the order-four plane

Cases L-meta-9739 and L-meta-9740 ask opposite sides of the same question. Can 118 binary monotone gates detect an incident point and line among the 41 posted inputs? **The exact formula size is 119.** The same lower bound holds if every shared gate is an OR of two raw points, with any number of pairs and arbitrary fanout. Exchanging the shores gives the result for pairs of lines. The unrestricted circuit question remains open.

The pair result also proves a subclass of the general edge-plus-cover conjecture in L-meta-612, for every finite four-cycle-free bipartite graph. No regularity, degree limit or bound on the number of shared pairs is needed.

## The labeled plane

Vertices 0 through 20 are points and 21 through 40 are lines. Every line meets five points. Sixteen points have degree five, and the other five have degree four. The 100 flags contain no four-cycle. For each line numbered 21+j, point j+1 is incident. These 20 disjoint flags give a matching, and the 20 lines are a minimum vertex cover.

Take one star per line. Four OR gates collect its points and an AND tests its line, costing 100 gates across the stars. Nineteen OR gates combine them. The [Lean construction](OrderFourPlane.lean) checks the 119-gate size, binary monotone legality, and the existential edge predicate on every input. The flag-cross rank bound gives 100 plus the cover size in formula leaves. This requires 119 binary gates and proves the formula optimum.

For comparison, the [previous unrestricted circuit bound](pseudoforest-circuits.md) gives at least 61 gates here. Its equality obstruction applies because every degree is at least two, the number of edges exceeds the number of active vertices, and twice the minimum cover size is at most the number of vertices.

## Arbitrarily many shared pairs on one shore

Let a four-cycle-free bipartite graph have m edges and minimum vertex cover τ. Trim the circuit to its binary output cone, contract unary gates, constants and repeated operands, and merge duplicate helpers if needed. Suppose each internal wire with multiple readers is the OR of two distinct raw vertices on the point shore. Cut each such wire and name it as an additional formula variable. If there are h helpers, the remaining formula has R raw leaves and A helper leaves, with A at least 2h. Its original gate count is R + A + h − 1. An ordinary output formula corresponds to h = 0.

For each pair of partner points, delete the flags joining them to their common line, when this line exists. Two distinct points have at most one common line. At most 2h flags disappear. Adding at most h common lines extends any cover of the retained flags to a cover of the original graph. The retained flag set D therefore has at least m − 2h edges and needs a cover of at least τ − h vertices.

For a retained flag (p,l), use its two endpoints as a positive input. For its negative comparison, activate the other retained points on l, all partners of p, and the other retained lines through p. Every partner is disjoint from the selected lines by the deletion rule. An incidence between another point and another line would make a four-cycle. Thus the comparison is negative.

On the diagonal, any helper activated by p is also activated by a partner on the negative input. When two retained flags share their point, the same argument blocks every helper report. When they share their line, the other row's point is on the negative input along with all the helpers it activates. In either case the only possible separating label is the common raw endpoint. For a degree-one rank charge, force the point report by activating its line and all its partners, or force the line report by activating the point on its own.

These tests give R ≥ |D| + τ(D), by factoring each raw label's report matrix through the occurrences of that label in the formula. Consequently R + A + h ≥ m + τ. The [general Lean proof](OneShorePairRank.lean) checks the comparison inputs and the rank deduction, bounds the deleted flags, extends a retained cover, and proves the gate count in the formula obtained by cutting the shared wires. The conversion from a live circuit with the stated sharing pattern to that formula is the wire-counting argument above.

On these 100 flags the maximum degree gives the stronger inequality 5s ≥ 595 + 3h for gate count s. Indeed |D| ≤ 5τ(D) and |D| ≥ 100 − 2h. Thus any circuit in this class with a genuinely shared pair needs at least **120** gates. The 119-gate star formula uses none. Lean also applies the general bound of 119 directly to the posted incidence relation with an arbitrary family of point pairs.

The sources require the project's Lean toolchain and the adjacent FlagCrossRank and FlagStarCircuit modules. Build the imported modules before checking OrderFourPlane.
