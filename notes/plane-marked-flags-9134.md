# Marked gates in the plane separator of L-meta-9134

Let `s` be the number of internal gates, `M` the actual marked conjunctions after choosing one allowed witness for each internal wire, and `E` the incident point-line pairs. The chosen marked conjunctions form a subset of the posted mark set. Say a gate is active on a flag when its value is true on the assignment with just the two endpoints of that flag on. Put `A_j = { e ∈ E | gate j is active on e }` for each `j ∈ M`. I obtain the bound

$$
|E\setminus \bigcup_{j\in M} A_j|\le s.
$$

In particular, the posted lower bound holds at every order if each marked gate is active on at most 99 flags. With the posted mark budget, any counterexample must contain a marked gate that is active on at least 100 flags. The mark budget does not give that per-gate bound.

## Sound output made from separated rectangles

All original wire sets are increasing and omit the all-zero input. This follows in wire order from the input sets and the permitted union, copy, empty set, and intersection rules. At an unmarked conjunction the first operand is invariant under changing the line bank, and the second is invariant under changing the point bank. Consequently the conjunction vanishes if either bank is entirely zero.

For each wire form its raw OR support. It is the set of variables reachable by following only copy and OR inputs backwards, stopping at every conjunction and at empty gates. Its disjunction is contained in the original wire set.

For every unmarked conjunction with operands `a,b`, make a rectangle that tests the raw OR support of `a` on the point bank and the raw OR support of `b` on the line bank. This rectangle is contained in the original gate. Each operand's raw OR support is already confined to the indicated bank. A raw variable on the other bank would make that operand true on an input supported by that single variable, contradicting invariance and rejection of the all-zero input.

Starting at the output, follow copy and OR inputs backwards, stopping at raw inputs, empty wires, and conjunctions. Take the disjunction of the rectangles at the unmarked conjunctions reached this way. This is a sound subfunction of the original output. Any raw terminal reached by this traversal would force the original output to accept a singleton, which is forbidden. The canonical forbidden input for a chosen set of zero or one lines dominates every nonincident singleton or point-line pair with those same lines. Monotonicity therefore supplies the required singleton and pair soundness.

This disjunction accepts every flag on which all marked gates are false. Fix such a flag. On either of its projections to a single bank, marked gates are false by monotonicity, and unmarked conjunctions are false by separatedness. In wire order the raw OR support gives the exact original value of every wire on each projection. On the flag itself each unmarked terminal conjunction thus agrees with its rectangle. Every marked conjunction on the output traversal is false, so the new disjunction agrees with the original output on that flag.

## Counting with sharing

On singleton point-line pairs each nonempty output rectangle is contained in incidence. A rectangle with two distinct points and two distinct lines would make two points share two lines. Thus each nonempty rectangle is a star, with a center on one bank and a subset of its neighbors on the other. Assign every flag accepted by this disjunction to one star that covers it. Choose either endpoint as the center for a one-edge star.

For a fixed center, let `m` be the number of distinct neighbors assigned to it and `t` the number of its terminal conjunctions that receive at least one assigned flag. Look at the OR and copy cones of the neighbor operands of these terminals. Project their raw supports onto the assigned neighbors. Start with one component for each assigned neighbor and process the cones in wire order. Every input belongs to one component. Each copy leaves the components unchanged. Each OR has children whose nonempty projected supports lie within single components. It can join at most two components. Each final neighbor support lies in one component, and together the `t` final supports cover all `m` assigned neighbors, so at least `m-t` distinct OR gates have joined components.

Any OR charged in this way has at least two distinct neighbors in its original raw OR support, and its entire original raw OR support is contained in the neighborhood of the center. It lies in the raw OR cone of a final neighbor operand and every wire in that cone has raw OR support included in the final support. The same OR cannot be charged to two different centers. Centers on the same bank share at most one neighbor. Centers on opposite banks have neighbors on different banks. The charged ORs and terminal conjunctions use different internal gates. Summing `m\le(m-t)+t` over centers bounds the number of accepted flags by `s`, including when the original cones share wires.

## Consequence for the exact threshold

There are `N(q+1)` flags. If every marked gate is active on at most 99 flags, then `N(q+1) ≤ s + 99|M|`. Multiplying by 100 and using the posted mark budget `100|M| < Nq` rules out `100s < N(q+1)`. A bound on the union of marked activations can certify the full target. The current argument leaves that union uncontrolled.

## Verification

An exact truth-table replay used 220 generated programs over three bits per bank. It checked inclusion in the original wire sets at 7,700 wires and agreement on 325,579 wire-input cases with every earlier marked gate false. The programs included 2,120 separated conjunctions and 1,120 marked conjunctions. The [Lean counting lemma](PlaneMarkedCounting9134.lean) verifies the finite-set covering step and the consequence that a counterexample has a mark active on at least 100 flags, given the bound on flags outside the marked union. The shared-cone gate count above is a written proof.
