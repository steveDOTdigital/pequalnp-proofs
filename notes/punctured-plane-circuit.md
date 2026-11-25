# Eleven surviving lines of the order-three plane

Case L-meta-9792 asks whether 53 binary monotone gates can compute the edge function on its 24 labeled inputs. We obtain **38 to 54 gates** for unrestricted AND/OR circuits and **exactly 54 gates** for AND/OR formulas. The 53-gate circuit question remains open.

## Formula optimum

There are 13 point inputs, numbered 0 through 12, and 11 line inputs, numbered 13 through 23. Each line meets four points. Each pair of distinct lines meets in at most one point. Grouping the four incident points by their line gives 11 stars. Their three internal OR gates and one AND gate cost 44 gates. Combining the eleven outputs costs another ten.

For the lower bound, take the 44 positive inputs that consist of one incident point and line. For a flag `(p,l)`, take the negative cross consisting of the other points of `l` and the other lines through `p`. An edge inside this cross would complete a four-cycle. Each singleton input is also negative. The rectangle-partition rank bound gives at least 44 formula leaves plus the size of a vertex cover. Each selected vertex covers at most four flags. Therefore the cover contains at least eleven vertices, and 55 leaves require 54 binary gates. The [Lean proof](PuncturedPlaneCircuit.lean) checks the flags, degrees, all required truth values, the formula lower bound and the actual 54-gate circuit.

## Why 37 gates fail even with sharing

The [restriction checker](punctured-plane-pins.cpp) first runs the [gate-elimination recurrence](cubic-pair-restrictions.cpp) on the posted graph. The initial lower bound is 37 binary gates with either ordinary monotone gates or free wire inversions. Here is a separate second-gate obstruction in the monotone model.

At budget 37, pinning any input low except 16 or 22 leaves a function requiring at least 36 gates. Each such input has just one direct reader. That reader must be OR. An AND reader would become false and would eliminate a second gate at its consumer. The pin leaves a nonconstant function, so the reader cannot itself be the output. For 16 and 22 the low-pin lower bound is 35, allowing at most two readers each.

Every input remains essential when another raw input is fixed to either controlling value. On a low pin use a different neighbor. On a high pin an adjacent input is already sensitive, and for a different vertex on the same shore there is a neighbor outside the pinned vertex's neighborhood. All point degrees are at least two and two distinct vertices on the same shore have at most one common neighbor. Thus either endpoint of a raw-pair gate needs a second reader. Only 16 and 22 can be its endpoints, and a twice-read input cannot feed an AND because its low pin would remove three gates. After simplifying absorption, the first gate must be `16 OR 22`.

A second raw-pair gate would duplicate the first. Reusing one of its operands with its output gives an alias by absorption. Otherwise the second gate combines the first output with a different raw input `c`. Its sole reader must be OR, but `c` remains essential even when `16 OR 22` is true. If `c` is a point, activate line 16 and any line containing `c`, initially with no points. If `c` is another line, activate line 16 and a point of `c` outside line 16. Toggling `c` changes the target in each construction. The proposed OR reader masks that change. There is no admissible second gate.

The implementation also enumerates the first two gates for active induced subgraphs obtained by deleting up to three vertices. At order 21 it strengthens 60 of 1,997 active masks. It checks 275 masks at order 22, all 24 at order 23 and raises the full lower bound to 38. A depth-four run also checked 10,279 active masks at order 20 and strengthened 162 of their bounds. The full lower bound remained 38.

Build the C++17 source with optimization and run the binary with argument `3` to replay this calculation.

## At least three flags require repeated leaves in a 53-gate circuit

A flag is a positive input with just one incident point and line switched on. On that input a proof of truth selects one child at each OR and both children at each AND, unfolding shared uses separately. Call a flag simple if some proof has exactly two leaves. Both endpoints must occur, since a proof using a single endpoint would also accept a singleton.

Let D be the set of simple flags and r the number of AND gates without an OR-only path from their output to the circuit output. When there is a nonsimple flag, r is positive. To see this, take the earliest true AND in a topological listing on that flag. Such an AND exists because an OR-only path from a true raw input to the output would accept a singleton. Both operands of this first true AND have a true OR-only path from a raw input. If the AND had an OR-only path to the output, these paths would give a proof with two leaves.

For nonempty D and positive r, the gate count s satisfies

$$
s \ge |D| + \tau(D) + r.
$$
Here τ(D) is the minimum size of a vertex cover of the simple flags. Start with a live circuit by discarding gates outside the output cone. Mark the output network reached backwards through ORs, stopping at the first ANDs. Keep the raw OR-only expansion of each marked AND operand, substituting zero at every AND encountered in these expansions. This flat circuit accepts exactly the simple flags on pairs and still rejects every nonedge and singleton. The [flat-circuit count](plane-rectangle-separation.md#a-sharp-bound-for-flags-with-two-leaf-proofs) requires at least |D| + τ(D) − 1 gates. In brief, each productive AND yields a star. Assign each simple flag to one covering star. For a center owning m flags through t stars, at least m − t raw OR gates merge the distinct neighbors into those stars. A gate counted at two centers would combine two common neighbors, impossible here. The star ANDs and the output ORs supply the remaining gates.

The flattening removes all r unmarked ANDs **and at least one more gate**. Choose the last unmarked AND in topological order. Its output feeds a successor because the circuit is live. This successor cannot be a marked OR, which would give the chosen AND an OR-only path to the output. It cannot be another unmarked AND by the choice of order. If it is a marked AND, one operand becomes zero, eliminating the gate. If it is an unmarked OR, then in the raw expansion its chosen input is zero, so the OR contracts to its other input or disappears altogether. This OR is never needed in the marked output network. Thus flattening costs at least r + 1 original gates. Marked ORs reachable inside a raw expansion have zero expansion because their raw OR-only paths would accept singletons. Consequently shared marked gates require no duplication in this construction.

For 44 simple flags, the flat count alone gives 54 gates. If 42 or 43 flags are simple, every cover has at least 11 vertices because each vertex covers at most four flags. With r ≥ 1 the stronger count again gives at least 54 gates. Therefore **every circuit of at most 53 gates has at least three flags on which every proof of truth repeats an endpoint**. The argument allows arbitrary sharing. It leaves open whether a circuit exhibiting those repetitions exists.
