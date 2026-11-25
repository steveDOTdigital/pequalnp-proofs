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

The implementation also enumerates the first two gates for active induced subgraphs obtained by deleting up to three vertices. At order 21 it strengthens 60 of 1,997 active masks. It checks 275 masks at order 22, all 24 at order 23 and raises the full lower bound to 38. This computation does not close budgets 38 through 53.

Build the C++17 source with optimization and run the binary with argument `3` to replay this calculation.
