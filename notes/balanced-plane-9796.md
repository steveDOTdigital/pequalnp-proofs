# A balanced 44-edge incidence graph

Case L-meta-9796 asks whether 54 binary monotone gates suffice on its 24 inputs. The exact formula size is **55**. The same minimum holds if all shared intermediate wires are ORs of pairs of raw points. In fact, any circuit in that class using even one genuinely shared pair needs at least **56** gates. The unrestricted monotone circuit minimum lies between 38 and 55.

## The 55-gate formula

The two shores each have 12 vertices. Group the points incident with each line into an OR, AND that output with the line input, and OR the twelve stars together. The 44 incidences cost 44 gates inside the stars, and eleven more gates combine them. The graph has no four-cycle. Its twelve matched incidences give minimum vertex cover 12, so the flag-cross rank bound requires 44 + 12 leaves. A binary tree with 56 leaves needs 55 gates. The [Lean proof](BalancedPlane9796.lean) also verifies the exact 44 labeled edges against the existential edge predicate and checks every gate of the construction.

## How much a shared pair costs

The graph contains a spanning cubic subgraph with 36 edges. One explicit choice is the union of three perfect matchings. In the list below, entry j gives the point matched to line 12+j.

| Matching | Points in line order |
| --- | --- |
| First | 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 |
| Second | 2, 4, 11, 6, 5, 8, 7, 3, 9, 10, 0, 1 |
| Third | 8, 2, 3, 4, 0, 1, 9, 10, 11, 5, 6, 7 |

Suppose h distinct shared wires are ORs of raw point pairs. Cutting these wires yields a formula with h additional input labels, each used at least twice. The [shared-pair rank argument](OneShorePairRank.lean) retains at least 44 − 2h labeled edges. If a cover of the retained edges has k vertices, it hits at most 3k cubic edges. Only eight edges lie outside the cubic subgraph. Hence the number of retained edges is at most 8 + 3k. Combining this bound with the rank charge for the physical leaves, the two references per shared wire, and the cost of building each pair gives

$$3s \geq 165 + h,$$

where s counts gates. Thus this class needs at least 55 + ⌈h/3⌉ gates. The [Lean proof](BalancedPlaneSharing.lean) verifies the finite cubic subgraph, the cover count and the final inequality for arbitrarily many pairs. Exchanging points and lines gives the same counting argument on the opposite shore.

## Unrestricted circuits

Running the [gate-elimination recurrence](cubic-pair-restrictions.cpp) on the 44 posted edges gave a signed lower bound of 37 and a monotone lower bound of 38. The [two-gate prefix check](punctured-plane-pins.cpp), using this case's edge list, checked 2,016 active induced graphs on 21 vertices, 276 on 22, 24 on 23 and the whole graph. These checks did not raise the bound. Arbitrary sharing, including combinations of different kinds of intermediate results, remains the obstruction to the 55-gate lower bound.
