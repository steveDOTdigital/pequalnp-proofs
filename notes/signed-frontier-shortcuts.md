# Two ways to check a signed circuit frontier

[Case 11088](https://github.com/open-goat/pequalnp-proofs/pull/15584) uses the six-input triangular prism to rule out a shorter circuit. A frontier records which wire values can still feed a computation with a given number of binary gates left. All 64 truth-table rows are available, and complementing a wire is free in this lower-bound calculation.

## Testing thirteen negative rows together

For each wire, store its truth word in thirteen 64-bit lanes and the corresponding negative input value repeated across each lane. Bitwise agreement then tests all pairs of a positive row and a negative row in parallel. If a positive row agrees with a negative row on every remaining wire, no continuation can distinguish them.

[The vector proof](PrismVectorClosure.lean) establishes each lane’s meaning, proves that signed gate operations preserve it, and connects a zero mask to the original closure test. [The supporting definitions](PrismPackedClosure.lean) also contain a slower verified variant that uses the mask to suggest a single row and checks that row explicitly. The compact case 11088 certificate uses the direct vector proof and verifies the wire sets returned by its lookup table.

## Ruling out a root partition

When m distinct wires remain and only m−1 binary gates are available, every wire must be used. A first gate merges two wires and leaves a suffix that is tight again. Working backward from the output shows that its two operands depend on disjoint nonempty parts of the initial wires.

For a proposed partition, an AND root is impossible if one negative row agrees with a positive row on the first part and with a possibly different positive row on the second. Reversing the two colors rules out an OR root. This also covers complemented operands. If every partition fails both tests, the state can be discarded. [Lean verifies this necessary condition](SignedRootSplit.lean). The [executable rejection test](SignedRootRejection.lean) enumerates the partitions and checks the opposite-colored rows with 64-bit intersections. Lean proves that a rejected state has no continuation within its gate budget.

[The reproducible prism calculation](signed-prism-root-split.py) starts from the existing public frontier. It applies the partition test and follows the surviving transitions. A separate native generation with the same test gave the same counts.

| Gates left | Original reachable states | After the partition test |
| --- | ---: | ---: |
| 4 | 62 | 1 |
| 5 | 2,002 | 54 |
| 6 | 2,520 | 1,990 |
| 7 | 384 | 384 |
| 8 | 9 | 9 |
| 9 | 1 | 1 |
| **Total** | **4,978** | **2,439** |

The numerical counts come from the search programs. The compact single-file case proof currently checks all 4,978 states using the vector method.
