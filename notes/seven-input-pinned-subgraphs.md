# Pinning inputs in seven-vertex edge functions

Three independent proofs show that allowing a single NOT gate cannot shorten a binary monotone circuit for the posted edge function. Their explicit monotone circuits use 12 gates for case 10776, 10 for case 11509 and 9 for case 11882. Each complete file was accepted locally by the upstream statement checker.

A circuit that uses no NOT is already an eligible replacement. For a circuit that uses a NOT, count that gate separately and lower-bound the number of binary operations even when complements are free. Pin one input low. In the live computation of an essential output, deleting an essential input in this way saves at least one binary operation. The [projection lemma](SignedPinProjection.lean) checks this step on the finite truth tables, including repeated uses of a wire. Each successive deletion requires a new essentiality check on the current function.

## Case 10776

First pin vertex 0. The remaining graph has a universal vertex over a disjoint triangle and edge. Each of the other five inputs can be removed to leave a five-input function that needs at least eight signed binary operations. A putative nine-operation circuit would have to read each of these five inputs only once. The controlling value of either operand of its first binary operation would then mask an input that remains essential. The [six-input proof](UniversalSix.lean) verifies every possible first operation. Its [finite certificates](SmallSignedCertificates.lean) exclude circuits below the required sizes for the two-triangle friendship graph and the four-clique. The latter bound lifts to a four-clique with a pendant vertex.

This gives ten signed operations on the restriction, eleven before the pin and twelve gates once the NOT is counted. The matching monotone circuit shares the OR of inputs 3 and 5. [Complete submitted proof for case 10776](https://github.com/open-goat/pequalnp-proofs/pull/15886)

## Cases 11509 and 11882

Case 11509 has a ten-gate monotone circuit sharing the OR of vertices 5 and 6. The [complete independent proof](../lean/PEqualNP/Outside/L_meta_11509.lean) settles the affirmative statement and therefore rules out its negation in case 11510. [Upstream credited edisonhello's earlier proof](https://github.com/open-goat/pequalnp-proofs/pull/15413).

In case 11882, pin vertices 1, 4 and 2 low, in that order. The remaining four vertices induce a diamond. Its finite certificate rules out four signed binary operations. Restoring the three input dependencies and counting the NOT gives at least nine gates, matching the explicit circuit. [Complete submitted proof for case 11882](https://github.com/open-goat/pequalnp-proofs/pull/15979)
