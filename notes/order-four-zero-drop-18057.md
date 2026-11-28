# Certifying the restricted circuit by its surviving flags

Independent work on L-meta-18057, using the [posted restrictions](https://data.pequalnp.com/data/desk/gaps.json) and the [previous checked erasure trace](order-four-erasure-traces-18057.md).

The [Lean proof](OrderFourZeroDrop18057.lean) shows that redirecting an erased gate to a pinned-false raw wire can only lower the output on the restricted rows. It uses the actual desk `eraseGate`, including its renumbering and the value false assigned to nonexistent wires. Ordinary exact-copy erasures can be interleaved with zero redirects. A gate that is false on the maximal allowed input is false throughout the restriction, so it has an exact redirect to a pinned zero. This test uses the complement of the union of the pins as the maximal input.

For the incidence predicate, a true row contains a surviving flag. If the final circuit of a certified trace accepts each surviving flag, monotonicity gives every true restricted row. The one-sided erasure proof excludes false positives. Lean checks the mixed trace theorem, including dead-gate steps and exact-copy steps, for any positive basis with this covering property.

For zero redirects alone, a circuit can retain any set of gates containing an accepting witness for each surviving flag. A true AND requires all of its operands and a true OR needs one true operand. The chosen witnesses continue to evaluate after any unneeded gates are redirected to zero. Conversely, an accepting witness in the shortened circuit traces back to retained gates of the original circuit because its true signals cannot come through a pinned zero.

The [replay](order-four-zero-flag-erasures-18057.cjs) checks all fourteen masks. Each surviving flag has a unique accepting tree in the usual 125-gate star circuit. The union of these trees is mandatory for zero redirects, and the replay independently verifies a trace erasing every gate outside that union. The exact zero-only maxima range from 37 to 45 erasures. The [full-length traces](order-four-star-erasures-18057.cjs) also use redirects to equivalent wires and reach 67, 72 or 76.

The replay also inserts a same-shore AND with a live path to the output of a redundant branch. Its wire differs from every earlier raw wire on the restricted cube. Redirecting it to pinned zero still preserves every flag and the entire restricted function, which exercises the mixed trace criterion beyond exact wire matching.

The posted erasure counts remain open for arbitrary circuits of at most 124 gates satisfying the activation and cold-OR hypotheses.
