# The nine-input graph in cases 10830 and 10831

The two desk rows ask opposite questions about a 14-gate circuit. Our independent exhaustive search finds that the minimum is **15**, even when wire inversions are free and only binary gates count. Hence the result supports row 10830. Lean checks a 15-gate construction, an ordinary circuit lower bound of 14, and a restriction on the first gate. The last step from 14 to 15 is currently a C++ calculation.

## The checked bounds

Five stars centered at vertices 0, 1, 2, 7, and 8 cover the eleven edges. Assign each edge to its first center in that list. The disjunction of the five star expressions uses 15 gates. Lean tests the resulting circuit on all 512 Boolean inputs.

Pin vertex 3 low. Relabel the remaining vertices in the order 0, 4, 7, 6, 1, 2, 5, 8. The restricted function is exactly the eight-input graph whose ordinary lower bound of 13 is checked in upstream case 8439. Vertex 3 genuinely affects the original function, and its low restriction is nonconstant, so pinning saves at least one gate. The nine-input ordinary minimum is therefore at least 14. The Lean argument uses the upstream pin and relabeling lemmas from case 8451. [Construction and reduction](NineVertex10831.lean) · [Upstream eight-input lower bound](https://github.com/open-goat/pequalnp-proofs/blob/73da90ce3f609cf2573e115b479d152147fea8ea/lean/PEqualNP/Outside/L_meta_8439.lean) · [Upstream gate elimination](https://github.com/open-goat/pequalnp-proofs/blob/73da90ce3f609cf2573e115b479d152147fea8ea/lean/PEqualNP/Outside/L_meta_8451.lean)

For every ordered pair of distinct raw inputs `i, j`, and for either value of `j`, Lean finds an assignment where changing `i` changes the output while `j` stays at that value. Consequently a direct AND or OR of `i` and `j` cannot be the sole reader of either operand. Set the other operand to its blocking value. The first gate then stays constant on the sensitive pair of assignments, as does every raw input visible downstream. This conclusion also holds if input or output inversions are free, by choosing the corresponding blocking value.

## Exhaustive lower bound

Run `python3 notes/nine-vertex-table-two.py --case 10831` from the repository root with a C++17 compiler. The calculation verifies the proper induced graphs in increasing order and then searches every allowable raw-input read profile of a circuit at the unresolved budgets. The signed gate search evaluates each candidate on its full truth table. A 15-gate star construction supplies the upper bound. A timed-out profile prevents the verifier from reporting an optimum.

| Search | Profiles | Prefixes visited |
| --- | ---: | ---: |
| Proper induced graphs, 54 isomorphism types | 48 | 2,240 |
| Full nine-input graph | 281 | 835,619 |

The source is the same [raw-input profile verifier](petersen-raw-prefix.cpp) used for case 11023, with the new graph selected by the [driver](nine-vertex-table-two.py). The remaining formal task is to certify the exclusion of an ordinary circuit at exactly 14 gates. The 15-gate witness alone cannot settle that question.
