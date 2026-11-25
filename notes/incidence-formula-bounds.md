# Formula bounds for cases 9757 and 9807

The two desk cases allow shared circuits. These results bound formulas, where each binary gate output has at most one reader. [Reproduce both enumerations](incidence-formula-bounds.py) by running `python3 -B notes/incidence-formula-bounds.py` from the proof repository.

## Case 9807

Deleting the two incidences (0,7) and (0,8) from the Fano incidence graph gives the exact posted 19 edges. The minimum signed formula has **26 literal occurrences and 25 binary gates**, even with negation available for free. The seven point stars attain 25. In particular, a 24-gate ordinary counterexample would have to reuse a binary signal after unary operations are absorbed.

The verifier applies the [signed formula comparison argument](heawood-signed-formulas.md) to the modified graph, retaining only permutations that preserve its edges. It charges mixed occurrences, tests singly read neighbors only where their degrees justify the test, and exhausts the resulting local rectangle assignments at 25 leaves.

For unrestricted circuits, setting input 0 low leaves the thirteen-vertex Fano deletion, whose signed lower bound is 21 in the linked study. Input 0 is essential. Restricting it in a trimmed signed binary circuit saves at least one binary gate, so the posted graph needs at least 22. The seven stars give an upper bound of 25. Separate searches left 12 monotone reader profiles and 44 signed reader profiles unresolved at budget 22. The desk asks for an unrestricted lower bound of 25.

## Case 9757

On the 26-vertex incidence graph a signed formula with only one variable occurring in both polarities needs **at least 65 leaves**. The bound also applies when all variables occur positively. The following are lower bounds on the actual numbered instances after simplifying the formula so that any mixed variable has at least two positive occurrences. A negative occurrence adds a leaf for each such variable.

| Mixed variables | Positive leaves | Total leaves |
| --- | ---: | ---: |
| None | 65 | 65 |
| 0 or 13 alone | 64 | 65 |
| 0 and 1 | 62 | 64 |
| 0 and 13 | 63 | 65 |
| 0 and 15 | 61 | 63 |
| 0, 1 and 2 | 59 | 62 |
| 0, 1 and 13 | 59 | 62 |

Simultaneously rotating the 13 point and line indices gives every singleton on its own shore. The tested same-shore pair and incident pair each exceed the 63-gate ordinary budget for a formula with a genuine negation. Such a formula with at least 64 leaves needs at least 63 binary gates and one NOT. The nonincident representative remains unresolved by this count.

For each vertex, route comparisons between a positive incidence and an independent set to a literal occurrence in the formula. A clean incidence at a vertex has an unmixed neighbor. The column consisting of the clean neighbors forces a positive report of the vertex once on each clean row. If every positive occurrence available on one clean row is also available on another row, call the latter dominated. An incidence cannot be dominated at both ends. The two clean exterior witnesses give a common independent column, because there are no four-cycles. They would require opposite reports on the same comparison. The [local enumeration](heawood-signed-formulas.py) checks possible dominated sets from the positive-occurrence masks.

Assign each dominated incidence to the endpoint dominating it, then assign any remaining incidence to either endpoint. The vertices owning at least one incidence form a cover. A vertex with an opposite endpoint outside the cover must own their joining edge. For each cover the verifier minimizes the local number of positive occurrences over all allowed ownership masks, respecting those forced edges. If a vertex owns $d$ incidences and needs $k$ positive occurrences, its contribution is $k-4+d$. The 26 degrees sum to 104, and the ownership counts sum to 52. Adding 52 to the sum of the contributions therefore gives a lower bound for positive leaves. The script enumerates all 23,168 covers of size at most 20. Larger covers use a size floor of 21 and the largest possible local loss at every vertex.

The 63-gate existence question for unrestricted circuits remains open.
