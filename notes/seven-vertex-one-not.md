# One negation on the seven-input graph in case 11088

The seven-input function has a 12-gate AND/OR circuit. An independent exhaustive computation finds that it needs 12 binary gates even when every wire can be inverted for free. Hence a paid NOT cannot produce a shorter circuit. The exact signed lower bound is currently external to Lean.

## Upper bound

Take the OR of the following three products. Each product is precisely a complete bipartite subgraph of the posted graph.

```text
5 AND (1 OR 3)
(4 OR 5 OR 6) AND (0 OR 2)
(0 OR 1 OR 6) AND (3 OR 4)
```

There are seven ORs inside the factors, three ANDs and two final ORs. The [Lean file](SevenVertexOneNot.lean) checks their cost and compares the output on all 128 inputs to the desk's list-indexed predicate.

## A smaller sufficient certificate

Pinning input 0 to false leaves the triangular prism on vertices 1 through 6. Its triangles are (1,3,5) and (2,4,6). Its matching joins 1 to 4, 3 to 6, and 5 to 2. The pin is nonconstant. At the input with only vertex 3 true, flipping vertex 0 changes the unrestricted target.

Lean uses these two witnesses to prove that a circuit for the seven-input function gives a signed program for the prism whose binary gate count is strictly smaller than the original number of paid binary operations. If the original list is already monotone, it is its own replacement. Otherwise at least one operation is a NOT, so the paid binary count is also strictly smaller than the original length. A signed prism lower bound of 10 therefore forces length at least 12, and the displayed circuit supplies the required replacement. This transfer accommodates arbitrary NOT counts and the project's default values for invalid reads.

## Exhaustive calculation

Run `python3 notes/seven-vertex-one-not.py` from the proof repository with a C++17 compiler. The [verifier](seven-vertex-one-not.py) first constructs upper bounds by covering every induced edge set with bicliques. It visits subgraphs in increasing vertex count. Single-pin bounds, possible raw-input read counts, all legal first gates and the complete [signed-prefix checker](petersen-raw-prefix.cpp) supply lower bounds. No previously asserted prism optimum is used. Smaller-than-cover witnesses found on masks 63 and 123 are checked on every truth row. A timeout gives no exclusion.

| Active vertex mask | Exact signed binary size | Best biclique-cover formula | Reader profiles searched | Prefixes visited |
| ---: | ---: | ---: | ---: | ---: |
| 63 | 7 | 8 | 4 | 34 |
| 123 | 9 | 10 | 38 | 2,826 |
| 126 (prism) | 10 | 10 | 14 | 730 |
| 127 (full graph) | 12 | 12 | 62 | 24,587 |

The 730-prefix prism calculation is the remaining kernel-certification target for the shorter proof. The separate unrestricted seven-input calculation verifies the stronger 12-gate signed minimum.
