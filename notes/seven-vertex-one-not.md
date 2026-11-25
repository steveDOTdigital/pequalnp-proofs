# One negation on the seven-input graph in case 11088

The seven-input function has a 12-gate AND/OR circuit. Lean proves that every circuit for the function using at most one NOT can be replaced by a monotone circuit of no greater size. The local project checker accepted the exact posted statement and rechecked 2,783 constants. The submitted file has its own certificate of the six-input signed lower bound. A separate C++ calculation gives the stronger seven-input signed minimum of 12. [Upstream proof submission](https://github.com/open-goat/pequalnp-proofs/pull/15584)

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

The 730-prefix calculation establishes the six-input signed minimum independently of the Lean certificate. The unrestricted seven-input calculation gives the 12-gate signed minimum.

## The Lean lower-bound certificate

The kernel proof works backwards from the output to identify the wires still needed after every gate. With `k` gates remaining, at most `k+1` such wires can participate. Two input assignments with different target values must disagree on at least one live wire. These restrictions leave 4,978 representative wire sets across all gate budgets after identifying the prism’s twelve vertex symmetries. The checker enumerates every legal next AND with either input optionally inverted, including every possible decision to reuse an operand. Each viable successor must match a recorded representative under an actual graph symmetry. The lookup hash only proposes a match. Lean checks the wire permutation before using it.

The [finite-search argument](PrismSignedFrontier.lean), [input and target tables](PrismFrontierData.lean), [certificate data](PrismFrontierCertificate.lean), [kernel checks](PrismClosure.lean), and [connection to the posted circuit semantics](PrismOneNotBound.lean) are included. The [data generator](prism-frontier-lean.py) uses the [standalone C++ enumerator](prism-frontier-certificate.cpp) and regenerates the stored table deterministically.

## Where a useful negation would have to occur

There is also a restriction using the already proved [monotone prism lower bound](https://github.com/open-goat/pequalnp-proofs/blob/fdf35ff0e30a2a395d0b1337ca148bc55d77ae33/lean/PEqualNP/Outside/L_meta_742.lean). In any circuit of length at most eleven for this target with exactly one NOT, the wire feeding that NOT must take **both** Boolean values on the slice where input 0 is false.

Suppose the wire were constant on the slice. Replace the NOT output there by the corresponding opposite constant. Input 0 must reach the output along a path avoiding the NOT. Otherwise increasing input 0 from false to true could only increase the input to the NOT, decrease its output, and decrease the final output, since all other gates are monotone. In fact enabling input 0 in the presence of vertex 3 alone makes the target rise. Thus an AND or OR on a path avoiding the NOT directly reads input 0. The output cannot itself be raw, since the target depends on all seven inputs.

After pinning input 0 to false, eliminate this direct reader by constant propagation or by copying its other operand. The NOT is already a constant. Remove the remaining constants and copies to obtain an AND/OR circuit for the nonconstant prism using at most nine gates. The project's gate operations of arity zero or one and default-false reads obey the same simplifications. Relabel the prism in the order 1, 3, 5, 4, 6, 2. The two triples are triangles and the three matching edges join the corresponding positions. This contradicts the checked monotone lower bound of ten. In particular, a negation of input 0 itself, or of any monotone subcircuit that becomes constant when input 0 is false, cannot shorten the seven-input circuit.
