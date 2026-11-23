# Independent P-NP results

## Official submission

Our vertex-cover proof shows that a cover of size t contains every vertex of degree greater than t. Omitting such a vertex would put all its neighbors in the cover. The project checker accepted the exact assigned statement locally and rechecked 1,061 constants. The desk acknowledged our submission. Upstream closed it after merging an earlier proof. [Our PR #1005](https://github.com/brilliant-hq/pequalnp-proofs/pull/1005) · [Merged PR #979](https://github.com/brilliant-hq/pequalnp-proofs/pull/979)

## Circuit sizes

| Assignment | Result | Evidence |
| --- | --- | --- |
| L-meta-741, triangular prism | The minimum monotone fan-in-two size is 10 in our search. The solver ruled out nine gates, both in one complete run and in all six canonical first-gate cases. Lean checked an explicit ten-gate circuit. The desk acknowledged the report that the posted nine-gate existence claim appears false. | [Lower-bound search](check-small-cover-bound.py) · [Lean construction](../lean/PEqualNP/Outside/L_meta_741.lean) |
| L-meta-700, bowtie | The minimum weighted cost is 10. An exhaustive solver run with internal proof checking excluded each gate count from 1 through 9 at cost at most 9. The matching construction uses three AND gates, three wide OR gates and two narrow OR gates. | [Search and construction](check-small-cover-bound.py) |
| L-meta-612, edge-and-cover bound | The bound holds in our exact searches for all 43 isomorphism classes with an edge, no four-cycle and two through six nonisolated vertices. Removing isolated vertices preserves the result by fixing their input bits to false. The largest unresolved run was split into all ten canonical first-gate cases, each of which returned UNSAT. The general theorem remains open. | [Small-graph search](check-small-cover-bound.py) |
| L-meta-652, three cyclic matchings | The unrestricted minimum is between 12 and 15 inclusive. CaDiCaL with internal proof checking excluded all circuits through 11 gates. A 14-gate search with one fixed five-gate output circuit also returned UNSAT. Lean checked the 15-gate construction and a five-gate lower bound for the last matching even with arbitrary functions of the other six edge products supplied for free. Unrestricted runs at 12, 13 and 14 timed out. | [Synthesis search](search-three-matchings.py) · [Lean proofs](../lean/PEqualNP/Outside/L_meta_652.lean) |
| L-meta-582, Heawood graph | After building six ordinary line stars, a suffix needs at least nine further gates, even with NOT gates and every parenthesization of those six stars available. This excludes a 26-gate circuit of that form. | [Lean proof](../lean/PEqualNP/Outside/L_meta_582.lean) |
| L-meta-650, order-three projective plane | Exactly 64 gates suffice when each path uses at most one AND gate. The lower bound allows shared OR gates. | [Counting argument](projective-plane-one-and-layer.md) |
| L-meta-651, Petersen graph | Lean checked a 20-gate circuit. Testing a family of 1,030,360,500 repair descriptions around that circuit found no 19-gate witness with a NOT. This count includes duplicates and covers only the stated family. | [Lean results](../lean/PEqualNP/Outside/L_meta_651.lean) · [Search](search-petersen-one-not.py) |
| L-meta-606, incidence functions | Lean checked the bounded-line-degree size bound and the exceptional-line lemma for an AND output with a line-independent factor. | [Lean proofs](../lean/PEqualNP/Outside/L_meta_606.lean) |

The exact synthesis scripts use the CaDiCaL executable distributed with Lean. To reproduce the prism search, run `python3 notes/check-small-cover-bound.py /path/to/cadical --prism --seconds 600`. Use `--bowtie` in place of `--prism` for the weighted bowtie search. A timeout prints `UNKNOWN` and leaves that case unresolved.

## Permanent and verification assignments

The standard six-dimensional cross in the four-by-five matrix problem has no strict level-space extension. The argument generalizes to the standard cross in every rectangular size with 3 ≤ p ≤ q. Other constructions could attain larger dimensions. [General proof](maximal-cross.md) · [Exact four-by-five certificate](check-cross-extension.py)

For five-by-five matrices, an eight-dimensional level space needs at least 15 available entries. Only one 15-entry pattern survives the tests up to row and column permutations and transpose. A nine-dimensional level space needs at least 18 entries, with just one surviving 18-entry pattern up to row and column permutations. A surviving pattern is a candidate for further work. [Exact support enumeration](check-sparse-level-spaces.py)

The earlier Lean work covers the four-by-five dimension filters, the three-block checkpoint protocol, and an obstruction to a grammar-compression approach to the faster verifier. [Matrix lemmas](../lean/PEqualNP/Outside/L_gct_215.lean) · [Verifier lemmas](../lean/PEqualNP/Outside/L_lib_123.lean)
