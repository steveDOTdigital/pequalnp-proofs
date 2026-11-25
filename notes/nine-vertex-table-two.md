# The nine-input circuit minimum in L-meta-11022 and L-meta-11023

The ordinary AND/OR/NOT circuit minimum is **16**. The same minimum holds when every wire and the output can be inverted for free and only binary gates are charged. The lower bound comes from the reproducible exhaustive calculation below. Lean independently checks the 16-gate upper bound and an unconditional ordinary lower bound of 15.

The negative desk statement L-meta-11023 asks for a circuit using at most 15 ordinary gates. L-meta-11022 gives the positive lower bound. These results concern one finite Boolean function in the project's Table 2.

## Construction

The six-cycle is 0, 5, 8, 6, 2, 7. Vertices 1, 3 and 4 make triangles on its edges 5–8, 6–8 and 0–7. The following five terms cover every edge exactly once.

```text
0 AND (4 OR 5 OR 7)
1 AND (5 OR 8)
6 AND (2 OR 3 OR 8)
7 AND (2 OR 4)
8 AND (3 OR 5)
```

Combining their outputs with OR takes four more gates. There are seven OR gates inside the terms and five AND gates, giving 16 in total. The [Lean construction](NineVertexTableTwo.lean) checks the posted input order, circuit semantics, allowed operations, fan-in and size.

## Signed lower bound

Number vertex subsets by their nine-bit masks, with vertex 0 in the low bit. For every subset the [verifier](nine-vertex-table-two.py) removes isolated vertices and groups isomorphic active graphs. It compares the actual relabeled edge sets. It visits subsets in increasing order and uses an exact proper-subgraph bound only after proving it. Each graph has the constructive upper bound `edges + minimum vertex cover − 1` from a cover of its edges by stars.

For the lower bound start with the number of essential inputs minus one. Pinning a vertex low leaves its induced deletion. Pinning it high gives the OR of its neighbors and the edge function on its non-neighbors. Each independent alarm in that OR costs at least one gate above a nonconstant residual, by pinning the alarm low. When no residual edge remains, the cost is the number of alarms minus one. The same connected-cone argument charges inputs lost on a restriction with nonconstant output. This first stage needs no formula bound specific to a graph family.

When the pin bounds fall short, the driver tests every possible number of direct gate reads of each raw input. If a vertex has r readers, pinning it removes those readers. If z of the readers are forced to constants on that pin, at least `min(2,z)` further gates can be removed in a minimum signed circuit. Two forced readers with just one common consumer can be factored by their shared literal. A similarly redundant nested reader can first be rewritten. For simultaneous zero pins, a gate joining two constant signals produces another constant signal. Charging that outgoing signal until it meets a surviving nonconstant branch accounts for the two original reads. A constant restricted target is excluded from this argument. See the [single-pin and first-gate derivation](petersen-raw-bound.md) and [simultaneous restriction checks](petersen-profile-cuts.hpp).

Every remaining profile goes to the [signed circuit enumerator](petersen-raw-prefix.cpp). It schedules pairs of distinct earlier wires, tries both signs of each operand, and normalizes each signal to false on the all-zero row. Constants, repeated signals and gates that do not reach the chosen output can be removed in a minimum circuit. The search checks distinctions between opposite target values and savings available from prefix gates on induced subgraphs. The only formula leaf bound supplied here is one plus an already established circuit lower bound on a nonconstant subgraph. It does not presume that a star is a minimum formula.

All 49 nonempty proper active graph types attained their star bounds. Eight types required nonempty circuit searches.

| Vertex mask | Exact signed size | Reader profiles | Prefixes visited |
| ---: | ---: | ---: | ---: |
| 362 | 8 | 3 | 38 |
| 435 | 10 | 4 | 20 |
| 477 | 11 | 1 | 6 |
| 487 | 11 | 24 | 1,113 |
| 495 | 13 | 14 | 2,911 |
| 503 | 14 | 275 | 792,406 |
| 507 | 14 | 79 | 60,983 |
| 509 | 13 | 5 | 3,062 |

Together these are 405 profiles and 860,539 prefixes. On the full graph in vertex order 0 through 8, the low-pin lower bounds are 12, 13, 14, 14, 13, 12, 12, 12, 11. The high-pin bounds are 9, 10, 10, 10, 11, 8, 10, 11, 9. At budget 14 every reader profile or first gate is ruled out before enumeration. At 15 gates the search excludes all **461 signed profiles**, visiting **14,225,848 prefixes**. Restricting the final search to AND/OR gives another complete exclusion in **320,255 prefixes**. The 16-gate positive control passes all 512 input assignments. The verifier treats a timeout as an incomplete result.

## Kernel checks and reproduction

[The deletion argument](NineVertexDeletion.lean) uses the project's [previously proved case 8451](https://github.com/open-goat/pequalnp-proofs/blob/fdf35ff0e30a2a395d0b1337ca148bc55d77ae33/lean/PEqualNP/Outside/L_meta_8451.lean). Pinning input 2 low removes at least one gate. In the order 8, 5, 1, 3, 6, 0, 4, 7, the remaining function is exactly case 8451 and needs 14 gates. Thus every ordinary circuit needs at least 15 gates. Lean also proves that in a minimum circuit of size 15 exactly one gate could read input 2, and its operation would have to be OR. Two distinct readers would both disappear on the low pin. A lone AND or NOT reader would become constant and eliminate a second gate. Either outcome would leave at most 13 gates for case 8451. Lean also checks that the OR reader cannot take a different raw input as its other operand. For each candidate input there are two rows with that input true where flipping input 2 changes the target. A direct OR of those two inputs would already be true on both rows. The theorem `ordinaryFromSigned` transfers a 16-gate signed lower bound to the exact ordinary lower bound. The numerical exclusion of the final size uses the external verifier. A kernel proof of that last exclusion is still needed for the positive desk statement.

From the root of the proof repository, run the following with Python 3 and a C++17 compiler. The second search is optional. The command below runs both the signed and the AND/OR exclusions.

```sh
python3 notes/nine-vertex-table-two.py --monotone-check
```
