# The nine-input graph in case 11016

An exhaustive circuit search found a minimum of **16 gates** for the posted edge function, even if each wire can be complemented for free. [The Lean proof](NineVertex11016.lean) verifies a circuit of size 16, an unrestricted lower bound of 15 and necessary conditions for any circuit of size 15. A Lean proof excluding the last size is still open.

## Construction

The circuit takes the OR of five stars. Each center is ANDed with the OR of its assigned neighbors.

| Center | Assigned neighbors |
| --- | --- |
| 0 | 4, 5, 6 |
| 1 | 5, 7, 8 |
| 6 | 2, 3 |
| 7 | 2, 4 |
| 8 | 3, 5 |

These terms cover all twelve edges and take twelve gates to build. Four OR gates combine them. Lean checks the circuit on all 512 inputs.

## What a 15-gate circuit would have to do

Pinning vertex 2 low gives the eight-input graph in [case 8455](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_8455.lean). Pinning vertex 3 low gives [case 8459](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_8459.lean). Both require fourteen gates. The reader and gate-elimination lemmas from [case 8451](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_8451.lean) give the 15-gate lower bound.

In a minimum circuit with at most 15 gates, both vertex 2 and vertex 3 would have exactly one gate reading them. Each reader must be an OR. A second reader, or a single reader forced to a constant on the low restriction, would save two gates and violate the corresponding eight-input bound.

Whenever flipping one of these vertices changes the output, a companion signal at its OR reader cannot be high on both inputs. Lean verifies that every other raw vertex is high on some such pair, ruling out a raw companion. If the companion computes the conjunction of two distinct other vertices, its pair must be one of the ten remaining graph edges or one of the following three extra pairs.

| Unique reader of | Additional allowed pairs |
| --- | --- |
| Vertex 2 | (0, 1), (1, 3), (3, 4) |
| Vertex 3 | (0, 1), (1, 2), (2, 5) |

## Exhaustive search

The [search driver](nine-vertex-table-two.py) establishes the proper induced-subgraph bounds before using them. It found 53 distinct nonempty proper graph types. Their exclusions used 887 reader profiles and 3,704,866 prefixes. On the full graph the signed search excluded 789 profiles in 36,667,170 prefixes. A separate AND/OR search excluded 789 profiles in 623,960 prefixes. The native checks completed without a timeout.

The following command replays the search from the root of the proof repository.

```sh
python3 -B - <<'PY'
import runpy

driver = runpy.run_path("notes/nine-vertex-table-two.py")
edges = [(0, 4), (0, 5), (1, 5), (0, 6), (2, 6), (3, 6),
         (1, 7), (2, 7), (4, 7), (1, 8), (3, 8), (5, 8)]
driver["CASES"]["11016"] = (edges, 16)
driver["run"](65, 2, True, "11016")
PY
```
