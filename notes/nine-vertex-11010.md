# Fifteen gates on the nine inputs of case 11010

An exhaustive search gives minimum size **15** for the posted graph, even with free wire inversions. A separate search using only AND and OR gates reaches the same result. Lean verifies a 15-gate construction and an unrestricted lower bound of 14. It also proves that any smallest 14-gate circuit would have exactly one reader for each of the five inputs numbered 0 through 4. The full 15-gate lower bound still needs a Lean certificate.

## Construction and five restrictions

Use the OR of four stars. Their centers and assigned neighbors are shown below.

| Center | Neighbors |
| --- | --- |
| 5 | 0, 1 |
| 6 | 2, 3 |
| 7 | 0, 2, 4 |
| 8 | 1, 3, 4, 5, 6 |

Each star uses one gate per assigned neighbor. The four stars account for all twelve edges, and three further ORs combine them.

Fixing input 0 or 2 to zero gives the eight-input graph in checked case 8515. Inputs 1 and 3 give case 8525, and input 4 gives case 8517. Each smaller graph requires at least 13 gates, including when NOT gates are allowed. The [Lean proof](NineVertex11010.lean) supplies the five label maps and proves the resulting function equalities. It uses the gate-elimination and reader lemmas from upstream case 8451. An essential leaf has a reader. Two distinct readers would both simplify on its zero restriction, leaving at most 12 gates. This proves the single-reader conclusion for all five inputs.

## Exhaustive calculation

The [replay driver](nine-vertex-table-two.py) starts with the essential-input lower bound and proves the subgraph bounds in increasing vertex count. Its 55 proper induced graph types need 158 signed searches covering 28,030 prefixes. On the full graph it checks 41 canonical reader profiles at budget 14, exploring 127,619 signed prefixes. Restricting the last stage independently to AND and OR checks all 41 profiles in 2,781 prefixes. All reported profiles end in an infeasibility result. The driver verifies the 15-gate upper witness as a positive control. The signed search also bounds ordinary circuits because dropping the cost of inversion can only decrease the minimum.

Input 8 can have as many as five readers at budget 14. The [prefix verifier](petersen-raw-prefix.cpp) and [profile encoder](heawood-high-cofactor.py) retain the original two bits for the first four counts and use a third bit when a larger count is needed. Replaying case 10831 preserved its 281 profiles and 835,619 signed prefixes.

Run `python3 -B notes/nine-vertex-table-two.py --case 11010 --monotone-check --seconds 90 --workers 2` from the proof repository. The Lean source uses the four named upstream modules at their published statements.
