# A 25-gate circuit for matrix 11871860300395540620

[L-meta-20327](https://data.pequalnp.com/data/lemma/L-meta-20327.53b400188b70.json) asks for at most 24 fan-in-two AND/OR gates on the one-per-side promise. We constructed a 25-gate circuit and proved that 25 is optimal within the four-product form described below. The unrestricted 24-gate question remains open. The catalogue already records a verified [27-gate upper bound](https://data.pequalnp.com/data/lemma/L-meta-20099.10cba253851e.json).

## Construction

Number rows 0 through 7 and columns 8 through 15. Each integer mask below denotes the OR of its selected raw signals. Compute the AND for each pair, then OR the four products.

| Left union | Right union |
| ---: | ---: |
| 8256 | 49542 |
| 5140 | 776 |
| 2080 | 21017 |
| 20609 | 33794 |

The construction uses 18 shared union gates, four AND gates and three final OR gates. Lean 4.36.0 checked the size, gate types and all 64 row-column pairs. [Lean proof and gate list](EightByEight20327.lean)

## Why four products need 25 gates

Eight accepted cells, in row order, have columns 2, 6, 0, 4, 3, 1, 7 and 5. No all-one rectangle contains two of these cells: for each pair, at least one cross cell is zero. Every rectangle cover therefore needs at least eight rectangles.

An AND of two unions of raw row and column signals covers at most two rectangles. The two unions must have disjoint row supports and disjoint column supports, since a shared signal would accept an entire row or column. Four such products must consequently induce eight nonempty rectangles, each with its own distinguished cell. Enlarging each rectangle to a maximal one still gives eight distinct rectangles.

There are 20 maximal all-one rectangles and six ways to cover the matrix with eight of them. Shrinking those rectangles, retaining coverage and pairing rectangles with disjoint supports gives 263 distinct families of required operand masks. For any one family, a union shared by two required operands must be a subset of their intersection. Enumerate every such optional mask. For each selected family of shared masks, build the selected masks and required operands in increasing size. If the fewest available masks covering a new mask is `k`, combining them uses `k−1` OR gates. This calculation allows overlaps and counts previously built masks once. It includes an optimal circuit: select every intermediate used by two or more required operands. Gates used exclusively by one operand can then be replaced by a tree on its available inputs.

Six operand families need 18 union gates, and every other family needs more. Adding four ANDs and three final ORs establishes the restricted lower bound. The calculation permits arbitrary sharing in the union stage. Circuits with other arrangements of AND and OR gates remain possible at size 24. [Reproduce the exact enumeration](matrix-20327-four-products.py)
