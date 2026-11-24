# A forced NOT in the flipped-input Petersen case

In L-meta-3248 the physical input yᵢ is the complement of the original graph coordinate at one vertex i outside {0,6}. The other eight coordinates have their original signs. The extra signal is y₀ OR y₆. The target on the physical cube therefore decreases along an i-edge whenever the selected other vertices form an independent set containing a neighbor of i. A monotone circuit fails on at least one endpoint of each such pair. A 13-gate solution has either one or two paid NOTs: adding one binary gate for the prescribed OR and absorbing signs gives a raw circuit, which [requires at least twelve binary gates](petersen-gate-elimination.py).

In the one-NOT case let h be the input to that NOT. Treat its output as a free bit t. The remaining output function K(y,t) is increasing in each physical input and in t because every other gate is monotone. For every comparable pair v ≤ w for which the target falls from true to false, h(v) = false and h(w) = true. Otherwise monotonicity would give true ≤ false for the actual circuit. For every point z of the interval [v,w], monotonicity now forces K(z,false) = false and K(z,true) = true. [Lean proves this interval identity](PetersenFlippedInput.lean) over any preorder.

The [enumerator](petersen-flipped-intervals.py) checks all comparable pairs in the 512-row cube. The source pin map preserves and reflects this order. Monotonicity forces h to zero below the lower endpoints and to one above the upper endpoints.

| Flipped vertex | Descending pairs | Forced zero rows of h | Forced one rows of h | Rows with K(y,t) = t | Two-gate candidates below / above yᵢ |
| --- | ---: | ---: | ---: | ---: | --- |
| 1 | 125 | 44 | 224 | 64 | 1 / 9 |
| 2 | 125 | 44 | 224 | 64 | 0 / 10 |
| 3 | 125 | 44 | 224 | 64 | 0 / 10 |
| 4 | 77 | 36 | 192 | 44 | 2 / 13 |
| 5 | 125 | 44 | 224 | 64 | 0 / 10 |
| 7 | 77 | 36 | 192 | 44 | 1 / 13 |
| 8 | 125 | 44 | 224 | 64 | 0 / 10 |

A first binary AND or OR cannot supply a distinct function to the unique NOT. Of the ten source signals only yᵢ has the forced values, and the enumeration excludes every other function of one binary gate. Two gates have either an equivalent one-gate expression, or a gate combining a source and a one-gate signal. After removing cheaper equivalents, every two-gate candidate satisfying the forced values is pointwise below yᵢ or pointwise above it. The counts in the table are necessary conditions. They leave the full one-NOT and two-NOT lower bounds open.
