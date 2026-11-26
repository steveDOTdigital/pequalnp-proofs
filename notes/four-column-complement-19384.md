# Complementing a promise graph with four column types

For [L-meta-19384](https://pequalnp.com/lemma#L-meta-19384), **the 2n−4 overhead holds whenever either side has at most four distinct neighborhood patterns**, for every n≥3. This includes every graph of order three or four. The coefficient and constant are sharp already on a single exceptional row and column. The [opposite statement](https://pequalnp.com/lemma#L-meta-19385) is the exact negation of the desk claim. A proof or counterexample for arbitrary numbers of patterns remains open.

Appending a NOT to a monotone circuit for the complement of A represents A itself. Thus the [previous NOT-removal result](promise-monotonicity-19158.md) gives the required 2n−4 bound when either side has at most three types or both have at most four. This argument interprets the output wire correctly even if the old circuit selected an absent wire, by reading false through a fresh invalid index in that case.

## Reduction to rectangular graphs

Take one representative per distinct row and column. An s-gate monotone circuit for the complement restricts to the rectangular complement without increasing its size: set the unused raw inputs to false and renumber its wires. Conversely compute the OR of each group of equal-pattern indicators and apply a rectangular monotone circuit for A. With p row types and q column types, this costs 2n−p−q extra OR gates. See the [compression argument](promise-monotonicity-19158.md#compression-when-both-sides-have-duplicate-patterns).

It remains to consider q=4 and p≥5, after transposition if necessary. Here 5≤p≤16. A rectangle B is entirely specified by a subset of the sixteen four-bit row masks; the rows are distinct. Retain those sets for which the four columns are also distinct. There are 62,461. It suffices to show M(B)≤M(complement B)+p, where M is monotone circuit size.

## Lower and upper bounds for the rectangle

If a raw row indicator of the complement is missing from the output cone, its neighborhood in B must contain every other row's neighborhood. Indeed, switching from the omitted row to any other can only increase the inputs seen by the monotone cone. The complement output can only increase, so the original B output can only decrease. At most one such row exists. The same holds for the four columns. Let I and J indicate whether B has such a dominating row and column. The complement needs at least p+4−I−J distinct raw signals. Its connected fan-in-two output cone therefore needs at least L=p+3−I−J gates.

For an upper bound, first compute the OR of the row indicators adjacent to each column, AND it with that column's raw bit, and OR the resulting terms. If W is the total number of ones, W+3 gates suffice; empty columns can be skipped. A full row may instead be ORed directly into the final output, saving three gates in this bound. Two row indicators occurring together in k column sums can be ORed once and replaced by that wire in all k sums, saving k−1 gates. The replay finds the maximum saving from disjoint pairs by a subset recurrence: leave the first row unpaired or try each possible partner. This verifies the required inequality for 61,906 rectangles.

For the remaining 555, the replay also reuses intermediate ORs. When two signals are present in the same set of k≥2 sums, create their OR for those sums and keep their separate occurrences elsewhere. Each such step saves k−1 gates. Different tie choices supply valid constructions; optimality of the procedure is unnecessary. This leaves 409 rectangles.

Attaining the raw-signal lower bound L would require a read-once tree. Restricting such a tree to three rows and three columns keeps it read-once, after pinning the other indicators to zero and folding constants. On a three-by-three promise there are exactly 362 read-once monotone tables, allowing any subset of the six raw coordinates and constants. The replay generates them by all binary AND/OR joins on disjoint sets of raw coordinates. If any restricted table of the complement is absent, replace L by L+1. Only 21 cases remain.

## Explicit circuits for the last 21

All have five row masks, including the full row. A row mask of weight three misses one column. Pair its row indicator with that missing column's indicator by OR. If there are four such rows, the test that at least two paired bits are true is exactly the mismatch test on their four labels. The four paired ORs, a seven-gate threshold test and one final OR for the full row cost twelve gates.

Otherwise there are three such paired bits h0,h1,h2 and an exceptional fourth column c. Their threshold test is

    (h0 AND h1) OR ((h0 OR h1) AND h2).

Together with the three paired ORs, that costs seven gates. If the remaining row is empty, OR the threshold with the full-row bit and with c AND (h0 OR h1 OR h2). Reusing h0 OR h1 from the threshold gives eleven gates. In the other cases the remaining row accepts c and at most one additional column. The column c is then universal. OR the threshold with the full-row bit and c, and add a single cell by AND and OR if required. This costs at most eleven gates. The replay evaluates each explicit circuit on every cell and compares its size with L+p.

The [standalone replay](four-column-complement-19384.cjs) verifies all counts in one run with Node.js. It is an external computation, and the assignment asks for an unrestricted Lean proof.
