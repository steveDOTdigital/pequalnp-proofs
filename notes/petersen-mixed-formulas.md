# Formula size with a prescribed OR on Petersen minus one vertex

For desk case L-meta-3174, the edge function on nine vertices requires at least **16 literal occurrences** in a De Morgan formula with any one of the six prescribed ORs supplied for free. The minimum is exactly 16 for the four nonadjacent pairs. For the two adjacent pairs the bounds are 16 and 17. Positive and negative occurrences of every raw input and the helper are allowed. This proves a restriction on the possible 13-gate circuits, whose general case permits arbitrary sharing.

## Counting repeated inputs

Write the helper as u = p OR q. The reflection (1 5)(2 8)(6 7) fixes 0, preserves the twelve graph edges and partitions the six pairs into three classes represented by (1,2), (1,3), (1,8). All nine raw labels are essential even when u is supplied. For a nonendpoint choose a neighbor and toggle the tested input, which leaves u fixed. For an endpoint keep the other endpoint high. If the endpoints are adjacent, the other endpoint alone witnesses dependence. Otherwise turn on a neighbor of the tested endpoint that is nonadjacent to the other endpoint. Such a neighbor exists because the tested endpoint has degree three and two vertices have at most one common neighbor.

Choose a shortest formula and push all inversions to its leaves. Write L for its leaf count and t for the number of helper occurrences. Replacing each helper literal by two raw literals gives a formula for the original graph of size L+t. The [raw formula bound](petersen-formula-size.md) gives L+t ≥ 17.

Among the seven other vertices, the labels repeated in the formula must cover every induced edge. For each such edge ij, turning off the other inputs gives the cofactor i AND j. Turn on a different neighbor of i and a different neighbor of j to obtain i OR j instead. The two neighbors are distinct and nonadjacent because the graph has no triangles or four-cycles. On each cofactor the helper is fixed. If i and j occur only once, all subtrees off their paths to the root become constants. On a cofactor depending on both, the lowest common ancestor must transmit the two literals with its fixed gate operation. It cannot realize both functions. Enumeration of the subsets of the seven vertices gives the following complete list.

| Helper | Minimum covers of the induced graph | Boundary minimum with only the helper allowed negative |
| --- | --- | --- |
| (1,2) | {4,5,8} | 17 |
| (1,3) | {0,7,8} | 16 |
| (1,8) | {2,4,5}, {0,3,7} | 16 |

In particular L ≥ 12+t. If L ≤ 15, then 2 ≤ t ≤ 3. In a minimum formula a nonendpoint appearing at most twice requires only positive literals. The graph is monotone in that variable with all other labels and u fixed, so the [polarity-elimination argument](petersen-formula-size.md) applies. An endpoint that occurs once must be positive by the essentiality test with the other endpoint held high.

If t = 3, the three repeated nonendpoints use all spare occurrences. Only the helper can occur negatively. If t = 2, at most one extra raw label can occur negatively. It must be an endpoint appearing twice, or a nonendpoint appearing at least three times. In the latter case the three distinct repeated nonendpoints form one of the minimum covers in the table. This exhausts all possibilities, including formulas shorter than 15.

## Finite separation calculation

The [checker](petersen-mixed-rectangles.cpp) computes the exact least leaf count needed to separate two finite sets of rows. A single literal has cost one when it accepts every positive row and rejects every negative row. An OR partitions the positive rows and both children must reject every negative row. An AND partitions the negative rows and both children must accept every positive row. Take the least sum over nonempty two-part partitions. If a child is unneeded the other child already separates the rectangle. This proves the recurrence by induction, and testing selected rows gives a lower bound on full formulas. Costs at least 18 may be saturated at 18.

Use the twelve edge rows and twelve maximal independent sets. Include both signs of u, all positive raw literals, and the one possible negative raw literal. For all raw labels allowed by the preceding count the minimum is at least 16, with a single exception on these rows. For (1,3) with raw label 7 allowed negative the boundary minimum is 15. Add the independent set {0,3,6} (row mask 73) to the negative rows. The minimum becomes 16. Thus every permitted pair excludes fifteen leaves.

For the matching upper bounds, start with the five-star formula
`0(1+4+5) + 2(1+3+7) + 3(4+8) + 5(7+8) + 6(1+8)`,
where each numeral denotes its input, juxtaposition means AND and + means OR. For (1,3) substitute u for the indicated sum in the second star. For (1,8) substitute u for the sum in the last star. Either change uses 16 leaves; reflection supplies the other two nonadjacent pairs. The adjacent pairs inherit the raw 17-leaf construction.

## Consequences for circuits

A [Lean proof](PetersenExpansion.lean) expands the actual gate-list evaluator, counting the number of source leaves in its output tree. Raw literals have weight one, an invalid read has weight zero, NOT copies its first operand weight and AND or OR sums its operand weights. Unused operands of NOT are ignored. A constant output has a separate case. Constant folding and pushing inversions to leaves give a formula with at most the computed weight. Specialize the eleven source pins to the nine positive raw literals, negative input 0 and positive u. A circuit computing the graph must have output weight at least 16, even if it uses all thirteen gates.

For a normalized output cone with B binary gates, give a binary gate j multiplicity m(j), the number of times unrolling the circuit visits it. The unrolled tree has 1 + Σ m(j) leaves. Thus Σ(m(j)−1) ≥ 15−B across binary gates in the cone. With thirteen binary gates this requires at least two extra binary-gate occurrences. It excludes a single extra use of a gate whose operands are both input literals when all other binary gates are read once. With one or two gates spent on NOT, at least three or four extra occurrences are necessary, respectively. The counting argument leaves circuits with greater sharing open.

Compile the checker with a C++20 compiler using optimization and execute the result. It checks graph symmetry, covers, upper bounds on all 512 rows and the signed separation lower bounds. Its largest dynamic-programming table occupies 32 MiB.

## A single shared signal with a small input tree

The [single-cut checker](petersen-mixed-second-gate.py) also excludes a circuit whose only repeatedly used computed binary signal is the result of a tree of at most four binary gates. The fan-out of that signal is unrestricted. This is a further finite result about the shared-circuit child.

Contract copies and inversions, allowing a free sign on each use, and replace the shared signal by a new input h. If producing h takes d binary gates, the remaining output tree has at most 14−d leaves. Replacing each occurrence of h with its generating tree adds d leaves. Therefore a suffix with L leaves needs at least ceiling((16−L)/d) occurrences of h. Use 17 in place of 16 when the suffix omits u and the generating tree can use raw inputs only.

The enumerator represents a signal by its 512-bit truth table, identifying complements. It generates the possible tables by splitting a binary tree at the root, choosing signs on both children and taking their AND. This includes OR by De Morgan. A constant, a source literal, or a cheaper equivalent tree can replace a subexpression without increasing the circuit budget. For each helper, the numbers of new tables at costs one through four are 171, 3,361, 70,056 and 1,461,250. The checker considers both possibilities for use of u in the suffix.

For each table, toggle every raw coordinate with the used helpers fixed. Every raw label that changes the target this way is essential. For each graph edge, seek both the AND and OR cofactors with the helpers fixed throughout each four-row test. At least one endpoint of every such edge repeats, by the lowest-common-ancestor argument. Add the number of essential raw labels, the minimum number of repeated labels covering these edges, the required occurrences of h, and one for u if used. If this exceeds the remaining budget, that table is excluded.

At equality each nonessential raw label is absent. Two rows agreeing on every surviving source and disagreeing on the target exclude the case. If the projected target is consistent, enumerate the minimum repeated covers. Any singly used essential raw label is positive. The rectangle checker allows both signs of every repeated label and both helpers, and compares the bound with the suffix budget. At cost two only four projected cases reach this last check across the three representative pairs; their boundary minima are 16,16,15,15 against a budget of 12. At cost three the projected-row collisions settle every tight case. Cost four is checked by the same method.

Run `python3 notes/petersen-mixed-second-gate.py` from the proof repository. It compiles the rectangle helper in a temporary directory and removes it on exit. The finite exclusion covers a single shared computed signal of the stated cost, while circuits with multiple shared signals or a larger shared subtree remain open.
