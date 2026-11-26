# Which first gates can start a small order-three plane circuit?

[L-meta-3773](https://pequalnp.com/lemma#L-meta-3773) asks for a monotone circuit of at most 63 gates with one of four prescribed first gates. Its opposite is [L-meta-3774](https://pequalnp.com/lemma#L-meta-3774). We prove a sharp bound for circuits in which every shared gate is safe, inactive on the 52 flags, or an OR of two raw inputs from the same shore. A shared gate is an internal output read at least twice in the live circuit. A safe gate can turn on only when some incident point and line are active. A flag is the input turning on just one such pair.

| Prescribed first gate | Minimum gates under this sharing hypothesis |
| --- | ---: |
| OR of points 0 and 1 | 64 |
| AND of point 0 and line 0 | 65 |
| OR of point 0 and line 0 | 65 |
| OR of point 2 and line 0 | 65 |

There is no bound on the number of shared pairs on either shore or their fanout. Unshared gates may combine arbitrary signals. The unrestricted desk claim remains open. The [finite replay](plane-pair-sharing-3773.py) checks each upper bound on the exact posted rows. The [Lean file](PlanePairSharing3773.lean) verifies the extra-row rank argument, cover enlargement and final count, using the [existing rectangle rank lemma](FlagCrossRank.lean). The circuit decomposition and constructions of comparison inputs are justified below.

The posted boundary is sufficient for full incidence. Among all 715 sets of four points the maximum number of lines missing all four is three. Thus every independent assignment has at most three active vertices on at least one shore and is contained in a posted negative input. Every positive input contains a posted flag. Monotonicity extends the prescribed values to the entire Boolean cube.

## Recovering the cover cost on deleted flags

Consider a square-free bipartite graph with m edges and minimum vertex cover size t. In a formula or in a collection of formula pieces selected by the positive row, suppose the virtual inputs are disjunctions of point sets. Count each physical point or line leaf with unit cost. A positive row and negative column follow one path: at an OR use the row to select a true child; at an AND use the column to select a false child. Each leaf gets a rectangle, and its reported input is true on the row and false on the column.

For each point p and each virtual set containing it, choose another member as a mate. Remove every flag (p,l) for which l contains a chosen mate of p. Write H for the retained flags, D for the set of lines having at least one removed flag, and M(p) for the mates at p. Every mate accounts for at most one removed flag by square-freeness. For a retained flag (p,l) use the independent comparison column consisting of the following vertices:

* All neighbors of l except p, including neighbors on deleted flags, together with M(p).
* All retained neighbors of p except l.

The ordinary point and line neighbors cannot be incident, since that would give a four-cycle. The retained lines avoid the mates by construction. At the diagonal, every active virtual point OR is masked by a mate, so the reported label is p or l. At any other retained flag sharing p or l with the diagonal, the comparison must report that shared endpoint. For the same-line case this also holds for any **deleted** positive on l: its other endpoint is present in the comparison column and masks every virtual OR it activates. A common column forcing the point p on its retained rows is M(p) together with its retained neighbors. The whole point shore forces the line on every row of that line.

At each vertex v, take all retained rows incident to v whose diagonal reports the other endpoint. Call their number k. In the matrix of reports of label v, their own comparison columns have zeros on the diagonal and ones off the diagonal. The common forcing column is all ones. These columns have rank k: subtract each comparison column from the common column to obtain unit vectors. If a retained diagonal reports v, include that row as an additional row. If v is a damaged line, one may instead include any deleted row on v. The extra row has a one on every chosen column. The differences still give the original k unit vectors, and the common column gives another independent vector. This includes k = 0. A physical leaf contributes only one rectangle, so its indicator matrix has rank at most one.

Summing the k's charges each retained edge once. The vertices with an extra charge contain both the reported endpoints of the retained flags and all of D. Together these cover **every original edge**. Hence the physical-leaf count is at least |H| + t. This keeps the original cover cost even if deleting the flags isolates a line or destroys all maximum matchings. The same proof works with the shores exchanged.

## Arbitrarily many raw pairs on both shores

Cut the circuit at every shared wire. For each flag choose the first safe shared signal true there, or the output if necessary. Its piece is false on every independent column. Earlier safe terminals and all inactive terminals are false on its positive row, so a comparison cannot end at any of them. Selecting a piece only by the row preserves the rectangle property. A shared raw pair OR has two raw operands which do not belong to an assigned piece. A gate known only semantically to equal that pair OR can first be replaced by its direct raw OR at its original index; delete now-unused gates without introducing any new readers. This replacement is for the lower bound; for the first-gate equality statement use the actual gate operations.

Let hP and hL count the shared point and line pair gates; rP and rL count all their reader slots. Let A be the number of physical raw leaves in the assigned pieces. With s gates, counting operand slots gives

    s + 1 ≥ A + rP + rL + hP + hL.

Indeed the raw slots include A and the two inputs of every pair gate; a pair with r reads contributes r−1 excess internal reads. Other shared wires can only add excess. Trimming unused gates and omitting invalid constant-false reads preserves the inequality. A constant leaf cannot report a difference.

In the first calculation expand every line-pair read into its two raw leaves, and leave point pairs virtual. At most 2hP flags are deleted. In the second calculation exchange the shores. The preceding rank bound gives

    A + 2rL ≥ m + t − 2hP,
    A + 2rP ≥ m + t − 2hL.

Adding the inequalities gives s + 1 ≥ m + t. For the desk graph m = 52 and t = 13, witnessed by the matching p ↦ −p. The same lower bound applies to arbitrary square-free bipartite graphs with a nonempty edge set once isolated inputs are fixed low.

At equality on this plane, if only one shore has shared pairs, the unexpanded-side estimate and r ≥ 2h give s + 1 ≥ 65 + h. If both shores have shared pairs, both estimates must be tight. In the point-virtual test, the reported cover enlarged by damaged lines must have size exactly thirteen and must contain a line: every pair of points lies on a unique line. A size-thirteen cover is a whole shore, by degree four and connectedness. Hence all retained diagonal reports are lines. Each retained flag charges a physical point leaf. The line-virtual test gives the dual bound on physical line leaves. Therefore A ≥ 104 − 2(hP + hL), while the operand count gives s + 1 ≥ 104 + hP + hL. This excludes equality. Without pair helpers, the physical leaf bound is 65; equality leaves no excess internal reads or unused gates. The [minimum-formula characterization](plane-shared-formulas.md#equality-for-formulas) then forces thirteen ordinary stars on one shore joined by ORs.

In such a minimum formula a first gate is an OR of two raw neighbors on the same shore. A same-shore first gate is realized by beginning line zero's star with points 0 and 1. Prepending any of the other three gates unused, and shifting internal addresses, makes a 65-gate circuit as allowed by the desk statement. Moreover, a 63-gate circuit cannot gain a solution by adding just one other shared raw OR with two readers (and allowing all the same-shore pairs). Duplicating that one gate yields at most 64 gates in the class just proved. Equality would be a star formula; it has no repeated nontrivial subtree and contains no mixed raw OR.

## Incident mixed pairs without mate conflicts

The proof also permits shared ORs of incident point-line pairs under the following sufficient condition. At either endpoint of a mixed helper edge, none of its same-shore pair mates is adjacent to its opposite endpoint. With only incident mixed pairs the condition is automatic.

In the point-virtual test, charge each reporting occurrence of a mixed pair (p,b) to a physical line label b on the rows containing b. Restricting a leaf rectangle to such rows still gives a rectangle. On every remaining row where this occurrence can report, p is present. Add all the incident mixed-helper lines of p to its comparison column, and delete their flags at p. Each added line meets the diagonal line only at p, which was excluded, and it avoids the point mates by the stated condition. Thus the diagonal, off-diagonal and common point comparisons still work. For a deleted row on the diagonal's line, either its point is present on the comparison column, or its mixed-helper report was charged to that line. The whole point shore still forces the line on every row. The uncharged part of each mixed leaf is masked whenever this argument needs a physical report. There is at most one extra charged leaf per mixed-helper read. Exchanging shores gives the same bound. Each mixed helper adds one possible flag deletion on either side. The two estimates and the operand count therefore give exactly the same lower bound; the final arithmetic is theorem `bothShores` in the Lean file.

## A single shared disjunction of any width

Suppose now that besides safe and inactive gates there is just one shared signal, an OR of any set Q of raw inputs, with at least two reads. Its private piece has at least |Q| raw slots. Compare the singleton of each member with the assignment of every variable outside Q. Only that member can be reported: earlier safe and inactive terminals are false on the singleton. The selected output pieces have A distinct raw slots outside this producer. Thus s ≥ A + |Q|. A pure-shore OR is covered by the one-shore comparison using one mate per member; no restriction on |Q| is needed.

For a mixed support use the same full-neighborhood columns as above with no mates. Delete a flag if Q is active on it and absent from its comparison column. On every retained diagonal either Q is inactive or it is masked. On a different row sharing an endpoint, an active Q is masked either by that row's other endpoint or because the retained diagonal shares its active endpoint. The same off-diagonal test works for **deleted** rows on either shore, since the canonical column includes all other neighbors on both sides. Both whole-shore base columns mask the mixed OR. Thus, for B deleted flags and their endpoint set U, the extra-row proof gives

    A ≥ 52 − |B| + |U| + matching number of the subgraph outside U.

The [replay](plane-pair-sharing-3773.py) evaluates this bound for all 67,092,481 mixed supports. It takes point-set orbits under verified incidence permutations, counts every line subset for each representative and checks the total orbit weight. Only 312 supports with one member on one shore and three on the other, and 312 with one and four, still admit s < 64 by this estimate. In each such case replace each read in the selected pieces by an OR of the singleton and one virtual disjunction of the larger shore. If the latter has d members, delete at most d flags with the one-shore argument, so A + r ≥ 65 − d. The producer has at least d+1 raw slots and r−1 excess reads. Therefore s + 1 ≥ A + d + r ≥ 65. This excludes every support.

## Several wide disjunctions with one distinguished shore

The one-shore argument also allows arbitrary sharing and nesting among disjunctions which contain at least two lines and at most one point apiece. All other shared signals must be safe or inactive. No width or fanout bound is needed.

For each line l in each disjunction Q, trace that disjunction's private piece on the singleton l and the assignment of all vertices outside Q. A reported input is either raw l or an earlier shared disjunction contained in Q and containing l. In the second case inherit the mate already chosen for l there. In the first, choose another line of Q. Each fresh mate therefore has a distinct physical line slot in a producer piece. If f flags are lost through these choices, there are at least f such slots. In the selected pieces, write a mixed disjunction as the OR of its point and its virtual line disjunction, charging at most one additional physical point leaf per terminal read of a mixed helper. With A physical leaves initially and u such terminal reads, A + u ≥ m + t − f.

For each mixed helper trace its singleton point against the outside of its support in the same way. This either finds a raw point slot in that producer piece or a read of an earlier mixed helper in that piece. These reads are outside the selected pieces. If h helpers are mixed, r is their total fanout, and b is the number of producer raw point slots, then h ≤ b + r − u. Thus the physical slots plus the excess reads pay at least A + f + b + r − h ≥ A + f + u ≥ m + t. This proves the same 64-gate lower bound, with the dual version obtained by exchanging shores.

## One shared point-by-line rectangle

Suppose the only shared signal besides safe and inactive signals is the conjunction of an OR of a nonempty point set P and an OR of a nonempty line set L, and that its input cone has no shared internal signal. Then the circuit also needs at least 64 gates. Its cone must read each of the d = |P| + |L| raw inputs, since each is essential for that conjunction. If the shared signal is safe or inactive the earlier bound already applies. Otherwise its producer is disjoint from the pieces selected by flags and s ≥ A + d.

Write X for the flags in P × L and K for the flags whose canonical comparison column meets both P and L. Use the original cross consisting of all the opposite neighbors of each endpoint except the diagonal endpoints. On K the helper is already one. On a helper-cold row outside X the comparison cannot report the helper. The replay uses three possible sets of retained flags.

1. Keep all rows outside X.
2. Keep flags in K or touching no flag of X, except that any kept flag in X must pass the two forcing tests below.
3. Keep the active flags of set 2. Add any inactive flag in K or touching none of those kept active flags.

“Touching” includes the flag itself and means sharing either endpoint. These choices guarantee that the diagonal of every retained row and its comparisons with retained rows sharing an endpoint report physical labels. For an active retained flag (p,l), to force p, choose a point from P missing l and turn it on with l. To force l, choose a line from L missing p and turn it on with p. Both choices exist by the two forcing tests. For inactive rows the full opposite shore suffices. The local rank bound then gives A ≥ the number of retained flags plus their matching number. Here the forcing column may depend on the row when there is no marker: the [ordinary rank lemma](FlagCrossRank.lean) only needs it for a lone zero diagonal. For two or more zero diagonals the square matrix of ones off the diagonal and zeros on it has full rational rank.

If needed, try an additional excluded positive row on each vertex. On the cross of every retained row incident to that vertex the marker's other endpoint is present. A helper-cold marker therefore forces the vertex there; a helper-active marker is usable when all these crosses are in K. The proposed common base column must contain all opposite endpoints of these rows and the marker. If any row there is active, find a member of the helper on the vertex's shore missing every required opposite vertex, and a member on the other shore missing that chosen member. Together with the required vertices these form an independent input activating the helper. If all rows are cold use the opposite shore. These conditions give precisely the extra row justified by the rank proof. Charge each marked vertex once, and take a matching on the retained edges outside the marked vertices.

The replay exhausts all 67,092,481 choices of nonempty P and L. In 6,591 cases the three ordinary rank tests did not reach 64; the additional-row tests reach it in every case. This result concerns a single shared rectangle with a private producer. Multiple shared computed signals remain outside this argument.

## Search near the 64-gate construction

The [gate rewrite search](plane-rewrites-9767.mjs) can be replayed on this assignment by replacing its punctured graph with all pairs (p,(d+13−p) mod 13) for d in {0,1,3,9}, and changing the two expected sizes to 52 edges and 64 gates. We used both shores as centers, with the ORs in a chain and in a balanced tree. For each of these four circuits the search tried 3,680 single-gate deletions with redirection and all further one-gate rewrites, covering 856,339,680 choices per circuit. None passed the 52 positive rows and 704 distinct maximal independent rows. The choices include NOT as well as both desk operations, allow repeated operands and may encode the same circuit more than once. This search does not decide the unrestricted existence question.
