# Twenty-seven gates for Heawood formulas

Independent research on PEqualNP desk case L-meta-3005, by steveDOTdigital.

The fourteen input words encode the seven points and seven lines of the Fano plane. Their low 21 positions are its incident point-line pairs, called flags. Their other 37 positions are precisely the maximal independent sets of the incidence graph. The target is 1 on the flags and 0 on those independent sets. Monotonicity extends these tests to all Boolean inputs.

Every binary monotone formula computing this target has at least 28 variable occurrences and hence at least 27 gates. At equality the seven terms are exactly the stars of one shore, combined by OR. The same 27-gate lower bound holds for a circuit with one shared internal gate if its shared function accepts a singleton input, if the formula feeding its shared output uses at most eight gates, or if that formula reads each raw variable at most once. A 26-gate circuit with more extensive reuse remains open.

[Lean proof](HeawoodPartition.lean) · [Finite verification](heawood-rectangle-partition.py)

## The formula lower bound

On input consisting of a flag and a maximal independent set, a formula selects a variable present in the flag and absent from the set. At an OR gate take its first true child on the flag. At an AND gate take its first false child on the independent set. Both properties continue to hold at the selected child. Each formula leaf receives a rectangle of flag rows times negative columns, because every decision on its path depends on only one of the two inputs. These rectangles partition the entire table.

For a flag e, record a Boolean vector over the 37 columns saying whether its point was reported. Two disjoint flags have different vectors. At least one crossed point-line pair is a nonedge, since the incidence graph has no four-cycle. Extend that nonedge to a maximal independent set. Its column forces one of the two flags to report a point and the other to report a line.

At vertex v, call a flag tied if its vector equals that of another flag at v. No flag is tied at both ends. Otherwise the other two flags witnessing the ties are disjoint and have the same vector. Thus at most 21 of the 42 local incidences are tied.

Write k for the number of rectangles labelled v and t for the number of tied flags there. All three flags must report v in some common column, since its three neighbors are independent. If k is one, all three flags are in the same rectangle's row set and all three are tied. If k is two, consider their activity in this common column. When both are active, their row sets partition the three flags. When just one is active, its row set contains all three. In either case there are at most two patterns of membership in the two row sets. Two flags therefore have the same membership, and hence the same orientation vector. For k at least three no further information is needed. In every case,

    9 ≤ 3k + 2t.

Summing over fourteen vertices gives 126 ≤ 3L + 42 for the number L of rectangles. Thus L ≥ 28. The seven expressions “point AND (line OR line OR line)” use 28 leaves, and six OR gates join their outputs. The Lean control evaluates the resulting 27 distinct legal word operations and obtains 2097151.

## The restricted-row bound

More generally, take any nonempty subset E' of the flags, keep all negative columns, and let τ(E') be the minimum number of vertices that meet every retained flag. Every raw-variable rectangle partition of these rows needs at least |E'| + τ(E') rectangles. The proof applies to any bipartite graph of maximum degree three with no four-cycle, using its maximal independent sets as negative columns.

Split each nonisolated vertex into classes of incident edges with equal orientation vectors. The number of classes at a vertex is at most its number of labelled rectangles. For one or two rectangles this follows from the common column argument above, also when some rows have been removed. For three or more rectangles it follows from the degree bound. In the split graph no edge has two endpoints of degree at least two, by the disjoint-flags argument. Each component is therefore a star, possibly a single edge. The total number of split vertices is |E'| plus the number of components. One center per component projects to a cover of E', proving the inequality. It is sharp: assign each edge to one endpoint in a minimum cover and take the OR of the resulting stars. For the empty subset the lower bound is zero.

## Structure at equality

For a 28-leaf formula, the local price inequalities must all be equalities. Two rectangles cost strictly more than the local minimum, as do four or more. Thus seven variables have one occurrence apiece and the other seven have three apiece. The seven single-occurrence vertices are independent, since every incident flag there is tied. Their degrees account for all 21 edges. The complementary vertices are therefore independent as well. Connectedness makes the two sets exactly the two shores.

Suppose the lines have single occurrences. Fix a line l as the only possible active line, and vary the point set P. Raising the unique leaf for l makes the output equal the disjunction N(l) of its three incident points. This is the conjunction of the values, with all lines off, of siblings at the AND gates along the path from that leaf to the root. If one such sibling is false, the value no longer depends on l and the all-lines-off result is false. If all are true, the path transmits true to the root.

Each of those sibling functions thus accepts all three singleton points on l. At least one rejects the complement of l. By monotonicity its point-only function is exactly N(l). Select one such subtree B(l) per line. They are distinct, since the seven functions are distinct. For each p on l, the part of B(l) outside its proper selected subtrees must contain a leaf p. Otherwise, when the singleton p is replaced by the complement of l, every maximal proper selected subtree becomes true, since its own line contains a point outside l. All remaining leaves there can only rise. This contradicts the change of B(l) from true to false. The seven disjoint regions thus use all 21 point leaves.

No line leaf lies inside any maximal selected subtree. With all points high and all lines off, all these subtrees are already true and the root is false. Raising an internal line leaf changes no maximal selected subtree, even though that input must make the root true. It follows that the B(l) are disjoint. If B(m) were properly inside B(l), its parent AND and the sibling containing the leaf m would also be inside B(l). Each B(l) now contains just its three point leaves, and its two gates must both be OR.

Write G(l) for the parent AND of B(l). No other line m can occur anywhere under G(l): choose a point on m outside l and activate m alone. Then B(l) is false, so the output would be unchanged on removing m. Consequently the seven G(l) are disjoint, and each contains exactly its three-point disjunction and its own line leaf. All remaining gates join these seven terms. Each term can be the only true term, so all these joining gates are OR. The argument interchanges the two shores. In particular no minimum formula repeats the same gate on the same two raw variables. A circuit whose unfolding is a minimum formula therefore cannot share any internal gate: two copies of a shared subtree would repeat a bottom gate.

## One shared internal result

Delete unused gates. Suppose H is the unique gate with multiple uses. Its input cone is a formula of g gates. Replacing each of its d ≥ 2 occurrences in the remainder by a special input leaves an outer formula. In a circuit with at most 26 gates this outer formula contains at most 27 − g leaves, of which at most 25 − g are raw. Call a flag hot when H is true there, and a negative column warm when H is true there.

On cold flag rows the special input cannot report a difference, so the outer raw leaves must supply at least |E'| + τ(E') rectangles for the cold flags E'. On warm columns the special input likewise cannot report a difference. Thus the raw leaves must partition all 21 rows on the warm columns within the same budget. These are necessary conditions independent of how the outer formula uses H.

If H accepts two singleton inputs, every column containing either variable is warm. For each of the three unordered pair orbits the verifier excludes a raw partition of 24 rectangles on those columns. This contradicts g ≥ 1.

If H accepts exactly one singleton c, then H = c OR h, where h is its formula with c set to zero and the resulting constants simplified. When h is nonzero it has at most g leaves and uses only other variables. If h is zero the circuit is a formula after replacing the helper by c. The columns containing c require exactly 19 rectangles. Adding any one of the other 25 columns makes 19 insufficient. Thus g ≤ 6, and at g = 6 every warm column must contain c.

Here is how the small finite check handles all the one-singleton cases, including repeated variables. If h is zero on all negative columns, evaluate the outer formula with H replaced by c and add h at the output by OR. This is a formula of at most 26 gates agreeing on all columns. If F consists of the hot flags away from c, the same repair works using the exact graph function of F whenever |F| + τ(F) ≤ g. It costs |F| + τ(F) − 1 gates for nonempty F, plus one joining gate. On flags at c, the ordinary input c already preserves every helper success. Empty F needs no joining gate. Either repair contradicts the formula lower bound.

Every flag in F has both endpoints among the leaves of h, since no second singleton is accepted. The verifier enumerates the possible leaf multisets for h, padding shorter ones by idempotence. It skips a support when even its induced flag set admits the preceding cheap repair, or when even its smallest possible cold subgraph costs too much. It enumerates both operations at every remaining tree split. After the two-singleton warm bound and the stated repairs and cold bounds, the counts of remaining distinct warm masks at g = 1 through 6 are respectively 0, 0, 0, 24, 114 and 0. At g = 6 this also uses the extra-column test. Every one of the 24 and 114 masks exceeds its outer raw budget in the checked partition search.

Finally, if H accepts no singleton, all its hot flags have both ends among at most g + 1 raw inputs. Removing every flag induced by such a support still leaves a subgraph of minimum price 27, 26, 24, 23, 21 and 20 respectively at g = 1 through 6. Each exceeds 25 − g.

## A read-once shared formula of arbitrary size

Suppose the formula feeding H reads each of its raw variables at most once. We may assume H accepts no singleton, by the preceding result. Split all OR gates above the first AND gates. Each top AND has children on disjoint variable sets. For a positive two-vertex input to satisfy this AND, one vertex must be in each child, and that singleton must make its child true. A raw leaf among the top OR terms would give a true singleton and is impossible.

In each AND, retain the endpoints of all flags accepted by that AND. Replace each child by the OR of the retained vertices on its side. This preserves all its accepted flags and only decreases its values on negative columns. It uses at most as many leaves as before. A term with no accepted flags can be dropped. If the accepted flags in a term have several connected components, split it into one product of two disjunctions per component. Each component uses its own point and line shores: the child partition is a two-coloring of the connected bipartite component, unique up to reversal. Making the split preserves all its flags and uses the same number of leaves. The new expression is a formula, so its gate cost is exactly the number of remaining leaves minus one.

We have reduced to a family of pairwise vertex-disjoint connected induced graphs, each with an edge. For each graph take “some point in the component AND some line in the component,” and combine by OR. Each connected graph is induced on its vertices because every incident pair inside one component makes its product true. Extra positive flags would also be harmless. The resulting helper covers every originally hot flag and can only lose warm columns, so replacing H preserves the target. If it is zero on all negative columns, simplify the outer formula with the helper set to zero and OR the helper itself at the output. Simplification removes at least one outer gate or leaves a constant. This gives a formula within the 26-gate budget.

For a family using n vertices its gate cost is g = n − 1. The outer raw-leaf budget is again at most 25 − g. We can strengthen the cold-row lower bound by counting isolated vertices of the cold subgraph. At any warm maximal independent set T, every vertex v outside T has a neighbor in T. That flag must report v, so some outer raw leaf must carry v. Any such vertex isolated in the cold subgraph is an additional cost beyond its edge-plus-cover lower bound.

The verifier finds 5,755 connected vertex subsets containing an edge, and enumerates their pairwise disjoint families without repetitions. For g ≥ 7 it discards families that exceed the cold-row bound with these extra vertices, and any warm mask containing all columns through one variable, which already needs 19 leaves. This leaves 420 distinct triples of gate count, hot flags and warm columns. At g = 7 through 13 the numbers of inclusion-minimal warm masks are 21, 84, 21, 21, 84, 0 and 0. Every one exceeds the available raw budget. This excludes every read-once shared formula.

In particular a helper of seven or eight gates with a repeated raw variable would use at most seven or eight distinct vertices respectively. Their best possible cold prices are 20 and 18 respectively, exceeding outer budgets of 18 and 17. Thus every single-helper circuit within 26 gates would require a helper with at least nine gates, a repeated raw variable, and no true singleton. Two or more shared internal gates also remain possible.

## Verification

Lean's `formula_lower` constructs the formula protocol, proves that each leaf gives a rectangle, and applies the incidence count to the desk's literal words. The finite geometry uses kernel evaluation. The theorem `upper_control` checks the legal 27-step word program. The equality classification, restricted-row argument and circuit deductions are given above.

Run `python3 notes/heawood-rectangle-partition.py` with the repository's Lean toolchain installed. A rectangle labelled v uses a nonempty subset of its three incident rows. Rectangles with identical label and row subset merge by union of their column sets, leaving 98 possible pairs. The SAT encoding limits the number selected. Each checked column independently chooses enabled pairs with an absent label that cover every flag exactly once. CaDiCaL checks its UNSAT proofs internally, and the script replays every SAT control. It also reconstructs the 37 maximal independent sets and verifies the automorphism orbits used to reduce the cases.
