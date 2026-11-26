# How many gates does deleting an AND-read vertex save?

[L-meta-3568](https://pequalnp.com/lemma#L-meta-3568) asks about a least binary AND/OR circuit for the edge function of a four-cycle-free bipartite graph. It asks for a circuit after deleting all the edges incident to z, saving at least the degree of z. If the residual graph has an edge and its minimum vertex cover is smaller, it asks for one more gate. The premise requires some AND gate to read z directly. The posted opposite is [L-meta-3571](https://pequalnp.com/lemma#L-meta-3571). The catalogue retired 3569 and refiled the same Lean term as 3571.

We prove the requested savings whenever all but one of the neighbors of z are private leaves, with no bound on the rest of the graph. We also verify the full conclusion for 348 of the 385 six-by-six incidence types with a perfect matching. All graphs on at most eleven active vertices were already covered by the five-vertex-cover theorem. The unrestricted assignment remains open.

## An exact deletion with one attachment to an arbitrary residual graph

Let H be any nonempty graph, where nonempty here means it has an edge. Choose a vertex u, add a new center z adjacent to u, and give z exactly k ≥ 1 new private leaves. Write M for minimum binary AND/OR circuit size. Then

    M(G) = M(H) + k + 2.

This does not require bipartiteness, a girth hypothesis, or an AND reader. For the upper bound OR the k leaves and u, AND the result with z, then OR this term with the old circuit. These are k+2 new gates.

For the lower bound begin with one private leaf p. With p high the output is F(H) OR z. Its minimum cost is M(H)+1. Pinning the essential z low in any circuit bypasses a reader and recovers F(H), and one extra OR attains that bound. With p low the output is F(H) OR (z AND u). Its cost is also at least M(H)+1. The flag {z,u} makes z essential, and pinning z low again leaves F(H).

Consider a first reader of p in a least circuit. Pin p to its controlling value, zero for AND or one for OR. This gate becomes constant. It has a consumer since both cofactors are nonconstant, and every gate in a least circuit is live. The consumer also folds, so at least two gates disappear. Either residual costs at least M(H)+1 by the previous paragraph. The original circuit therefore needs at least M(H)+3 gates. For k>1 pin k−1 private leaves low successively. At each step the next leaf is essential, the cofactor is nonconstant and at least one gate disappears. This gives the full lower bound.

Deleting z leaves H with ignored inputs. Its cover number drops by exactly one. Adding z to a minimum cover of H covers G. Conversely a cover containing z must also cover H, and one omitting z contains every new private leaf in addition to covering H. Since the degree of z is k+1, the saving k+2 realizes the stronger desk bound exactly. In particular, attaching any pendant path of even length 2j to an existing graph increases the minimum by exactly 3j, by applying the one-leaf case j times.

If z has only private-leaf neighbors and H has an edge, the separate star also costs exactly k+1 extra gates. Set all k leaves low one by one, pinning the last leaf to its first reader's controlling value instead if necessary. A direct proof is to remove k−1 twin leaves for one gate each, then pin one endpoint of the isolated edge to a controlling value. Both cofactors have H as a further restriction and at least two gates disappear. If H has no edges, the graph is just the z-star and isolated inputs. The star has k+1 essential inputs and hence costs at least k binary gates, attained directly. In the desk model the empty residual uses no gate and an output address beyond the input array, which evaluates to false.

## Other consequences of the exact quantifiers

For a nonempty residual H, write d for the degree of z, t for the minimum cover size of G, and t' for that of H. Then t−t' is either zero or one, since adding z repairs a cover. Set U(G)=|E(G)|+t−1. The star construction costs U(G), and

    U(G) − U(H) = d + (t−t').

Consequently if G attains the star lower bound, using the star construction for H proves the posted witness for every z. More generally the desired inequality for a particular eligible z is equivalent to U(G)−M(G) ≤ U(H)−M(H), by choosing a least D. The comparator in the Lean statement ranges over all covers of G, so its extra unit is exactly the cover-number drop. The [cover-five proof](incidence-helper-3491.md) therefore settles every original graph with cover at most five, of arbitrarily large order.

There is a direct circuit test as well. If r distinct gates read z and some is an AND, pinning z low removes all r. That AND has a consumer when H has an edge. The consumer cannot also read z in a least circuit, because combining z with z AND W gives an existing wire for either operation. Thus at least r+1 gates disappear. This proves the full demand for r ≥ d and the basic demand for r ≥ d−1. It covers every degree-one vertex in the stated premise and degree two when the cover does not drop.

## The twelve-vertex boundary

At most eleven active vertices implies a bipartite cover of size at most five. At twelve, the only further possibility has six vertices on each shore and a perfect matching. Deleting any vertex from such a graph leaves cover exactly five. It leaves an edge, and the new optimum is known by the cover-five theorem. In these instances a shortfall of one gate below U(G) would thus translate exactly to a one-gate shortfall in the requested savings whenever the least circuit has an AND-read vertex.

The [finite replay](and-read-deletion-3568.py) grows a line neighborhood at a time on six points. A neighborhood is a nonempty six-bit mask. Two masks may meet in at most one bit. Repeated singletons are allowed. After adding each line, order the points by degree, try every permutation within equal-degree classes, and sort the line masks. Permutations of an earlier representative extend to permutations of its possible next masks. At six lines, identify transposes and retain perfect matchings. This gives exactly 385 incidence types under point and line relabeling and shore exchange.

| First applicable lower bound | Types reaching the star size |
|---|---:|
| Removing a peelable leaf | 282 |
| A shore of maximum degree two in each component | 2 |
| At most one cycle per component | 7 |
| Minimum degree two and one more edge than vertices | 4 |
| Shared-wire singleton and cofactor counts | 53 |
| **Total certified** | **348** |

The [leaf-peeling proof](cyclic-core-peeling.md#removing-leaves) uses a sibling leaf or a parent of degree at most two. Every proper restriction here has cover at most five after isolated OR inputs are split off. The degree-two and sparse cases use the [subdivision theorem](single-read-cover-kernels.md) and [pseudoforest and strict fanout bounds](pseudoforest-circuits.md). For the last 53 the replay exhausts the candidate shared-wire responses one gate below U(G) with the [previously justified exit tests](incidence-helper-3491.md). It installs the exact cover-five bound for every proper restriction and asserts the matching hypothesis on each use.

There are 37 unresolved types, listed by the replay. Repeating the same exit test at lower budgets leaves a one-gate interval for 36. For masks (12,21,26,38,41,48) the remaining interval is 19 through 21 gates. These intervals do not supply any circuit smaller than the star construction.

The 348 conclusions extend to families of arbitrary order. For any one certified graph, fix one minimum cover. Attach new private leaves at any of its vertices. Each new leaf can be pinned low for at least one gate of savings, while the same cover adds its edge into a star for one additional gate. The cover size stays fixed by the original matching. The enlarged graph therefore still attains its star bound and satisfies the deletion statement for every eligible vertex. One can also attach any sequence of the length-two pendant paths proved above. Each path increases both the minimum circuit size and the star bound by three.
