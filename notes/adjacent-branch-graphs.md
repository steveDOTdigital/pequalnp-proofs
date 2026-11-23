# Two adjacent branch vertices reduce to one twelve-vertex graph

Consider a finite graph of maximum degree three and girth at least seven, with at most two degree-three vertices, adjacent if both occur. For the edge function with AND, OR and NOT gates, the sharp lower bound of L-meta-519 holds throughout this class except possibly for graphs having the theta graph with path lengths 1, 6 and 6 as a connected component. **The whole class satisfies the proposed bound if and only if this one twelve-vertex graph needs eighteen gates.** Its minimum is either seventeen or eighteen.

This concerns the case with at most two branch vertices in the whole graph. The assignment also allows further branch vertices elsewhere.

## Classifying the induction steps

Use the project's good-leaf and six-vertex-run induction. A good leaf is a leaf whose neighbor has degree at most two or has another leaf neighbor. A run is a path of six distinct vertices with its four internal vertices of degree two and both ends of degree at most two. The checked induction steps use the lower bound on smaller vertex deletions, including edge functions with additional disjoint singleton OR inputs. The code exposes the steps separately, so individual exceptional base graphs can be supplied in an ordinary induction on the edge count. [Good-leaf and run steps](../lean/PEqualNP/MetaComplexity/Helpers/EdgeFnGraphPlan.lean)

Vertex deletion preserves the stated degree and adjacency conditions. Consider a connected component with edges and neither reduction. A path has a good leaf, a cycle of length at least seven has a run, and a tree has a good leaf. For the last fact, root a tree at a leaf and consider a farthest leaf and its parent: any other child of that parent is also a leaf. If the parent has just one child it has degree at most two.

Every remaining leaf is adjacent to a degree-three vertex, with at most one such leaf at each branch. For a connected graph the number of independent cycles is 1 + (number of degree-three vertices minus number of leaves)/2. With one branch, the only cyclic case is a cycle with one leaf attached directly to the branch. The cycle has six consecutive vertices of degree two, so there is a run.

With two branches and two leaves, the leaves are attached one per branch. Removing both leaves leaves a cycle in which the two branches are adjacent. If the cycle has length at least eight, the other vertices include a six-vertex run. The remaining case is the seven-cycle with a leaf attached at each end of a chosen edge.

With two branches and no leaves, suppress the degree-two paths. If there is a loop at one branch, there is one at each, and the original connecting edge links the two cycles. Each cycle has at least six vertices besides its branch, giving a run. Otherwise there are three internally disjoint paths between the branches. Their common endpoints are adjacent, so one path has length one. Each other path has length at least six by girth. Any length at least seven supplies six consecutive internal vertices of degree two. Thus the only remaining graph is the theta with lengths 1, 6 and 6.

In a disconnected graph without a reduction, there can be only one component containing edges: either exception already uses both branches. Moreover an induced copy of the exceptional theta must already be a component of the original graph. Its two branches have full degree, and an extra neighbor at any other theta vertex would create a third branch.

## Paying for the seven-cycle exception

The seven-cycle has seven edges and cover number four. A minimum cover can contain both ends of its chosen edge, by alternating on the other path. The two new leaves leave the cover number at four and add two edges. Pin them false successively. Each remains essential until fixed, and pinning an essential input in a normalized circuit removes at least one consuming gate, also in the basis with NOT. The remaining cycle needs at least 7 + 4 − 1 = 10 gates by the checked peelable-graph bound. The decorated cycle therefore needs at least twelve, and the cover construction attains twelve. [Peelable-graph theorem](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/MetaComplexity/L532.lean)

The same one-gate argument handles the extra disjoint OR variables required by the induction. Pin them false one at a time before applying the ordinary base bound, and set isolated unused inputs to false. Now induct on the number of edges for graphs without a theta component. Either one of the checked steps applies or the graph is the decorated cycle up to isolates. If the eighteen-gate base bound for the theta is supplied, the same induction covers the full stated class. Necessity follows by taking the theta itself.

## The last gate of uncertainty

The theta has thirteen edges and cover number six. Both branch vertices and the second and fourth internal vertices of each long path form a six-vertex cover. The twelve-cycle made of the two long paths has a perfect matching of size six. The cover construction consequently uses eighteen gates.

Delete the middle vertex of one long path. Eleven edges remain, and the cover number is still six. For example, writing the paths as u-a₁-a₂-a₃-a₄-a₅-v and u-b₁-b₂-b₃-b₄-b₅-v, deleting a₃ leaves a seven-cycle on u,v and the b-path. It needs four cover vertices, and the disjoint edges a₁a₂ and a₄a₅ need one each. This smaller graph has no theta component and therefore needs at least 11 + 6 − 1 = 16 gates. Pinning a₃ false saves at least one gate, giving seventeen for the theta.

The finite check traverses all 512 induced subgraphs of the decorated cycle and all 4,096 of the theta. Up to isolates, the theta has four proper induced subgraphs with edges and neither checked reduction; each is the decorated cycle. [Reproducible enumeration](adjacent-branch-graphs.py)
