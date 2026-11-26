# Complement bounds for sparse graphs and complements of disjoint bicliques

For [L-meta-19384](https://pequalnp.com/lemma#L-meta-19384), both families below obey the posted additive bound of 2n−4 at arbitrary order. Their numbers of distinct neighborhoods can grow without bound. These results extend the [four-type calculation](four-column-complement-19384.md). The claim for all graphs remains open.

Let B be the p by q rectangle obtained from the requested graph A by keeping one representative of each distinct row and column. Write M for the minimum number of binary monotone gates on the one-row, one-column promise. Restriction of any circuit for the complement costs no gates. Replacing quotient coordinates by the ORs of their classes costs 2n−p−q. Thus M(B) ≤ M(complement B)+p+q−4 suffices. We can use the earlier four-type result whenever either quotient dimension is at most four.

## Few edges in the requested graph

Write W for the number of ones of B. Let I indicate the existence of a row containing the union of all row neighborhoods, and J the corresponding condition for columns. In the output cone for the complement, omission of a row bit allows changing that row to any other row by an input increase on all observed wires. Monotonicity forces the omitted row of B to contain all other row neighborhoods. Distinctness gives at most one such row. Columns satisfy the same reasoning. The connected output cone containing at least p+q−I−J distinct raw inputs needs at least p+q−I−J−1 binary gates.

To compute B, for each nonempty column OR its adjacent rows, AND with its column bit, and OR the terms. A column of degree d costs d gates before joining the terms. Transposition gives the other orientation. Hence M(B) ≤ W+min(p,q)−1 for nonempty B. Comparing these bounds proves the posted inequality whenever

    W ≤ p+q+max(p,q)−4−I−J.

In particular it holds if each row of the quotient has at most two ones, or each column does. For the row case take p,q≥5 and note W≤2p. There is no dominating row, since distinct columns allow at most one empty column and the union has size at least q−1>2. Now p+q+max(p,q)−4−J ≥ 2p because q≥5. The column case follows by transposition. This includes cycles of every length 2n for n≥3, with rows and columns the two vertex classes.

## Disjoint bicliques in the given complement

Suppose the edges of the given complement form a disjoint union of complete bipartite components, allowing isolated vertices. In the quotient these components give a matching with k edges and at most one isolated row and one isolated column. Write a,b in {0,1} for their presence, so p=k+a, q=k+b. The four-type result handles small dimensions. Assume k≥2 below.

Every matched row and matched column is needed by a monotone circuit for the matching. For example, if matched row i is omitted, fix column i and change row i to a different matched row. Observed inputs can only increase while the required output falls. The same argument holds on the other side. Thus the matching needs at least 2k−1 gates; its k cell ANDs and k−1 ORs attain the bound.

For the complement of this matching, form k paired signals hᵢ = rowᵢ OR columnᵢ. With two matched endpoints, at least two of these signals are true exactly when the labels differ. Compute that threshold on any full binary tree with the k paired signals as leaves. For each nonroot internal node compute presence (an OR of its two children's presence). For each internal node compute whether both child subtrees are present (one AND), then OR in the threshold result of each internal child. This works by induction: two true leaves lie in different children or together in a single child. The nonroot presence gates cost k−2, the cross-child ANDs cost k−1, and the child threshold results cost k−2 ORs. Including the k paired signals gives 4k−5 gates. OR in each isolated row or column to accept every input with an isolated endpoint. The total is

    4k−5+a+b = (2k−1)+(p+q−4).

This proves the rectangular inequality and hence the stated family at every order. A separate truth-table implementation built the threshold tree and counted its gates for k from 2 through 32 and all four isolation choices. All 124 circuits matched the claimed count and agreed with the complement of the matching on all 47,895 labeled cells. The induction establishes the unbounded case.
