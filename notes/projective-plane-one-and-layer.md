# A 63-gate incidence circuit would need nested AND gates

For the order-three projective plane in L-meta-650, the minimum size is **64** among monotone fan-in-two circuits with at most one AND gate on every input-to-output path. The count allows arbitrary sharing of OR gates on either side of the AND gates. This is a restricted lower bound. The unrestricted 63-gate question remains open.

## Counting gates

Let a nonempty bipartite graph have edge set E, cover number τ and no four-cycle. Its edge function is true when both ends of some edge are true. Consider a circuit of the stated kind computing this function. Discard dead gates, propagate constants, and bypass unary gates and OR gates whose output equals one of their inputs. These simplifications preserve the function and can only decrease size.

Above the AND gates, the output is an OR of their values. No input can occur as another term in this OR, since a single active vertex never makes the edge function true. Write r for the number of distinct AND gates contributing to the output. Connecting r sources to one output takes at least r−1 binary OR gates, even with sharing. Indeed, the underlying undirected graph is connected, and each binary gate provides at most two edges.

Each AND computes a product of two nonempty disjunctions of inputs. Their supports are disjoint, again by the single-vertex test. Every pair with one endpoint from each support must be an edge, by the two-vertex test. Conversely every graph edge must be covered by some such product. If both supports had at least two vertices the graph would contain a four-cycle. Each product therefore describes a star. Assign it to the singleton endpoint, choosing either endpoint for a one-edge star. The chosen centers form a vertex cover, so r ≥ τ.

For a center v let tᵥ denote its number of products and dᵥ the number of distinct neighbors covered by those products. Trace the disjunction on the neighbor side of each product back to its input variables, including a bare variable as a one-node trace. The union of these traces has dᵥ sources, say gᵥ binary OR gates and at most tᵥ connected components. Counting undirected edges gives dᵥ + gᵥ − tᵥ ≤ 2gᵥ, hence gᵥ ≥ dᵥ − tᵥ.

Every OR gate in such a trace contains at least two distinct variables after simplification. If it were traced for distinct centers v and w, those two variables would be common neighbors of v and w, giving a four-cycle. Thus these gates can be summed over centers. The traces cover all edges, so Σdᵥ ≥ |E| and Σtᵥ = r. There are at least |E| − r preprocessing gates, r AND gates and r − 1 output gates. Their sum is at least **|E| + τ − 1**. The bound is attained by assigning every edge to an endpoint in a minimum cover, taking one star product per used center, and ORing the products.

## The assigned graph

The 13 points each have four incident lines, giving 52 edges. Two different points share exactly one line. A matching covering the points has line indices, in point order 0 through 12,

    13  15  14  19  18  17  16  22  21  20  25  24  23

These distinct indices occur in the posted incidence list. The matching forces cover number at least 13 and the points themselves attain 13. Thus the bound gives 52 + 13 − 1 = 64. Using the point stars takes 39 OR gates for their neighborhoods, 13 AND gates and 12 final OR gates.
