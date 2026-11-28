# Factoring an OR between AND gates in L-meta-8059

[L-meta-8059](https://data.pequalnp.com/data/desk/gaps.json) asks for a 63-gate lower bound for two readouts with at most one AND gate directly reading another AND. The [Lean control](PlaneTwoOutputs8059.lean) verifies a 63-gate circuit against the project definitions, including both exclusive witnesses and an empty set of direct AND-reader indices. The earlier [boundary note](plane-two-output-boundary-8059.md) gives a reduction to independent readouts.

## Zero direct readers and one intervening OR

Append one OR of the two readouts and trim the resulting one-output separator. Call an OR intervening if it is strictly between two ANDs on a directed path. The [earlier quadrangle lower bound](quadrangle-two-pairs.md) gives 64 gates whenever at most two pairs of distinct ANDs are comparable by reachability. Consequently a circuit of at most 62 original gates with no intervening OR is impossible. All AND dependencies would be direct, and the sole permitted direct reader has at most two operands.

Now suppose there are zero direct AND readers and exactly one intervening OR B. Every AND below B on such a path is a direct operand of B. An intermediate OR would be another intervening OR, and an intermediate AND would give a direct reader. Thus B has at most two strict AND ancestors. For the same reason, all ANDs descending from B read it directly and have no later AND descendants.

If B is false on every quadrangle, set its later reads to zero and add B as a disjunct of the final output. This preserves every positive and negative test. At least one AND reader of B becomes constant false and can be removed, paying for the new output OR. B now has no AND descendant. The same removal argument works with one direct reader when B is the only intervening OR. Only the direct comparable pairs can remain.

Otherwise B cannot reach the output through ORs alone. Each AND that reads B is an output term of the form B AND G, with G raw or computed entirely by ORs of raw inputs. If G were an AND gate, the term would be a direct reader. If G were a different OR with an AND ancestor, that OR would also be intervening. Reading B on both operands would accept a negative.

Suppose k output terms read B. Factor them into B AND the disjunction of their k guards. The new guard uses at most k−1 ORs and the factored term uses one AND, replacing k ANDs. If the final OR cone originally combined t distinct term wires, it had at least t−1 OR gates by the connected fan-in-two count. The new cone has at most t−k+1 term wires and can be rebuilt as a tree using at most t−k ORs. The old outer ORs have no AND descendants, since B is the only intervening OR and B never reaches that cone through ORs alone. Gates with no nonconstant input can be discarded from the cone. A raw input reaching the output through ORs alone would accept a negative quadrangle containing that input.

The factoring therefore cannot increase the total size. The remaining AND comparabilities are the at most two ancestors of B feeding the single factored term. This contradicts the earlier 64-gate bound for the joined separator. The [replay](plane-guard-factoring-8059.cjs) exercises this transformation on two valid readouts. One intervening OR yields four comparable AND pairs before factoring and two afterward, with one gate saved. Lean checks the Boolean guard factoring identity.

## The lone bridge with one AND ancestor and one direct reader

Let the sole intervening OR B have exactly one strict AND ancestor H. The unique direct-reader AND D cannot be an ancestor of another AND through B, since that would give B at least two strict AND ancestors. Any direct AND below D would be another direct reader. Thus D is a terminal.

After trimming, the other ANDs using B have the form B AND X, with X raw or a pure raw disjunction. If one also reaches the output through ORs alone, a D conjoining it with something else is redundant. Otherwise its only live consumer is D. An OR on a path from that lower AND to D would be a second intervening OR.

The following rewrites leave at most two comparable AND pairs and do not increase size.

- If D reads B and a primitive AND P, include P in the merged guard of the B terms. This gives the pair from H and at most one from P. If P is H or already has the form B AND X, D equals P by absorption.
- If D reads two B terms, replace their conjunction by B AND the conjunction of their raw guards. If D reads one B term and a raw guard, do the same. The new guard is one AND, so it and H are the only AND ancestors of the merged B term.
- If D reads a B term B AND X and also H, use H AND X. There is at most one pair at this term and one at the merged B term.
- If D has no input from B or from a B term, and has just one distinct AND operand, it contributes only one comparable pair. Factoring the B terms contributes at most one more.

A remaining counterexample with one intervening OR must therefore have an intervening OR accepting a negative, and either at least two strict AND ancestors of that OR or one of two placements of the direct reader. In the one-ancestor case, the direct reader must conjoin two distinct primitive ANDs or conjoin a B term with a primitive AND distinct from H. The latter B term has no separate OR-only route to the output.

## A cover restriction for three exceptional centers

For nonempty point and line sets with no incidences between them, the total size is at most ten. The only size-ten profiles are one point and nine lines or nine points and one line. For k chosen points the number of incident lines is at least 4k minus the number of pairs, since each pair of points shares exactly one line. Apply this to k from one through five on the smaller shore. Both shores cannot have at least five vertices, since five chosen points already leave at most three missed lines. The [finite replay](plane-mixed-covers-8059.cjs) checks all point sets and confirms the equality profiles.

Suppose the ordinary terms are consolidated into one live star per center. Suppose also that all flags missed by those stars have a cover by at most three exceptional vertices. The ordinary centers together with these exceptional vertices cover the plane. With at most eleven ordinary centers the union has size at most fourteen, so it contains a complete shore and at most one vertex opposite. Every vertex of the complete shore outside the three exceptional vertices must have an ordinary star covering at least three of its four flags. There are at least ten such vertices, and the [ten-center argument](quadrangle-two-pairs.md#ordinary-star-centers-on-a-single-shore) gives the required 64 gates for one output.

With twelve ordinary centers the union still contains a complete shore, and has at most two vertices opposite. The same argument works if at most two exceptional vertices lie on the complete shore, since the opposite vertices share just one neighbor. If all three exceptional vertices lie there, the only residual case has two vertices opposite whose intersection on the complete shore lies outside the exceptional set.

If thirteen ordinary centers and three exceptional centers give a cover that omits vertices on both shores, the equality profile forces twelve cover vertices on one shore and four on the other. The four are all incident with the one omitted vertex on the larger shore. Each other vertex on that shore has exactly one neighbor among the four. Here too, at least ten ordinary stars have three neighbors unless all three exceptional centers lie on the larger shore.

These results leave the unrestricted 62-gate exclusion open.
