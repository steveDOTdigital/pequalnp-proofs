# Counting the edges witnessed by sound AND gates

Let E be the edge set of a bipartite graph with no four-cycle. Write x for the point inputs and y for the line inputs. Its edge function F is true whenever the active inputs contain both endpoints of an edge. Consider any monotone fan-in-two circuit computing F. Call a gate **sound** when its output implies F on every assignment.

For an edge (p,w), say an AND gate witnesses it if the first operand is true on the point singleton (p,0) and the other on the line singleton (0,w), in either order. Let H consist of the edges witnessed by at least one *sound* AND gate. If the circuit has O OR gates and A sound AND gates, then

    |H| ≤ 2O + A.

This holds even when other gates give false positives. In particular, any circuit in which every edge has a sound witness requires at least |E|/2 gates. The unrestricted L-meta-606 conjecture also covers edges without such a witness and graphs without a fixed bipartition.

## A count for several outputs of a shared circuit

Let Sᵢ be sets of points, any two meeting in at most one point. In a shared point-only AND/OR circuit choose a group Wᵢ of output wires for each i. Require every wire in Wᵢ to be false when precisely the points *outside* Sᵢ are active. Let dᵢ count the distinct singleton inputs accepted by any wire of Wᵢ. Then

    Σ dᵢ ≤ number of OR gates + Σ |Wᵢ|.

Lean checks this statement in the project circuit model, allowing fan-in zero, one and two, repeated reads, unused gates and shared intermediate wires. [Lean theorem grouped_outputs](../lean/PEqualNP/Outside/IncidenceFactorCount.lean)

For a proof, work backwards from a frontier of wires false on the outside assignment. A wire accepting at most one singleton can be removed and that singleton recorded. At an AND, choose an operand false on the outside assignment. Every singleton accepted by the AND is accepted by that operand. At an OR, both operands are false on the outside assignment. Replacing the wire by both operands increases frontier size by at most one. Process each gate once, in reverse circuit order, merging repeated frontier requests. At the end each remaining input accounts for at most one singleton. Only an OR accepting two or more distinct singletons needs a charge. Monotonicity puts all its accepted singletons in Sᵢ because the OR was false outside Sᵢ. Two such singletons determine at most one Sᵢ, so each physical OR is charged at most once across all groups.

## Applying the count to an arbitrary bipartite circuit

For a sound AND with operands a and b, form the product of the two pure functions a(x,0) and b(0,y), and also consider the reverse orientation. By monotonicity each product implies the original gate, hence F. At most one orientation can cover any singleton pair if the other covers one: otherwise both operands accept some point singleton, so both would accept the union of those points with all lines off. Soundness rules that out.

For a productive orientation, its hits on singleton pairs form a nonempty rectangle contained in E. It must be a star, since two points and two lines in that rectangle would form a four-cycle. Assign each star to its center, choosing either endpoint in the one-edge case. For a line center w, its point factor is false when all points outside the neighborhood N(w) are on. Otherwise that input together with just line w would make the product true without an edge. Apply the grouped-output count to all these point factors at once. They are wires of one circuit obtained by fixing the original line inputs to zero. Propagate constants and bypass copies; this uses at most O OR gates. The same count on the other axis covers the point-centered stars using at most O additional OR charges. Each star supplies at most one output to one group. Their union covers H, and there are at most A stars. This proves the inequality.

## An exact minimum with separate preprocessing

For nonempty E let τ be the minimum vertex-cover size. Suppose point inputs and line inputs are preprocessed separately by arbitrary shared monotone binary circuits. They meet in product gates, each of whose outputs implies F on every input. A final fan-in-two circuit reads only those products and computes F. **The exact minimum size is |E| + τ − 1.** The final circuit can even use arbitrary Boolean operations of fan-in at most two.

Discard dead gates. Every product is zero on the all-zero input, so each graph edge has some productive rectangle: otherwise its singleton pair would give the final circuit exactly the all-zero product vector. Let r count the productive products. Their centers cover E, giving r ≥ τ. The grouped-output proof uses disjoint banks on the two sides, so each preprocessing OR is counted at most once in total. The banks therefore use at least |E| − r OR gates. The r productive gates need at least r − 1 downstream gates to reach one output, by connectedness and fan-in two. Adding the r products gives |E| + r − 1. To attain the bound, assign each edge to an endpoint in a minimum cover, compute the ordinary star at each used center, and OR the stars together.

## The remaining obstruction

Every edge has some witness. On its singleton pair the output is true and on each of the two singletons it is false. Take the earliest wire with these three values. An OR would have an earlier operand with the same three values. An AND must instead receive one operand from each singleton: both operands are true on the pair, neither was the earliest wire, and the AND rejects each singleton. What can fail is soundness of the witnessing AND. Even an exact monotone circuit for a matching can have no edge with a sound witness. For the matching (x₁,y₁), (x₂,y₂), take

    a = (x₁ OR y₂) AND (x₂ OR y₁)
    b = (x₁ OR x₂) AND (y₁ OR y₂)
    output = a AND b.

With both points and no lines, a is true without an edge. On the nonedge (x₁,y₂), b is true. The final AND is sound, but b is false on either pure axis, so the final AND witnesses neither edge. The distributive law, or a sixteen-row truth table, verifies the matching output. This example has seven gates; the ordinary two-product circuit has three. A bound for arbitrary circuits would need to account for such edges or show that a minimum circuit can avoid them.
