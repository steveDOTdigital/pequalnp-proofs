# Seven erasures in cubic edge-function circuits

For desk case L-meta-2640, the graph function is the OR of its edge monomials
and a set of isolated input variables. Fixing two adjacent vertices to false removes
all edge monomials incident to either endpoint. The desk asks for seven legal,
single-gate erasures in some circuit of minimum fan-in-two size. A legal erasure
either redirects a gate to a wire of equal value on the restricted inputs or drops
a gate with no remaining readers that is not the output.

## A static certificate for arbitrary circuits

Fix a circuit, any family of input rows of length n, a set S of gate indices,
and a redirect p(m) for each member m of S. Require p(m) to be earlier than the
wire n+m and outside the set of marked wires. Each m must satisfy one of two tests
in the original circuit.

1. The values of n+m and p(m) agree on every row.
2. The output is different from n+m and every gate reading n+m is marked.

Then there is a trace of exactly |S| legal erasures. Erase in decreasing order.
The gates preceding the largest mark, and the values on their existing wires,
are unchanged. If a mark passes the second test, erasing its last marked reader
introduces no new reader of it, since redirects always land outside the marked
wires. The same holds for the output. The largest mark satisfying the second test
therefore has no later readers and can be dropped. Induction on |S| proves the claim.
The proof allows arbitrary gate operations and arbitrary original wire indices,
including forward reads with the circuit model's default-false semantics.

[CubicBatch.lean](CubicBatch.lean) proves the certificate theorem in Lean using
the project's actual `eraseGate`. The reduction's remaining child asks for such
a certificate with at least seven marks in a minimum circuit. The next result
supplies it for a family that can be recognized by its circuit size.

## Star circuits on arbitrary simple graphs

Assign each edge to one of its two endpoints. An active center c with k owned
edges computes the OR of its k owned neighbors using k−1 private gates, then
ANDs that result with its own input. A final OR tree joins all active center
outputs and all isolated OR inputs. If m is the number of edges, s the number
of active centers, and a the number of isolated OR inputs, this costs
m+s+a−1 gates. Changing the order of the OR trees preserves this size.

**Claim.** If u and v are adjacent active centers and there are at least three
summands, this construction admits d(u)+d(v)+1 marked gates on the cofactor
u=v=false, where d denotes graph degree.

- In the two endpoint stars, mark every gate. The two center ANDs are false.
  Every private OR is read only by another mark in the same star. All these
  marks can redirect to raw input u, which is false on the cofactor.
- At any other center, order its unpinned leaves before its pinned leaves.
  If it has live leaves, each pinned leaf adds one OR to their accumulator.
  Mark those ORs and redirect each to the last accumulator of live leaves.
  With just one live leaf, that accumulator is its raw input.
  If every leaf is pinned, mark all gates in the star and redirect them to raw u.
  This marks exactly one gate per owned edge going to the two endpoints, including
  when one center owns edges to both.
- First join the other summands. Append the u and v terms last, using two ORs.
  Both can redirect to the accumulator of the other summands. If that accumulator
  is a marked wire, it must be a lone fully pinned center term and is equal to
  raw u instead. The case of a lone isolated variable uses that raw input.

The star marks count every edge incident to u or v exactly once. The edge uv
appears in both degree counts, giving d(u)+d(v)−1 distinct marks there. The two
final ORs complete the certificate. All anchors are earlier and unmarked. This
construction also handles triangles.

**Consequence for L-meta-2640.** Active centers meet every edge. In a nonbipartite
graph some two of them must be adjacent, since otherwise the centers and their
complement give a bipartition. In a simple cubic graph there must be a third active
center if two adjacent vertices are centers: one has a neighbor outside the pair,
and that neighbor needs three distinct neighbors, which cannot all belong to
a cover of size two. The claim now gives 3+3+1 = 7. The argument does not require
the girth hypothesis.

In particular, let τ denote the minimum vertex cover size. A minimum cover has
a private incident edge at each vertex (otherwise it could be reduced). Assign
these edges to their cover vertices and orient the remaining edges arbitrarily
toward the cover. If the unrestricted circuit minimum is m+τ+a−1, the constructed
circuit realizes that minimum and witnesses the desk conclusion for every choice
of the starting minimum circuit. The open part includes circuits that save gates
through sharing or negation and achieve a size strictly below this star bound.

## Reproducible finite checks

Run `python3 notes/check-cubic-batch.py` from the research checkout. The script
constructs a 24-cycle with matching offsets (12,7,−7) repeated eight times,
verifies degree three, and computes girth seven by shortest paths after deleting
each edge. It finds all eight minimum covers of size 14. For each cover it checks
all 64 orientations of the six cover-internal edges and all six choices of an
adjacent pair of centers, giving 3,072 certificates. It also checks six traces with
two extra isolated OR variables and 96 traces on the complete four-vertex graph.

For every trace, the program computes exact monotone Boolean functions as antichains
of minimal true sets, tests the original function, checks all seven static marks,
and independently replays the desk's redirects. It verifies each move's legality and
the final restricted function. These are exact checks on the constructed circuits.
Whether smaller unrestricted circuits exist for the 24-vertex example remains open here.
