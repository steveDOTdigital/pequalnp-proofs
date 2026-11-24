# Equality for safe AND gates in the order-three plane

Independent proof for PEqualNP desk case L-meta-2069, by steveDOTdigital.
A safe AND is an AND whose value 1 implies a positive value of the target function on every assignment. The hypothesis applies to every AND in this case. Here is an argument for the stronger conclusion that no AND lies in the input cone of another AND. This is a written proof. The accompanying Lean file checks the counting identity and the plane vertex-cover lemma.

## The bound

Let a connected simple bipartite graph have two shores of size `n`, degree `d ≥ 2` at every vertex, and at most one common neighbor for two distinct vertices. Put `m = nd`. The target function on vertex bits asks whether the selected vertices contain an edge. Gates are AND or OR of two earlier wires. Consider a correct circuit in which every AND is safe. Restrict first to gates that can reach its output. An input or an invalid output wire cannot compute this function. Deleting a dead gate and renumbering the live wires preserves the function, safety and the gate model.

For each wire let its support be the raw variables whose singleton assignments turn it on. Inputs have singleton support, ANDs have empty support by safety, and ORs take unions. Equivalently, forcing all AND outputs to zero leaves each wire equal to the disjunction of its support. Call an empty-support wire *zero* below, even though it may turn on at an edge. Write `A_i, O_i` for the numbers of AND and OR gates with exactly `i` nonempty-support operands.

Each gate counted by `A₂` defines a set of edges. Its operand supports are disjoint by singleton safety. Every cross pair is an edge because it turns both operands on, by monotonicity, and the gate is safe. Both supports must lie in opposite shores. They cannot both have size at least two, since that would give a four-cycle. Choose a singleton operand as center and call the other support its leaves. Moreover these stars cover all edges. On an edge assignment the output must be true, whereas its support is empty. The first true AND on this assignment reads operand values equal to those in the all-AND-zero circuit. Its star contains that edge. Writing `r = A₂`, we obtain `r ≥ m/d = n`.

For a chosen center `c`, let `t_c` be the number of its stars and `d_c` their number of distinct leaves. Trace their leaf operands backwards. Stop and identify a source vertex by its label whenever a support is a singleton. At a support with at least two elements the wire must be an OR. Bypass it if just one operand has nonempty support, and otherwise retain the OR and trace both operands. The reduced directed graph for this center has `d_c` sources, at most `t_c` connected components, and at most two incoming arcs per retained gate, even if contraction identifies two operands. The edge count in a connected graph therefore gives at least `d_c − t_c` retained gates. Each retained gate is counted in `O₂`; it has at least two distinct leaves in its own support. Such a gate cannot be retained for two centers, which would then share at least two neighbors. Thus

    O₂ ≥ Σ_c (d_c − t_c) ≥ m − r.

The number of zero gate outputs is `Z = A₀ + A₁ + A₂ + O₀`. The total number of gate reads of zero wires, with multiplicity, is `U = 2A₀ + A₁ + 2O₀ + O₁`. Every live zero wire has a reader, counting selection as output as one extra read. The output has empty support, so `U+1 ≥ Z`. In particular `A₀ + O₀ + O₁ ≥ r−1`. For the total gate count this gives

    N = O₂ + r + A₁ + (A₀ + O₀ + O₁) ≥ m + r − 1 + A₁ ≥ m + n − 1.

## Rigidity at equality

If even the original circuit has at most this many gates, every gate is live and all the bounds are equalities. In particular `r=n`, `A₁=0`, and each zero wire has exactly one reader, including selection as output. The `n` stars partition the edges into full stars of degree `d`. Their centers are distinct. Every edge has exactly one center as endpoint, so connectedness forces the centers to form one entire shore. Call its vertices centers and the opposite vertices leaves. Write `g_p` for the unique star AND at center `p`.

Equality in the OR count means that **every** `O₂` gate was retained in a leaf trace. Its support therefore consists of at least two leaves. It follows inductively that each nonempty wire support is either leaf-only or a single center. A mixed OR (`O₁`) copies the support of its nonzero operand. Along a path through nonempty wires, a leaf-only support can lead only to other leaf-only supports, and a singleton center support only to the same center. In the latter assertion the only possible OR is a mixed OR.

Consider now the graph on zero wires, with an arc for each direct read by another zero gate. Every vertex has at most one outgoing arc by the reader equality. Chronological order makes it acyclic. Its components are trees directed towards a unique exit. The source vertices are the star ANDs; every other vertex is an `O₀` or `A₀` and has two zero operands. The exit is either the output itself or the unique zero input of a mixed OR.

Suppose a component does not contain the output. Pick a star `g_p` in it. On each of its edges `(p,l)`, the first actual positive AND must be `g_p`, since no other star covers this pair in the all-AND-zero circuit. We choose an edge that prevents any second star from turning on. If there were a second positive star, up to its evaluation any positive zero wire would have to be in this same component: following true zero operands backwards ends at a positive star, and only `g_p` has fired. Consequently the only way a nonempty wire can become newly positive, compared with the all-AND-zero circuit, is through the unique mixed OR at the component exit and then through nonempty wires.

* If that OR has leaf-only support, its effect stays on the leaf shore. Every star except `g_p` still has a false center operand, for any neighbor `l` of `p`.
* If it has support `{c}`, its effect stays on wires with that same support. Every leaf operand keeps its baseline value. For `c=p` there is no other candidate star. For `c≠p`, choose a neighbor `l` of `p` that is not a neighbor of `c`; degree at least two and the common-neighbor bound guarantee one. The leaf operand of `g_c` is false. Every remaining candidate apart from `g_p` has a false center operand.

In both cases a second positive star is impossible. The output component therefore has no positive star, and its zero output cannot be true, contradicting correctness on the chosen edge. Hence every zero wire belongs to the output tree. There is no mixed OR, because its zero operand would have a different exit.

The nonempty operand network now has no input from a zero wire. On each edge exactly its own star fires. If the output tree contained a binary AND (`A₀`), choose a star below one of its operands and an edge owned by that star. Its sibling subtree is false there because the two subtrees have disjoint star leaves. The AND blocks the sole true star on its unique path to the output; every other subtree is false. This contradiction eliminates `A₀`. All the ANDs are therefore the full stars, with no AND in their operand cones. This proves the claimed rigidity even when the original circuit description permits unused gates or a nonfinal output index.

## The assigned plane and the boundary

The two shores are copies of the integers modulo 13; `p` is incident with `l` if `p−l` is 0, 1, 3 or 9. The twelve nonzero ordered differences of these four residues are distinct, giving the common-neighbor bound on both shores. Residues 0 and 1 alone connect the graph. There are 52 edges and the threshold is 64. The case demands a strictly nested pair of ANDs, which the argument rules out before either directional derivative is used.

A circuit of 64 gates groups the four neighbors of each point with three binary ORs, ANDs the result with the point, and joins the thirteen stars by twelve ORs. To get 65 gates, replace line 0 in the leaf disjunction for point 0 by the wire `point0 AND line0`. To get 66 gates, AND that new wire again with line 0 before using it. Both substitutions preserve all truth values of the output by absorption, and every AND is still safe. The 65-gate example has a nested AND; the 66-gate example can miss both formal derivatives at the chosen incidence. These constructions give no lower bound of 66 for a double miss. The lower bound and equality classification here use the all-AND safety hypothesis throughout.

The [control script](check-plane-safe-stars.py) checks both choices of center shore, all 52 minimal positive rows, and all 704 maximal negative rows. Monotonicity makes these rows sufficient for the full truth table and for safety of each AND. It evaluates both directional recurrences at all 52 edges: at 64 both directions pass everywhere, at 65 one fails only at (0,0), and at 66 both fail only at (0,0). The [Lean lemmas](PlaneSafeCounting.lean) are independent of these computations.
