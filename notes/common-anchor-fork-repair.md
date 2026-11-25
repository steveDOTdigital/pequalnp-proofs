# Repairing several private forks with one anchor

Consider a binary monotone AND/OR circuit computing the edge function of a bipartite graph without four-cycles. A cut replaces every external read of each selected gate by the same raw input $s$. Assume every selected gate accepts exactly the singleton $s$ among the singleton inputs. Let $U$ be the union of their gate cones, including the selected gates themselves. Suppose the output is outside $U$, and after rewiring no gate outside $U$ reads a wire produced in $U$. Let $D$ be the set of vertices incident to edges lost by the cut. If every lost edge has one endpoint adjacent to $s$, the cut and repair give

```
|D| ≤ |U|
size(repaired circuit) + |U| ≤ size(original circuit) + |D|.
```

The selected cones may overlap. Neither inequality depends on the number of selected gates. The residual circuit can have an arbitrary pattern of sharing.

## Why the lost endpoints fit in the removed gates

Each selected gate dominates its replacement on every Boolean input, by singleton acceptance and monotonicity. The rewired circuit consequently computes a subfunction of the original. On any assignment containing $s$, every selected wire and every replacement has value one, so induction through the gates gives equality. In particular a lost pair has two endpoints $u,v$ distinct from $s$.

At least one selected gate was true on the lost pair in the original circuit. Otherwise all replaced occurrences retain their original value and induction again gives equal output. That selected gate is false on each of the singleton inputs $u,v$. Switching off either coordinate in the pair therefore changes that gate. Its cone must read both coordinates. Every selected cone must also read $s$, since its selected gate is false on the empty input and true on the singleton $s$.

For a nonempty selection, consider the undirected graph of gate and raw-wire vertices in the union of these cones. Each cone is connected and includes the raw vertex $s$, so the union is connected. It contains at least $|U|+|D|+1$ vertices, but at most $2|U|$ edges because each gate has two input ports. Connectivity gives $|D|≤|U|$. For the empty selection both sets are empty.

## Why the replacement costs one gate per lost endpoint

Orient every lost edge from its endpoint $t$ adjacent to $s$ to its other endpoint $u$. Bipartiteness makes this orientation unique. All $u$ have the color of $s$. If the same $u$ occurred with two different centers, then $u$ and $s$ would have two common neighbors, a four-cycle. Thus the lost edges form vertex-disjoint nonempty stars.

Delete the gates of $U$ from the rewired circuit, keeping every other gate in order. Relabel a retained gate wire by its new position and keep the raw indices fixed. The closed-read condition makes every surviving operand and the output well defined. Induction on retained gates shows that the relabeled wires have the same values as in the rewired circuit. This saves exactly $|U|$ gates.

For each active center with $d$ leaves, compute the OR of its leaves with $d-1$ gates, AND the result with the center, and OR this term into the running residual output. The $d+1$ new gates equal the number of vertices in this star. Every new term represents an original edge and the residual is a subfunction of the original. Conversely an input containing any original edge either already passes the residual on that pair, or activates the corresponding star. These facts give equality on all inputs.

## How the single-fork desk hypotheses imply the loss condition

For a lost pair the output is true before rewiring and false afterwards. The top OR tree has an originally true AND leaf, and every leaf is false afterwards. Trace a changed operand of this leaf backwards. Until reaching a redirected occurrence, each changed gate lies downstream of the selected gate and belongs to the output cone. Choose the earliest changed AND on such paths that feeds the changed output through a chain of changed gates. The descendant restriction makes it a top-tree leaf, since the internal top gates and allowed intermediate gates are OR. At least one operand changed. Following its changed predecessors reaches the selected gate via OR gates only. Direct readers of the selected gate are OR, so that operand satisfies the desk's OR-reach condition. This leaf was true on the pair. By the guard its opposite operand accepts one endpoint $t$ as a singleton. The OR-reaching operand accepts $s$ as a singleton. Hence the original leaf, and therefore the output, accepts the pair $\{s,t\}$. Since $t≠s$, this is an edge, as required. Private ancestry supplies the closed-read condition. The output cannot be the selected gate (it would accept a singleton), or a strict ancestor of the selected gate (the selected gate already reaches the output).

## Verification and attribution

The accompanying [Lean development](ForkStarRepair.lean) checks star disjointness and exact endpoint counting, and constructs a legal repair suffix for the project's actual numbered-wire circuit model. The theorem `appendLostEdges` groups the oriented lost edges, emits the repair gates, and proves the gate count and the output on every Boolean input. The arguments about the union of cones, deletion, and the desk guard are given above.

This was independent work on **L-meta-3018**, the negation of **L-meta-3017**. The project grader had already accepted another contributor's proof of L-meta-3017. The public fork records this extension separately. [Upstream verdict](https://github.com/open-goat/pequalnp-proofs/pull/5832)
