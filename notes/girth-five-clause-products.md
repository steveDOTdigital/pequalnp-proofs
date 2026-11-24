# Linear size bounds for circuits built from products of raw clauses

Let $G$ be any finite simple graph of girth at least five, with $m$ edges. Its Boolean edge function is true when at least one edge has both endpoints active. Suppose a binary monotone circuit of size $s$ computes this function as an OR of products, each of which is an AND of two or three disjunctions of raw vertex inputs. Disjunctions may share OR gates, and three-clause products may share their inner AND gates. Then

$$3m\le 4(s+1).$$

The graph may have unbounded degree and need not have a specified bipartition. The general desk conjecture also allows a later AND to read an OR of earlier products.

More generally, a bound linear in $m$ holds for **every fixed number of clauses per product**. The coefficient proved below depends polynomially on that bound. The three-clause case has the sharper coefficient above.

## Accepted pairs in one product

An accepted pair consists of the two active inputs of one graph edge. Each product rejects every independent set. A product of two clauses accepts a complete bipartite graph between disjoint clause supports, since it rejects singletons. A complete bipartite subgraph without a four-cycle is a star.

For a product of three clauses, each vertex carries three membership bits. A pair is accepted if its two masks cover all three bits. Two disjoint accepted edges force an accepted crossing between their endpoints: each clause hits both edges and can miss at most one of the four crossings. If there are no disjoint accepted edges, the graph is a star or empty. Indeed, two intersecting edges have a common center, and an edge meeting both but missing that center would complete a triangle.

If there are disjoint edges, choose an accepted crossing. This gives a path $a,u,v,b$. The three remaining pairs are forbidden by the triangle and four-cycle assumptions. Up to permutation of clauses, the masks of $u,v$ each miss one distinct bit. The clause missed by $u$ consists precisely of inputs whose pair with $u$ is accepted. The same statement holds for $v$. The remaining clause contains both centers. Every accepted pair touches $u$ or $v$: the finite mask check in [ThreeClauseShape.lean](ThreeClauseShape.lean) proves this for an arbitrary vertex type. In particular, the two clauses missed by the centers are pure neighbor clauses, each containing at least two neighbors.

For a three-clause product that accepts only a star at $c$, its center misses either one or two clauses as soon as it accepts an edge. If it misses one clause, that clause contains only neighbors, and it contains all the accepted neighbors. If it misses two, both contain all the accepted neighbors. In each missed clause consider its inputs outside the graph neighborhood of $c$. These two sets are disjoint. Every vertex in the first must be adjacent to every vertex in the second: otherwise those two inputs and $c$ would form an independent set satisfying all three clauses. If they shared a vertex, that single vertex together with $c$ would already suffice. A four-cycle forbids both outside sets from having size at least two. Choose a clause with at most one outside input.

## Counting OR gates without charging the same work twice

Remove repeated output terms, terms with no accepted edge, and any three-clause term whose inner AND is already an output term. Removing the first two kinds preserves coverage of all graph edges. Absorption handles the third. Let $r$ count remaining ordinary products, $e$ count three-clause stars, and $k$ count genuine double stars. For each ordinary star choose its neighbor clause as a terminal. For a three-clause star choose the clause from the preceding paragraph. A star with just one edge may use its bare neighbor input for this count. For a double star choose the two pure neighbor clauses, one per center. There are at most $K=r+e+2k$ terminals, counted with their assigned centers.

At each center $c$, let $U_c$ be the union of the neighbors on its assigned accepted edges. Write $M=\sum_c |U_c|$. Every edge is covered, so $M\ge m$. Project the OR cones of the terminals at $c$ to inputs in $U_c$. Discard empty wires and bypass an OR whenever its projected support already equals the support of one operand. Choose one path forward from every remaining source to a terminal by keeping one outgoing edge per nonterminal and using terminals as roots. Prune branches without a source. The resulting forest has $|U_c|$ source leaves, at most the number of assigned terminals as roots, and internal vertices of fan-in one or two. Across all centers there are at least $M-K$ binary branchings, each charged to an original preprocessing OR.

A gate charged at two centers has exactly three raw inputs in its support. To see this, the two centers have at most one common neighbor. Each charged cone lies in a terminal support with at most one input outside its center's neighborhood. The intersection of two such supports has size at most three. A branching gate needs at least two neighbors at each center, so their union has size at least three. Its two required neighbors at either center must be split exclusively between the two operands of the original OR, since otherwise the projection would have bypassed that gate. On three inputs, at most two unordered pairs cross such a split. Each pair determines at most one center, so a gate is charged at most twice.

At each center, a doubly charged branching has exactly two descendant source leaves. In a forest, the leaf pairs of two such branching vertices are disjoint. Thus there are at most $|U_c|/2$ occurrences of double charges at $c$. Summing over centers counts each doubly charged gate twice. At most $M/4$ branchings were counted in excess. The number of distinct preprocessing ORs is therefore at least $3M/4-K$.

There are at least $r+e+k$ product output ANDs and $r+e+k-1$ OR gates combining these outputs. Their total plus one is at least $K$. This count already allows all inner ANDs to be shared. Together with preprocessing, $s+1\ge3M/4\ge3m/4$. The empty graph satisfies the inequality directly.

## Any fixed clause bound

Assume each output term is a product of at most $k$ raw-input disjunctions, with $k\ge2$. The AND gates forming these products and the OR gates forming the raw clauses may each be shared arbitrarily. Let $t=k^4$, and put $Q=\binom{2t-1}{2}$. Then $m\le Qs$. This proof only requires the absence of four-cycles. Triangles are allowed.

**Independent representatives.** Given at most $k$ nonempty sets of vertices in a four-cycle-free graph, each of size at least $t$, it is possible to choose one vertex from each so that the chosen vertices form an independent set. First trim each set to exactly $t$. For two sets $A,B$, form the bipartite adjacency relation between their copies. Distinct vertices of $A$ cannot have two common neighbors in $B$. This also holds when the sets overlap, since a loop is never an edge. If $e$ counts ordered adjacent pairs and $d_b$ is the number of neighbors in $A$ of $b\in B$, then

$$\sum_{b\in B}d_b(d_b-1)\le t(t-1),\qquad e^2\le t\sum_{b\in B}d_b^2\le t^2(t-1)+te.$$

Consequently $e<t(\sqrt t+1)$. Choose the representatives independently and uniformly. For each pair of sets the probability of choosing adjacent vertices is less than $(k^2+1)/t$. The sum over all pairs is less than one, since $\binom{k}{2}(k^2+1)<k^4$. A choice avoiding every adjacency exists. Coincident representatives are harmless.

**Few centers and few extraneous inputs.** Each output term has a clause of size less than $t$. Otherwise independent representatives, one from each clause, would make that term true on an independent set. Every accepted pair meets the small clause, so its members are at most $t-1$ centers whose stars cover that term's accepted edges.

For such a center $c$ on an accepted edge, at least one clause misses $c$. Consider all clauses missing $c$, removing the neighbors of $c$ from each. If all remaining sets had at least $t$ elements, independent representatives of the remaining sets together with $c$ would again satisfy the term on an independent set. Thus some clause missing $c$ has at most $t-1$ inputs outside the neighborhood of $c$. Every accepted neighbor of $c$ belongs to that clause. Use it as the terminal at $c$ and proceed with the same projection and forest count as above.

**Multiplicity.** Suppose an original preprocessing OR with raw support $B$ is charged at two distinct centers. The full neighborhoods of the centers intersect in at most one vertex, and each terminal has at most $t-1$ extraneous inputs. Hence $|B|\le 2t-1$. Each center that charges the gate requires at least two distinct neighbors from $B$. No two centers can use the same unordered pair of neighbors. Thus the gate is charged at most $Q$ times. A gate charged at only one center satisfies the same bound.

If $a$ is the number of preprocessing ORs, $r$ the number of distinct nonempty output terms, and $K$ the total number of chosen terminals, the forest count gives $m\le M\le Qa+K$. There are at most $(t-1)r$ terminals. Each term accepting an edge uses its own output AND: a raw disjunction alone cannot accept an edge while rejecting all singletons. These output ANDs are distinct from preprocessing ORs even when AND subexpressions are shared. Since $Q\ge t-1$ and $a+r\le s$, we get $m\le Qs$.

The gate counts and independent-representative argument are written proofs. The accompanying Lean file checks the crossing and center classification, the numerical accounting for three clauses, and the moment and density inequalities used for an arbitrary fixed clause bound. This extends the [order-three plane argument](quadrangle-three-clause.md) to arbitrary finite graphs of girth at least five and exact edge-function outputs.
