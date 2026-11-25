# Which shared gates could beat the 64-gate plane circuit?

For the order-three projective plane in L-meta-650, a 63-gate monotone circuit would need a shared intermediate result that carries more information than an edge already found or a disjunction of points. The statement also holds with points and lines exchanged. Even allowing disjunctions on both shores and across them, **two arbitrary shared ORs of raw input pairs cannot suffice** if all the other shared gates are safe or inactive on the minimal positive inputs. There is no bound here on the number of such other gates. The existence of an unrestricted 63-gate circuit remains open.

Here “shared” means an internal output read at least twice in the live output cone. Raw inputs may be read any number of times. An output is **safe** when its truth implies the graph edge function on every input. An output is **inactive** when it is false on each input supported on one edge. The familiar 64-gate construction uses thirteen ordinary stars. These results concern all gates of a circuit, including arbitrary unshared AND/OR subformulas.

## Cutting a circuit into formulas

Let \(G\) be a nonempty bipartite graph with no four-cycle and maximum degree at most four, with \(m\) edges and matching number \(\tau\) (also its minimum cover size). Write \(s\) for the number of binary gates in the live circuit and \(a\) for the number of gate operands that read raw inputs, with multiplicity. Put \(\sigma=\sum_h(\mathrm{fanout}(h)-1)\) over internal wires other than the output. Counting all \(2s\) input slots gives \(s=a+\sigma-1\). Repeated operands and dead gates can first be eliminated in a minimum circuit.

Cut at every shared internal wire, treating that wire as a formal input at its readers. The pieces are trees, one ending at each shared wire and one at the output. Every original raw operand slot belongs to exactly one piece. Use the minimal positive inputs (one edge each) as rows and independent sets as negative columns. Assign a row to the first safe shared output which is true there, or to the output if no such wire occurs first. In the chosen tree, every earlier safe terminal is false on that row. An inactive terminal is also false. At every negative column the root of the chosen tree is false.

Route each row and column down this tree. An OR tests the row to choose its first true operand. An AND tests the column to choose its first false operand. Each leaf occurrence receives a rectangle, and its input is true on the row and false on the column. Choosing the tree depends only on the row, so its choice simply restricts the row set of each rectangle. This works with arbitrary correlations among terminal values.

## Any number of disjunctions on one shore

Suppose every shared wire is safe, inactive, or computes exactly a disjunction of vertices on the point shore. Then
\[
                  s\ \ge\ m+\tau-1 .
\]
The intermediate gates building those disjunctions may use any inputs or operations. A shared wire equal to a single raw bit can be replaced by that bit. Empty disjunctions are inactive. Focus on the wires with point sets \(Q\) of at least two elements.

Fix a maximum matching \(M\). For each shared disjunction \(Q\) and each \(p\in Q\) we need a point \(q\in Q-\{p\}\) that can mask this helper in a comparison column. Process helpers in topological order. If a previous helper \(Q'\subseteq Q\) containing \(p\) was reached while tracing the private tree as described next, inherit its previously chosen partner. Otherwise charge one raw \(p\) occurrence in the current private tree and choose a partner in \(Q-\{p\}\).

To justify the charge, evaluate the helper at the singleton \(p\) and at the assignment of all vertices outside \(Q\). Its values are one and zero, respectively. Follow the formula comparison path. A terminal at which it can end is either raw \(p\) or a previous shared disjunction containing \(p\) and contained in \(Q\). Safe terminals are false at a singleton. Inactive terminals are false there too, since a relevant point has an incident edge. Distinct new choices cost distinct raw slots, even across trees. Ignore isolated vertices, which do not affect the function and can be fixed low.

When choosing a new partner for \(p\), prefer one outside the line matched to \(p\), if \(p\) is matched. Delete from \(G\) the flag between \(p\) and the line joining the two points if such a line exists. There is at most one, by the four-cycle condition. Keep every selected partner at \(p\), including choices made for other helpers. This deletes at most \(a_0\) edges, where \(a_0\) counts raw slots in the disjunction trees. A matched edge can be lost only if an entire helper \(Q\) is contained in the matched line. Each such helper lies on at most one line, and that line has at most one edge of \(M\). If there are \(t\) such helpers, the remaining graph \(H\) has at least \(m-a_0\) edges and a matching of size at least \(\tau-t\). Also \(t\le\sigma\).

For any point \(p\), the column consisting of \(N_H(p)\) together with its partner points is independent in the original graph. Every retained line through \(p\) avoids every partner by construction. On this column every retained incident row must report raw \(p\): each point disjunction true on that row contains \(p\), and its partner makes it true on the column as well. For a line \(w\) the full point shore forces every incident row to report raw \(w\).

Use the local charging argument from the [formula-size proof](cubic-formula-leaves.md). For clarity, each incident row has a pattern of the raw leaves at its vertex whose rectangles contain that row. The forcing column meets every such pattern in exactly one leaf. With \(r<d\le4\) raw occurrences, at least \(d-r+1\) rows contain the pattern of some different row. Such a row is called dominated at that endpoint. A retained flag \(pw\) cannot be dominated at both ends. For two witnesses \(pb,aw\), use the column \(\{a,b\}\) together with the partners of \(p\). The four-cycle condition rules out \(ab\). The retained flag \(pb\) rules out adjacency of \(b\) to any partner. Row \(pb\) must report raw \(p\), and row \(aw\) must report raw \(w\), since \(a\) itself blocks any point disjunction true on \(aw\). Pattern containment would force both reports on \(pw\).

The same saving-vertex count as in the linked proof gives at least \(|E(H)|+\tau(H)\) raw slots in the trees assigned positive rows. They are disjoint from the \(a_0\) slots. Consequently \(s\ge m+\tau-1+\sigma-t\). In particular the lower bound is strict if a shared safe wire has been retained or if a retained shared wire has more than two readers. The upper bound is attained by assigning edges to a minimum cover and forming ordinary stars. The projective plane has \(m=52,\tau=13\).

## Disjunctions of raw pairs on both shores

For a set of \(k\) distinct shared binary gates of the form \(u\lor v\) on raw inputs, each such gate supplies two raw slots and at least one excess reader. All other shared signals may be safe or inactive. Thus these \(k\) gates contribute at least \(3k\) to \(s+1\) before counting the raw leaves in the assigned trees. Duplicate helpers can be merged.

For each vertex \(x\), initially designate the other endpoint of every incident helper as a partner. Choose retained flags so that \(N_H(x)\) and the partners of \(x\) together form an independent set for every active \(x\). Such a column forces all retained rows at \(x\) to report \(x\). For a retained flag \(pw\) with witness rows \(pb,aw\), the comparison column consists of \(a,b\) and all partners of both endpoints. Count \(pw\) as exceptional if some such choice fails to be independent or includes \(p\) or \(w\). All other flags can be dominated at most once. Further flags may be omitted voluntarily.

Let \(C\) be the exceptional flags and \(U\) their endpoints. Then the raw-leaf bound becomes
\[
             |E(H)|+|U|-|C|+\tau(H-U).
\]
Indeed, if \(S\) denotes the saving vertices, add the number of edges avoiding \(S\) and subtract the exceptional edges with both endpoints in \(S\) in the usual charge. On each exceptional edge the two contributions together are \(1\) minus its number of selected endpoints. The expression to minimize is therefore \(|C|+\sum_{v\in U}(1-d_C(v))\,1_{v\in S}\), plus the cost of selected vertices outside \(U\) and uncovered ordinary edges. Putting all of \(U\) into \(S\) can only decrease this expression. Outside \(U\), paying one for a vertex or one per uncovered edge has minimum \(\tau(H-U)\).

One may instead charge every read of a chosen helper to one of its endpoints \(x\). Its occurrences become additional leaves labeled \(x\) on just the rows containing \(x\). Restricting the row set preserves rectangles, and a false helper on the column implies \(x\) is false there. The partner obligation at \(x\) disappears for that helper. The other endpoint retains its obligation. A helper with \(r\) reads contributes \(2+(r-1)\) raw slots and excess reads, paying for the \(r\) new leaves with one unit to spare. Thus an oriented helper contributes one in place of the usual three.

The [finite checker](plane-shared-or-check.py) uses the actual 52 desk flags. It verifies all incidence-preserving permutations it uses, computes residual matchings by augmentation, and exhausts the indicated helper families. Here are the smallest certified lower bounds. All bounds allow any number of safe or inactive shared signals in addition to the helpers.

| Raw-pair OR family | Geometries before symmetry | Minimum certified gate count |
| --- | ---: | ---: |
| One point pair and one line pair | 6,084 | 66 |
| Two point pairs and one line pair | 234,234 | 65 |
| Two point pairs and two line pairs | 9,018,009 | 64 |
| Three point pairs and one line pair | 5,933,928 | 64 |
| One point-line OR | 169 | 64 |
| Two point-line ORs | 14,196 | 64 |
| One point pair and one point-line OR | 13,182 | 64 |

Interchanging points and lines gives the dual results. With one nonincident point-line OR, the eight exceptional flags form the two disjoint endpoint stars. They have ten endpoints, and deleting those endpoints leaves a matching of size eight. The price is \(52+10-8+8+3-1=64\). With an incident pair only its own flag can be exceptional. For two cross-shore helpers the program also tries dropping flags between the pencil at a point and the points on its partner line. In the mixed family the orientation option covers the case where an endpoint has two adjacent partners. The table gives lower bounds, not claims of minimum circuit sizes within each family.

## Equality for formulas

In a connected regular bipartite graph of degree two through four, with no four-cycle, the only minimum covers are the two shores. A proper nonempty subset on either shore has more neighbors than vertices: equality in the degree count would isolate a component. Suppose a monotone formula attains \(m+\tau-1\). The leaf proof forces equality in \(\tau\le |S|+W\), where \(W\) counts edges avoiding \(S\). If \(W>0\), choosing different endpoints of one uncovered edge produces two minimum covers differing by a single swap. Equality guarantees that the choices do not duplicate previously selected vertices. This is incompatible with the two disjoint shores. Hence \(S\) is a whole shore. Every vertex in it occurs exactly once, and every opposite vertex occurs exactly its degree many times.

The lowest common ancestor of any two single-read center bits has to be OR. Set all opposite bits to one and all other centers to zero: the restriction is the OR of these two bits. Thus at each AND on the center skeleton only one child contains centers. An OR on the skeleton cannot have a pure opposite-shore child: with all opposite bits one and all centers zero it would turn on, propagate through every ancestor AND's pure sibling, and incorrectly turn on the output. The center skeleton is therefore an OR tree with pure factors conjoined along its branches.

For each center \(p\) every factor along its path must accept each singleton in \(N(p)\). Turn on \(p\) alone among centers and all opposite variables outside \(N(p)\). The output must be zero, so some factor on this path rejects the outside set. Monotonicity makes this factor exactly the OR of \(N(p)\). It cannot be on the path of another center, whose equally large and distinct neighborhood it would also have to accept. These private factors already require all \(m\) opposite-shore leaves. Each uses its own neighbors once, in a pure OR tree (any AND would block a singleton). The whole formula is an OR of the ordinary stars of one shore. In particular, fully unfolding a 63-gate solution on the plane, if one exists, would produce at least 65 binary gates: a 64-gate star formula has no repeated nontrivial subtree to share.

[Lean verification](PlaneSharedFormulas.lean) proves that routing on an arbitrary binary formula separates positive and negative inputs and that each leaf receives a rectangle, even for correlated terminals. It also checks the circuit-accounting and exceptional-edge inequalities. The graph and circuit decompositions above are written proofs. Run the finite geometry checks with Python 3 and no external packages.
