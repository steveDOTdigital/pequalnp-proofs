# Removing pendant trees from graph-circuit lower bounds

For L-meta-612 the star construction is optimal for **every four-cycle-free graph of vertex-cover number at most three**, including graphs containing triangles, with no bound on the number of vertices. It is also optimal on every graph whose sole cycle is a triangle, with arbitrary attached and disjoint trees. For this second family the lower bound even allows inversions of every wire for free. In each nonempty graph the size is exactly $|E|+\tau-1$. The general desk statement for all four-cycle-free graphs remains open.

The [Lean proof](CyclicCorePeeling.lean) gives the general reduction to terminal graphs in the project's binary AND/OR/NOT circuit model. It uses the elimination, cover and edge-count lemmas from the project's [forest proof](../lean/PEqualNP/MetaComplexity/Helpers/ForestBound.lean). The new terminal classifications and three finite monotone exclusions below are computer-assisted mathematical arguments. The [reproducer](cyclic-core-peeling.py) includes both the stronger signed tests and the monotone tests.

## Removing leaves

Write $F(G,A)$ for the OR of the edge function and the individual inputs in $A$, all isolated in $G$. For nonempty $G$, each element of $A$ costs a gate. Set it to zero. It is essential and the residual still depends on an edge. One of its readers simplifies, so peeling all these inputs leaves a circuit for $G$ at least $|A|$ gates smaller. Adding their OR back realizes the opposite bound. Lean proves the size-preserving statement with the original input arity in `removeAlarms`.

Choose a leaf $l$ with parent $p$. If there is another leaf at $p$, setting $l$ to zero costs one gate and one edge. The minimum cover size is preserved since a cover of the reduced graph can be chosen to contain $p$ by swapping the other leaf for it. Otherwise suppose $p$ has degree at most two. Setting $l$ to zero deletes one edge. Setting it to one deletes all edges at $p$ and makes $p$ an isolated OR input. Either pin decreases $|E|+\tau+|A|$ by at most two, since adding $p$ repairs a cover. Some pin eliminates two gates whenever both cofactors are nonconstant. The sole-edge exception follows from its two essential inputs. This is exactly where the forest argument can stop at an arbitrary residual graph. For any family closed under edge deletion it suffices to verify the lower bound on its nonempty graphs admitting neither kind of leaf. The theorem `reduceToCore` implements that implication, including the constants and empty-graph endpoints.

The monotone version uses the same descent. In a cleaned monotone circuit choose a first reader of an essential input. A pin simplifies it. Its controlling pin also makes its value constant, simplifying a consumer. If it is itself the output its controlling cofactor is constant. These operations preserve monotonicity. With complemented wires for free the same proof absorbs any sign on a bypassed wire. These two versions explain which terminal checks can be used in which circuit model.

There is a direct-sum consequence. If $f$ is any nonconstant function on disjoint variables and $T$ is a forest, then
$$
  C(f\lor E_T)=C(f)+|E(T)|+\tau(T).
$$
Here $C$ may count ordinary AND/OR/NOT gates or monotone gates when $f$ is monotone. In the latter case sharing between the two groups of inputs is unrestricted. To prove the lower bound, run the preceding leaf induction in the presence of $f$. Setting its own inputs to a zero of $f$ witnesses the required dependence of the leaf. Setting every remaining forest input to zero, including the parent after a high leaf pin, leaves both values of $f$ possible. Thus neither cofactor is constant, even on the last forest edge. The induction bound is $C(f)+|E|+\tau+|A|$. At the base remove each isolated OR input as above. Conversely, use a circuit for $f$, a forest star cover, and one final OR if the forest is nonempty. This extension to arbitrary $f$ is a written proof.

## A graph with one triangular cycle

In a component with no cycle, the forest good-leaf lemma always supplies a reduction when there is an edge. In a tree attached to a cycle choose a nonleaf outside the cycle farthest from it. All its children are leaves. Two children are siblings, and with only one child its degree is two. Consequently a terminal graph with sole cycle a triangle consists, up to isolated vertices, of the triangle with one leaf on each of a subset of its vertices. There are four cases up to symmetry. Deleting edges never introduces another cycle or changes a surviving triangle into a different cycle.

| Leaves on the triangle | Edges | Minimum cover | Exact binary gates |
| ---: | ---: | ---: | ---: |
| 0 | 3 | 2 | 4 |
| 1 | 4 | 2 | 5 |
| 2 | 5 | 2 | 6 |
| 3 | 6 | 3 | 8 |

The signed checks allow complemented inputs, complemented intermediate results and complemented output at zero cost. A solver run checks the necessary smaller sizes that survive the first-gate bound. The ordinary monotone stars attain every entry. Run `python3 notes/cyclic-core-peeling.py --triangle`.

## Cover number at most three

Fix a minimum cover of size $k$. The outside vertices have no mutual edges. In a terminal graph two of them cannot have the same singleton neighborhood, and two neighborhoods cannot share two vertices because this would form a four-cycle. Each nonsingleton neighborhood therefore uses a distinct pair of cover vertices. There are at most $2k+\binom{k}{2}$ active vertices, even in the presence of triangles.

Enumerate the graph inside the cover first. No pair can have two common inner neighbors. A proposed outside neighborhood cannot contain two cover vertices that already have a common inner neighbor. Two outside neighborhoods may intersect at most once. These conditions exhaust four-cycles according to how many outside vertices they use. Adjacent cover vertices are allowed in a neighborhood, which is essential for triangles. Enumerate the distinct outside neighborhoods, remove isolated or peelable graphs, test the claimed minimum cover, and canonicalize vertex labels. The number of terminal graphs for $k=1,2,3$ is respectively **0, 3 and 22**. For example, the three cover-two terminals consist of a triangle with zero, one or two extra leaves.

For a raw vertex $v$, the zero cofactor is $G-v$. The high cofactor consists of one disjunct for every neighbor and the edge graph outside the closed neighborhood. This supplies two recursive costs. In an essential-input circuit with $d$ readers of $v$, of which $a$ are AND, pinning zero saves at least $d+\min(a,2)$ gates and pinning one saves at least $d+\min(d-a,2)$ when the respective cofactor is nonconstant. Two AND readers cannot both have only one common consumer in a smallest circuit: factor $v$ out of that consumer and save a gate. The OR case is dual. One reader feeding another reader of the same operation simplifies by idempotence. The [earlier graph computation](edge-owner-exchange.md) gives the connected-circuit count for the essential raw inputs that vanish under a pin.

We also enumerate candidates for the first gate. If its raw input $v$ is read nowhere else, the other input's controlling pin must make $v$ inessential. With signed operands we use the [first-gate elimination](petersen-gate-elimination.py) on all four choices of controlling values. The numeric bounds leave just three exact monotone sizes for SAT to exclude. In canonical neighbor-mask order these are:

| Neighbor masks | Excluded gates |
| --- | ---: |
| 24, 20, 18, 17, 15 | 7 |
| 32, 16, 8, 52, 42, 25 | 7 |
| 48, 40, 24, 6, 37, 19 | 8 |

The [binary monotone encoder](check-petersen-monotone.py) tests positive edges and maximal independent negatives. All raw inputs are essential, both pins in these three graphs leave a nonconstant function, and all gates of a minimum circuit can be made live, binary and free of duplicate operands. The added clauses only enforce the proved cofactor budgets. CaDiCaL runs with proof checking enabled. Run `python3 notes/cyclic-core-peeling.py --mono --cover 3 --seconds 30` from the proof repository. For $k=4$ there are 489 terminal graphs. Before additional solver calls this calculation settles 20, and its remaining lower bounds fall short by one, two or three gates on 331, 126 and 12 graphs respectively. The option `--four-summary` reproduces those counts.
