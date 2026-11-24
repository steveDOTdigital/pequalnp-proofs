# A computer-assisted proof for every flipped input in L-meta-3248

The gate-list circuit in L-meta-3248 cannot compute the specified Petersen edge function with at most thirteen gates. The argument covers all seven allowed choices of the flipped input. The finite exclusions use CaDiCaL with internal proof checking. Formalizing the exclusions in Lean is a separate step.

## Removing the flipped input and vertex 6

Write G for the displayed nine-vertex graph and H for its induced subgraph after deleting vertex 6. A signed binary circuit may use either sign of every wire, including its output, for free. Each paid gate is an AND of two signed earlier wires. This model includes OR by De Morgan's law, permits arbitrary sharing, and can fold constants and copies without a binary gate.

Suppose the desk circuit computes G. For each permitted vertex i, fix one neighbor high and all other vertices except i low. Selecting i changes the target from false to true while its supplied pin falls from true to false. The free OR depends only on 0 and 6 and stays fixed. Every AND/OR circuit is monotone on its supplied pins, so at least one paid gate is a NOT. There are at most twelve binary gates left. Absorb the supplied flip and every NOT into wire signs; fold zero- and one-argument gates, invalid reads and constants. This yields a signed circuit for G from its nine raw inputs and u = x₀ OR x₆, using at most twelve binary gates.

Vertex 6 must have a direct binary reader in the resulting output cone. For instance, compare the raw selections {0,8} and {0,6,8}. Their u values are both true and only the latter contains an edge. A source-literal or constant output cannot compute G. Now set x₆ to zero. Its reader becomes a constant or a copy, and the free OR becomes x₀. The result is a signed circuit for H on eight raw vertices with at most eleven binary gates. The remaining proof excludes this circuit.

## Counting direct readers

Work with a smallest signed circuit, prune to the output cone and replace constants, copies and repeated operands. Choose among the resulting circuits one minimizing the sum of operand indices in a topological listing. A gate combining a previous gate g(a,b) with one of a,b can be normalized away from that dependency. Fix the shared operand to the value forcing g to be constant. The composition is then constant. On the opposite value it is a unary function of the other operand. Consequently the composition is a constant, a signed literal, or one signed binary gate of a,b. Replacing it reduces the gate count or strictly reduces the operand-index sum. This rules out such direct dependencies. This normalization survives reordering the gates.

If v has d direct readers, fixing v simplifies all d. If k of those readers are forced constant and the restricted target is nonconstant, at least min(k,2) further gates simplify. Every forced reader has a consumer, and the normalization excludes a consumer that itself reads v. If two forced readers have only a single consumer between them, that consumer combines exactly those two. When v forces the readers, their joint output is constant. On the other value of v, their joint output is a signed binary operation of the other two operands. These three gates can therefore be replaced by at most two, contradicting minimality. Thus the number of gates that can remain supplies a bound on d + min(k,2). When only one reader of v is possible, its other signed operand must be true on every pair of rows where toggling v changes the target.

In the theta graph and H, for each pair of distinct raw vertices p,q the variable p remains essential with q fixed to either value. At q = 0 use a neighbor distinct from q. At q = 1 use q itself if they are adjacent, or a neighbor of p that is nonadjacent to q. The minimum degree is two and the graph has no triangles or four-cycles. Hence whenever a first gate reads p,q, p has another reader bypassing that gate. Its zero cofactor loses at least two gates, or three if zero forces the first gate. The same applies with p and q exchanged. The finite checks calculate the corresponding bounds on each of the four slices. Any gate with two raw operands can be placed first, so the slice test applies to every such gate.

## Six- and seven-vertex bounds

Let T be the theta graph induced by {1,2,3,5,6,7,8}, with poles 2,8. Its three paths between the poles have lengths 2,3,3. Deleting one vertex produces exactly three types. The following minima hold with free signs.

| Six raw vertices | Starting lower bound | Size excluded by signed SAT | Matching star upper bound |
| --- | ---: | ---: | ---: |
| 2,3,5,6,7,8 | 7 | 7 | 8 |
| 1,2,5,6,7,8 | 7 | 7 | 8 |
| 1,3,5,6,7,8 | 6 | 6 | 7 |

The starting bounds use the [signed first-gate elimination recurrence](petersen-gate-elimination.py). For T, deleting either pole leaves a graph of cost seven; every nonpole deletion costs eight. The four-slice first-gate test excludes eight or fewer gates. At nine, the first gate must be the OR of the poles (represented by AND of their complements and free output polarity). The signed SAT instance with that gate and the proved cofactor bounds is UNSAT. Hence T requires at least ten gates.

The other seven-vertex graph J is induced by {1,2,3,4,5,7,8}. The elimination recurrence gives seven. Signed SAT excludes seven and eight. A nine-gate star formula attains the resulting bound.

## The eight-vertex exclusion

In H, deleting 0,2,3 or 5 gives a graph isomorphic to J. Deleting any of 1,4,7,8 gives a graph isomorphic to T. Thus the zero-cofactor bounds are nine and ten respectively. The four-slice test excludes ten or fewer gates. For an eleven-gate circuit, every possible first gate is an OR between two of {0,2,3,5}. H has eight automorphisms. They partition the six candidate pairs into two orbits, represented by (0,2) and (0,5). Both signed SAT instances are UNSAT. This proves that H needs at least twelve signed binary gates and gives the contradiction for L-meta-3248.

## Reproducing and auditing the finite exclusions

The [graph checker](petersen-deletion-check.py) verifies all vertex relabelings, the slice calculations, the two pair orbits, and the star upper bounds on complete truth tables. The [signed circuit encoder](petersen-signed-induced.py) uses one pair of distinct earlier-wire selectors and two independent sign bits per gate, and one free output sign. It evaluates **every row** of the induced graph. All essential sources and nonfinal gates have readers. Commutativity orders the two operands, and a greedy topological ordering sorts the ready gates by larger operand then smaller operand. For a prescribed first gate, only the suffix needs this sorting. A newly ready gate reads the wire just produced, so its larger operand exceeds those of all previously ready gates. Ties can be placed in any order.

The direct-dependency, reader-count and sensitivity clauses implement the conditions above. Only the theta and eight-vertex checks need the sharpened cofactor bounds or the seed restrictions. Each exclusion concerns a *globally minimal* circuit of the indicated size, so the smaller sizes are handled first. The solver runs with `--check --checkproof=2`. A timeout is inconclusive. Positive SAT models, when returned, are decoded and evaluated independently on the full truth table.

Run these commands from the repository root with the Lean toolchain installed:

```sh
python3 notes/petersen-deletion-check.py
python3 notes/petersen-signed-induced.py 235678 7
python3 notes/petersen-signed-induced.py 125678 7
python3 notes/petersen-signed-induced.py 135678 6
python3 notes/petersen-signed-induced.py 1235678 9 --theta-cuts
python3 notes/petersen-signed-induced.py 1234578 7
python3 notes/petersen-signed-induced.py 1234578 8
python3 notes/petersen-signed-induced.py 01234578 11 --known-cofactors --seed 0,2,1,1
python3 notes/petersen-signed-induced.py 01234578 11 --known-cofactors --seed 0,5,1,1
```
