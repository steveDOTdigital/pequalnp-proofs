# The Heawood edge function has AND complexity seven

Consider the 14-variable edge function from L-meta-2278. The point neighborhoods
in line labels are 0: 7,8,10; 1: 7,9,13; 2: 8,12,13; 3: 7,11,12; 4: 10,11,13;
5: 9,10,12; 6: 8,9,11. Every vertex has three neighbors, and any two vertices
on the same side share exactly one neighbor.

**Claim.** With arbitrarily many free OR gates, computing the edge function needs
exactly seven binary AND gates. This allows nested ANDs, arbitrary sharing, and the
desk's extra input OR(0,1). Seven point stars achieve the upper bound. The counting and geometric arguments
below give a direct proof. [An independent finite check](heawood-six-and-core.py)
uses the standard Python library. [Lean verifies the final four-edge contradiction](HeawoodPortPairing.lean).
The full lower bound on the number of AND gates is not formalized in Lean here.
L-meta-2278 additionally asks for a lower bound of 26 on the total paid size.

## Paid gates and raw input ports

Propagate constants and copies. Since OR gates are free, each operand of an AND
is an OR of raw inputs and outputs of earlier AND gates. Call the subset of raw
inputs on one operand its *port*. At each gate, factor out raw variables common
to both operands using (X∨A)∧(X∨B) = X∨(A∧B). Record the old output as the OR of
X and the new gate, and substitute that OR at later uses. In topological order
this costs no additional ANDs and makes the two ports at every AND disjoint.
Constants produced in the process can again be propagated. The final OR contains
no raw input since all singleton inputs are false. Every normalized AND also
vanishes on all singleton inputs, by induction and disjointness.

With k ANDs a monotone circuit has at most 2^k maximal false rows. Indeed, choosing
one operand at each AND yields an OR of literals (here just positive raw inputs)
or a constant, which is a pointwise upper bound on the original circuit. At a
given false row, choose an operand evaluating to false at each false AND; other
choices there are immaterial at true ANDs. Induction preserves every gate value
on that row. The resulting OR's false rows form a principal down-set, so it can
contain at most one maximal false row of the original function. Constants satisfy
the same conclusion whenever the function has a false row.

A maximal false row consists of a set of points together with all lines missing
it, and includes every point missed by those lines. The possibilities for the
point set are the empty set, all seven points, any singleton, any pair, or the
complement of any line. For a pair, exactly two lines miss it and their union
is its five-point complement. No line misses a collinear triple; a noncollinear
triple is missed by one line and can be extended to its four-point complement.
A set of four or more points missing a line must equal its complement. Thus the
five classes have sizes 1,1,7,21,7, totaling 37. Fixing a particular point true
leaves 1+1+6+4 = 12 maximal rows containing it; fixing a line is dual. Thus a hypothetical circuit with at most six ANDs
has exactly six. Each raw input occurs in at most two ports: setting that input
to true removes every AND having that input in a port, while the remaining
function needs at least four ANDs. The two ports at any single AND are disjoint.

Every raw vertex is essential. If two input rows activate the same set of ports,
the entire circuit has the same value on them: later ANDs only use these port
values and earlier AND outputs. For a point p, the row of all lines and no points
is false and adding p is true. Hence at least one port containing p has no lines.
The dual statement holds for each line.

For a vertex v with two ports, let a and b be other raw inputs in its respective
ports. They must be adjacent. Otherwise choose a neighbor w of v adjacent to
neither a nor b. Each of a,b on v's side blocks at most one of v's three neighbors;
one on the opposite side blocks none. The vertices a,b,w form an independent
set, with equality among them allowed. Adding v makes an edge but activates
no additional port. The same argument shows that a vertex occurring in only one
port must be alone in it. These separation arguments also follow by extending
the independent set to a maximal false row.

## Peeling the ports

Whenever a port contains only one remaining vertex, discard that vertex from
all ports and remove empty ports. Each discarded vertex consumes at least one
distinct port. For a surviving vertex, every port originally containing it
still survives. The companion-pair adjacency condition still applies to all
remaining companions, and each vertex retains at least one pure-side port.

At termination each surviving vertex has exactly two ports of size at least
two. Its two sets of companions must be on opposite sides, since all their cross
pairs are graph edges. It therefore lies in one pure group and in one mixed
pair. To see the latter has size two, a mixed port of size at least three contains
two vertices of the same side and one of the opposite side. Either of the first
two vertices then has companions of both colors in one port, impossible since
it has a companion in its other port.

The mixed pairs biject r points with r lines. The pure groups partition each
side. For a point p in a pure group, all other group members are neighbors of
the mixed partner of p. A group of size four or more is impossible: the distinct
mixed partners of two members would share at least two neighbors. Pure groups
thus have size two or three. Counting the peeled ports, the mixed pairs, and the
two sets of pure groups gives

    12 ≥ (14 − 2r) + r + 2 ceil(r/3).

For 0 ≤ r ≤ 7 this holds only for r=6. Equality forces two triples on each side,
six mixed pairs, and just two consumed ports (now empty on the core). Each point's
partner is uniquely determined by the other two points in its triple.

## Four edges suffice to contradict a port pairing

Both point triples are noncollinear: otherwise their three points would have the
same mixed partner. The line groups are forced. The three opposite lines of each
point triangle are mutually compatible in a line group. For a line opposite p,
a partner from the other triangle must have its matched point on that line. The
line contains two points of its own triangle, leaving room for only one point of
the other triangle. The cross-triangle compatibility edges therefore form a
matching. No triple of mutually compatible lines can contain members of both
triangles. This determines both line groups from the point groups alone.

All such pairs of disjoint point triangles are equivalent. Label the seven
desk points, in order, by binary vectors with integer encodings 1,2,4,3,6,7,5.
Each listed line is a triple of nonzero vectors summing to zero, as inspection
of the seven lines verifies. A noncollinear ordered triple is therefore a basis.
In this basis, the four remaining points are the three pair sums and the sum of
all three basis vectors. The pair sums are collinear. A second disjoint triangle
must consist of the total sum and two of the three pair sums; a basis permutation
carries any such choice to any other. All invertible linear maps preserve lines.
Hence one explicit representative suffices. Its ports, in order from 0 to 9, are

    {1,12}, {2,7}, {3,13}, {4,9}, {5,11}, {6,10},
    {1,2,3}, {4,5,6}, {7,12,13}, {9,10,11}.

Each two-vertex edge row must make at least one AND true. At the first such gate
both operands get their true values directly from the raw inputs. Since the raw
ports there are disjoint, one endpoint is in each port. The six AND gates
therefore induce a matching on the ten surviving ports whose paired products
cover every core edge. A port paired with an empty port can be ignored, and the
remaining partial matching can be extended to a perfect matching.

Consider just (1,7), (1,9), (1,13), and (5,12). Point 1 occurs in ports 0 and 6.
Of its three target lines, the only two sharing any port are 7 and 13, which share
port 8. Thus one of ports 0 and 6 must pair with 8, and the other must pair
with 3 or 9 to reach line 9. Both ports containing line 12 (0 and 8) are now
paired, and neither is paired with port 4 or 7, the only ports containing point
5. This contradicts the fourth edge. As separate checks, the program enumerates 42 valid layouts, confirms that they
form one orbit under the 168 line-preserving permutations of the points, and tries
all 945 pairings in each. Every pairing covers at most 14 of its 16 core edges.

The boundary in the desk statement suffices: by monotonicity, the 21 edge rows and
37 maximal independent rows determine the whole function. This remains true after
appending the free monotone OR input. Consequently the AND-count theorem applies
to every circuit in the assignment. The remaining budget question concerns
circuits with seven or more ANDs and at most 25 paid gates.

## Reproduction

Run `python3 notes/heawood-six-and-core.py` from the checkout. It checks the
graph, all fixed-true row counts, the companion separation property, the layout
orbit and all port pairings. The graph data are in
[heawood-first-gate-bound.py](heawood-first-gate-bound.py), which also implements a
weaker independent first-gate lower bound. A [separate SAT encoding](heawood-and-budget.py)
replays the seven-star control on all 16,384 inputs. Its unconstrained six-AND search
reached a 150-second limit; the exclusion above uses the finite core argument.
