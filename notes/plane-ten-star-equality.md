# Ten completed stars force all thirteen at 64 gates

L-meta-1481 asks for a 64-gate monotone circuit for point-line incidence in the order-three projective plane which loses both formal directional derivatives at some incident flag. The 26 inputs are thirteen points and thirteen lines. The label difference modulo 13 lies in {0, 1, 3, 9} at incidence.

**Equality theorem.** Suppose a binary AND/OR circuit with distinct earlier operands computes incidence, has at most 64 gates and contains ordinary stars on ten distinct lines. Its live circuit consists of all thirteen ordinary line stars and a binary OR tree over their outputs. It has exactly 64 gates. The dual statement holds for ten point stars. Every incidence has both formal derivatives in these circuits. A witness for L-meta-1481 must therefore contain at most nine ordinary stars on each side.

An ordinary star is an AND of its raw line bit and a three-gate OR tree on its four incident raw points. Its intermediate wires may initially be read anywhere. The [previous lower bound](projective-plane-line-prefixes.md) showed that ten stars cost at least 64 gates. The new claim characterizes equality, including arbitrary suffix gates and possible use of intermediate wires. The structural proof below uses three small SAT exclusions. The [search and built-in proof checks](plane-three-line-cores.py) reproduce them. The [supplementary Lean lemmas](PlaneElevenStars.lean) concern the two-line path and single-read derivatives. They do not formalize the equality theorem.

## The two eight-gate cores

Three unfinished lines form a triangle or meet at one point in a pencil. For the triangle, retain just its three intersection points. The incidence graph of those points and the three lines is a six-cycle. For the pencil, retain the common point and one private point per line. The seven inputs form three length-two arms.

Each core costs exactly eight gates. Three two-edge line stars and two final ORs suffice. For the pencil the [forest lower bound](../lean/PEqualNP/MetaComplexity/Helpers/ForestBound.lean) gives six edges plus a cover of size three minus one. The matching from each line to its private point proves the cover bound. For the cycle the [independent Boolean calculation](plane-small-core-bounds.py) rules out two or fewer reads beyond the first in its live graph, giving at least eight gates. The [earlier exact search](check-small-cover-bound.py) also excludes a seven-gate cycle.

At eight gates the pencil must contain the three ordinary line stars. The six-cycle must contain the three ordinary stars on one side or the three ordinary stars on the other side. For the pencil, forbid the star of one named line. For the cycle, if neither side has all three, there are missing stars on opposite sides. Up to cycle symmetry the two named centers are adjacent or opposite. All three SAT instances are UNSAT. The positive controls return actual eight-gate circuits for the same functions.

The encoding chooses one operation and two different earlier operands per gate. A nontrivial monotone function can be checked on its minimal positive and maximal negative rows. Every minimum circuit has all its gates live. Ready gates can be sorted by their larger operand, breaking ties by the smaller operand, because a newly ready gate reads the latest, largest wire. The forbidden pattern is exactly an OR of the two raw neighbors followed by its AND with the raw center. Once three stars are present they consume six gates. The last two live gates can read at most three distinct outside wires and must see each center bit through its star or its raw bit. Turning the other two centers off shows the raw bit alone would lose sensitivity to a neighbor. Thus the three sources are the three stars and the last two gates form their OR.

## Restrict the forty-gate prefix

Choose ten completed lines. Two such stars cannot share a nontrivial point OR since their lines meet only once. The forty distinct gates can be scheduled first. Their live suffix has at most 24 gates. Let U be the union of the three unfinished lines. For each completed line the suffix must use its raw line bit or its star, the only prefix wires depending on it. Each unfinished line bit and every raw point in U must also be read. For a point q, turn on just an unfinished line through q, set its other points to zero and every point off it to one. Varying q changes incidence. Each prefix point OR containing q also contains an off-line point, so it stays one. Completed stars stay zero.

We use simultaneous pinning. In a connected output cone with g binary gates and s distinct sources the undirected multigraph has cycle rank g − s + 1. Setting k distinct live sources to constants, propagating constants and retaining a nonconstant output removes at least k gates. The simplified graph is a connected minor, since a gate with one surviving varying operand can be contracted onto that wire and unused components deleted. If g′ gates and s′ sources survive, g′ − s′ ≤ g − s and s′ ≤ s − k. The argument also works with correlated source wires. First pin the specified source wires in the abstract circuit, then specialize the others or give equal sources the same input label. These final substitutions cost no gates. Boolean copies and repeated operands can be removed for the lower bound.

Turn off all ten completed line bits and keep only the core points described above. Set all other points of U to zero. Either geometry has **six mandatory raw points** turned off. First set all points outside U to zero, then consider the alternative setting with all of them one. In either setting ten completed channels and six other raw sources become constant and the surviving target costs eight gates. A seventeenth distinct constant source is impossible, since 24 − 17 < 8.

It follows that each completed line uses exactly one channel. No raw point outside U can be a suffix source. No used intermediate point OR can contain a point outside U, since it would become one in the second setting. A used intermediate OR must also meet the retained core point set in every choice of core, since otherwise it would become zero in the first setting.

- For a pencil, an old line through the common point meets U only there. An old line avoiding the common point meets each unfinished line in just one private point. Representatives can be chosen on all three lines to avoid those points. No nontrivial intermediate OR survives both tests.
- For a triangle, an old line meets the three intersection points in at most one, since each pair determines an unfinished line. A surviving OR must contain one of them, c. It can also contain exactly one private point a, necessarily on the opposite unfinished line. The only possible extra helper is therefore of the form c OR a. Each private point has just one opposite intersection.

Every completed channel must be its star. Each completed line j has a point outside U, since each of three other lines meets it at most once and it has four points. Set only the bit of j to one and vary a single such outside point, with all other points zero. The target changes. The raw bit alone could not transmit this change and the preceding tests eliminated every other point-dependent source that could carry it.

Set points outside U to one. All ten completed star channels now equal their raw line bits and vary independently of the residual points, lines and surviving helpers. In this abstract suffix the target is the OR of ten independent alarm bits and the three-line incidence function. The resulting wiring is the original suffix wiring.

## Restore the private points

First set the ten alarms to zero. The remaining circuit has at most fourteen gates. Starting with either eight-gate core, six further private points have to be restored. In the pencil fix one representative per line throughout. In the triangle start with no private points.

For any subset of k restored points a circuit for that subproblem costs at least 8 + k gates, even with the allowed free helpers. Each of the k raw private points must be read. In the pencil there are no helpers. In the triangle choose only its own line, turn the other points on that line off and its opposite intersection on. This saturates the only possible helper containing the point. Toggling the raw point changes the answer. Pin all k raw sources to zero, then identify any surviving helper with its opposite intersection. The eight-gate core remains. Simultaneous pinning proves the bound, and attaching private points to ordinary line stars attains it.

Take any optimal circuit at level k and set one restored raw private input a to zero. Its direct reads must all disappear. It has exactly one reader because the next level costs 8 + k − 1. Its reader is an OR. If it were an AND it would become zero and remove a second gate consuming its output, while the pinned target is nonconstant. Contract the OR onto its other operand w. In the triangle reconnect any reads of the free helper c OR a to c. The result is optimal at the preceding level. There is no budget for a dead or redundant gate.

Reversing this step inserts a gate a OR w and redirects a nonempty selection of the old reads of w to it, with the output itself eligible when w was the root. The triangle can also replace some former reads of c by c OR a. In the preceding line-star circuit each occurrence of c is a point leaf in a star for one of the two lines through it. Forcing that occurrence high when a alone is high would create a false incidence with that line. All additional changes only raise wire values. No such replacement is possible. This reasoning includes a replacement at the other operand of the inserted OR. In the alternative six-cycle orientation c is a star center with two neighbors, neither equal to the line of a. Replacing it gives the same contradiction.

Consider the ordinary OR insertion. In a line-star circuit an insertion in the final OR tree or at a star output would accept a alone. An insertion at a line bit cannot produce the required edge with all old points zero. Inserting into a point-OR tree works precisely when the selected occurrence is in the star of the line of a. Sending it to any other line creates a false edge. Each raw point occurs at most once per star and nontrivial OR subtrees are private to their own star. The extension therefore attaches a to a single leaf or subtree of its own line star. In the opposite orientation of the bare cycle an insertion at a point center would accept a with both of that center's neighbors. An insertion on the line-input side needs an old point to fire. Neither gives the one required edge, so that orientation disappears at the first private point. Induction leaves exactly the three ordinary line stars joined by OR for the full residual geometry.

## Restore the ten alarms

With t independent alarms the minimum is 14 + t. Pinning them to zero removes at least t gates and the point argument gives fourteen. The matching upper bound joins the alarms by OR. At equality each alarm has a single OR reader by the same one-gate pinning argument.

Starting with the three line stars, inserting a new alarm at a raw point, inside a point OR, or at a line bit cannot make the output true when the alarm is the only high input. Every AND still lacks its other type of input. An insertion at a star output, an existing alarm, an upper OR, or the root simply joins the new alarm to the top OR tree. Those wires have a single read, counting the designated output. This preserves the claimed form throughout. Replacing the independent alarms by their actual completed stars now gives thirteen ordinary stars joined by OR. The count exhausts all 64 gates, so there were no dead gates.

At a flag, the line direction passes its star's AND because the incident point makes its point OR true. In the reverse direction the point seed passes the OR tree and the incident line makes the AND transmit it. The final OR tree transmits both. The dual argument interchanges points and lines.

## Reproduction and the open case

From the research repository's Lean directory run the following commands with its pinned toolchain.

```sh
python3 ../notes/plane-three-line-cores.py --classify-core --seconds 180
python3 ../notes/plane-three-line-cores.py --pencil --classify-core --seconds 180
python3 ../notes/plane-small-core-bounds.py
lake env lean ../notes/PlaneElevenStars.lean
```

The independent extension enumeration on the six-cycle with one, two and three specified private leaves gives respectively 9, 27 and 81 optimal circuits up to gate scheduling and operand order. None has even a single missing direction. It checks whole truth tables. A separate 66-gate control appends a duplicate of the last OR in the ordinary 64-gate circuit and ANDs the two distinct output wires. It passes all 52 minimal positives and 704 maximal negatives, and both formal directions vanish at all 52 flags. The 64-gate problem with at most nine complete stars on each side remains open.
