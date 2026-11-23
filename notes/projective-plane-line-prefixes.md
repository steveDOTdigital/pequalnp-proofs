# Ten completed line stars already force 64 gates

For L-meta-650, consider a monotone fan-in-two circuit for incidence in the projective plane of order three. Suppose it contains ten ordinary line stars on distinct lines. Each uses three binary ORs on its four point inputs and one AND with the line input. Its other gates may use any inputs, intermediate ORs and completed stars, with unrestricted sharing and AND depth. **The circuit has at least 64 gates.** The ordinary thirteen-star construction attains 64. Interchanging points and lines gives the same conclusion for ten point stars.

## Reduce to three lines

Distinct lines meet at exactly one point, so their stars cannot share a genuine OR of two or more points. Order the forty star gates first. Set their line inputs to zero in succession. Before each setting the target still depends on that line: turn on just its bit and one incident point. The only prefix signals depending on that line bit are the bit itself and its completed star. At least one must feed a live suffix gate, since the residual function depends on several lines. Both signals become zero, so a consuming AND or OR can be removed by constant propagation. Earlier eliminations leave the same argument valid at each step. Ten settings therefore save at least ten suffix gates.

Under a budget of 63 this leaves at most thirteen gates for the three unfinished lines. Fix all points outside their union to one. Each old point OR becomes constant one or remains a disjunction of at least two distinct points from a single old line. Call the latter a helper. Identify duplicate signals and discard unused ones. Every helper contains at most one point of any unfinished line.

Every remaining **raw** input must itself feed the output subcircuit. For a point, select an unfinished line through it, turn on just that line, set its other points to zero, and set every point outside it to one. Toggling the point changes the output while every helper stays one. The three line bits are also required, since helpers depend only on points.

Call a pair of raw inputs switchable if, after fixing all other raw inputs with every helper constant, its output can be restricted both to AND and to OR. For any two unfinished lines meeting at a point p, p and either line bit u are switchable. To get AND, allow only u to be active, clear the other points on u and turn on all points outside u. To get OR, turn on the other line v, clear its points except p and turn on all points outside v. Now u sees a true point whenever u is on, and v contributes exactly p. All helpers stay one in both tests.

## Count uses of live signals

A connected output subcircuit with s distinct sources and g binary gates has g − s + 1 operand uses beyond the first use of every non-output signal. This follows by subtracting s + g − 1 from the 2g operand positions. Bypass constants and copies first. With zero excess uses it is a read-once formula. In such a formula any restriction depending on just two source leaves computes the fixed operation at their least common ancestor: all other gates on their paths must pass the varying input through. Thus a switchable pair excludes zero excess uses.

With one excess use, exactly one signal z is used twice. Its input subcircuit is a read-once tree. Let R be its source leaves, including z itself if it is a source. Outside that tree each source occurs once and the two occurrences of z may be regarded as two leaves. A switchable pair must straddle R. If both were inside, the outer circuit under each test would be a monotone unary function of z, necessarily the identity. If both were outside, z would be constant in each test and the pair would again have a fixed least common ancestor. This argument treats helpers as source leaves: their values are fixed in the tests even when their defining sets contain a varying point.

## Three concurrent lines

Here there are ten point inputs and three line inputs. With two or more helpers there are at least fifteen sources, already requiring fourteen gates. With one helper and at most thirteen gates there are zero excess uses, contradicted by a switchable pair.

Without helpers the incidence graph is a tree with twelve edges and minimum cover size three. The three lines cover it, and one private point on each line gives a matching of size three. The forest lower bound gives 12 + 3 − 1 = 14 gates. [Forest theorem](../lean/PEqualNP/MetaComplexity/Helpers/ForestBound.lean)

## Three lines forming a triangle

There are nine points and three line bits. Two helpers force at least fourteen sources and, under a thirteen-gate budget, a read-once formula. More helpers exceed the budget. With one helper there are thirteen sources, hence at most one excess use. The six switchable incidences between the three line bits and their three pairwise intersection points form a connected six-cycle. Consequently R contains all three line bits or all three intersection points, and none of the opposite group.

Set all six private points to zero. If R contains the line bits, consider the three choices of a single active intersection point. At least two choices give the helper the same value. The signal z is then the same function of the three line bits in these two settings. Each setting needs a nonconstant output and the outer circuit sees those bits only through z, so both outputs would equal that same function. In fact they are the ORs of two different pairs of line bits.

If R contains the intersection points, the helper sees at most one of those three points: any two of them already determine an unfinished line. With private points zero, the helper is zero or equals one intersection bit. Fix that bit to zero, choosing an arbitrary intersection bit if the helper is already zero. Two independent intersection bits remain inside R. Two choices of a single active line outside R select the first and second bit separately. Neither choice changes the function z of the two bits. A monotone unary function of z cannot recover both projections in this way.

Finally, if no helper is used, set the six private points to zero one at a time. Each remains essential until fixed, and its setting removes at least one consuming gate. This would leave at most seven gates for the six-cycle. The exact monotone circuit check returns UNSAT for that budget. Its six edge inputs and all maximal independent sets determine the full truth table by monotonicity. Eight gates suffice via three two-edge stars. [Exact search and encoding](check-small-cover-bound.py)

To reproduce the six-cycle check, run from the repository root with the Lean toolchain's CaDiCaL on PATH:

```sh
python3 -B - <<'PY'
from runpy import run_path
search = run_path("notes/check-small-cover-bound.py")["search"]
cycle = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]
print(search(6, cycle, "cadical", 60, budget=7))
PY
```

The two configurations exhaust the 286 triples of lines. Of these, 52 are concurrent (four triples at each of thirteen points) and 234 form triangles. In each case at least fourteen suffix gates survive the restrictions. Adding back the ten eliminated suffix gates and the forty star gates gives 64. Circuits with fewer than ten complete stars on each side remain candidates for the assignment.
