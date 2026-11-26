# Raw input sides in the 19-gate plane circuit

[L-meta-5060](https://pequalnp.com/lemma#L-meta-5060) concerns a 19-AND circuit for the order-four projective plane. Its 42 variables are the 21 points and 21 lines. An input is accepted exactly when it contains an incident point and line. The [opposite is L-meta-5061](https://pequalnp.com/lemma#L-meta-5061). The following necessary conditions leave the full claim open.

**[At least 28 variables survive singleton removal](#at-least-28-variables-with-equal-shores-at-28).** Start with the 38 signed raw sides (the left and right variable sets at all 19 gates). Restrict all the sides to the remaining variables. Whenever a side contains only one variable, remove that variable and discard resulting empty sides. Repeat until every retained side contains at least two variables. At exactly 28, fourteen points and fourteen lines survive. The bound holds for every order of removal. In the original circuit each of the 42 variables also occurs on at least one side of size at most three.

## Recovering variables on independent inputs

For input set X, write down one bit for each raw side, indicating whether it meets X. The circuit is monotone in these bits because its output has no bare variables and all gate operations are monotone. A variable v is read by at most three signed sides: it is read by at most three gates, and the two sides of a gate are disjoint.

Suppose v is absent from an independent input X but every raw side reading v meets X. Pick one representative other than v from X on each such side and call their set T. It is independent and has size at most three. Choose a neighbor w of v not adjacent to any member of T on v's shore. Such a neighbor exists: every other vertex on that shore shares at most one neighbor with v, which has five neighbors. Then T together with w is independent, while adding v creates an edge. The raw-side bits are identical on the two inputs. This contradicts computation of the posted graph.

Consequently, on any independent input, a variable is present exactly when all its raw sides meet the input. Equivalently, choosing one substitute other than v on each of its sides must always produce a set containing an edge. This condition also holds when every side and all substitutes are restricted to any fixed vertex subset. The argument uses only raw inputs and hence includes circuits with arbitrary internal gate fanout.

## A side of size at most three for every vertex

A singleton side suffices. Otherwise remove v from its incident sides when considering possible substitutes. Some residual side A must consist entirely of points and some other side B entirely of lines. Choosing substitutes of just one shore would be independent. With two residual sides, all pairs across A and B must be adjacent. Two points have only one common line, so one side has a single substitute. With three residual sides, suppose A and B each have at least three members; otherwise the desired bound already follows. Any point of the third side C must be on every line of B that misses some point of A. At most one line meets every point of A. Thus at least two fixed lines of B must contain every point of C, and C has at most one point. Dually C has at most one line. Restoring v gives a raw side of size at most three.

The cyclic differences in the posted graph are 0, 5, 7, 17 and 20 modulo 21. As a check on the last step, for each triple of points A and each triple of lines B, intersect the neighborhoods of the endpoints of every nonincident pair across A and B (take their union for each pair). This lists all possible substitutes in C. Across all 1,768,900 ordered choices of the two triples, 1,254,400 intersections were empty, 403,200 had size one and 111,300 had size two.

## The counting argument

On removing a singleton variable at least one side disappears with it. There are initially four fewer sides than vertices, so at termination the number of sides is at most the number of vertices minus four. The resulting set is nonempty. Each surviving vertex needs both a pure side of its own shore and a mixed side on which it is the only member of its shore: otherwise it has an independent choice of substitutes, all from one shore. Both shores therefore survive.

Fix a shore of size k. For each v choose one mixed side W(v) on which v is that shore's only member. These k sides are distinct. Choose an opposite-shore vertex t(v) on each W(v). For each v, let its signature consist of all its remaining sides. It has one or two of them, since it needs a pure side and the original read limit is three. If another vertex q on this shore has a signature containing v's signature, then q must neighbor t(v). Otherwise q and t(v) supply independent substitutes on all the sides of v. The chosen sides W of other vertices on the same shore contain no v.

Each signature class has at most three members. For a class of four or more, the chosen witnesses of any two members both neighbor all the other members, including two distinct vertices. They must be the same opposite vertex. This would read at least four distinct sides. Furthermore a class of three cannot be collinear (or concurrent on the dual shore). The three witnesses would all have to be the unique common neighbor and occupy three mixed sides. The same witness, itself a surviving vertex, needs a pure side as well.

With at most two remaining side labels on a shore, k is at most six. Write a,b,c for the multiplicities of signatures using only the first label, only the second, and both. Each is at most three. If c is positive and a is three, the three members of the first class are noncollinear. A member of the third class must lie on all three distinct lines through pairs of the first class, which is impossible for a noncollinear triple. Hence a and b are at most two when c is positive. A total of seven would require a=b=2 and c=3. The witness for a member of the first class would have to neighbor all three members of the third class, which are noncollinear. This is again impossible.

When a shore of size k at least seven has a single pure side, it contains all k vertices. Each member must have one further mixed side beyond W(v). Without that extra side the chosen witness would neighbor the other k−1 vertices, exceeding degree five. There is room for just one extra mixed side per vertex. At most three vertices use any one as their extra, by the signature-class bound. Thus the number of mixed sides is at least k plus the ceiling of k/3.

Four further restrictions sharpen the count.

1. A class of three is incomparable with every other occupied signature. A smaller signature would have a witness neighboring the whole noncollinear triple. For a larger signature, its vertex would have to lie on all three lines through pairs of that same noncollinear triple.
2. For a class of size two with at least two vertices having strictly larger signatures, the witnesses of its two members must coincide: they neighbor the same two larger-signature vertices. Each chosen mixed side contains just its own vertex and that common witness, since every opposite-shore vertex on the side must serve as a witness. The two class members and all strict supersets lie on this one line. Each such class therefore consumes one mixed side beyond those available as distinct private choices for the opposite shore. Distinct classes use disjoint pairs of sides.
3. Suppose a class of three has an extra mixed side besides its chosen private sides. Its common signature then consists of one pure side H and this mixed side J. Pick an opposite vertex t on J. Every q in H outside the class must neighbor t: for each class member v, use q on H, t on J and the witness on W(v). If q missed t, it would have to neighbor all three W witnesses. Those are the three distinct sides of the noncollinear triangle formed by the class. Thus H outside this class has at most five vertices and cannot contain an entire other class of three.
4. If a shore with a single pure side has k at least nine, a three-member group from the preceding paragraph would have to fit k−3 other vertices on one line. For k equal to eight, two groups of three would instead give two lines each containing the complement of its group. The lines share at least two of the eight vertices and hence coincide, which would put all eight on one line. Thus when k equals eight at most one group has three members, and at least four extra mixed sides are required. For every k at least eight the lower bound on the mixed sides is k plus the ceiling of k/2.

Let p,l be the two shore sizes, M the mixed-side count and A,B the pure-side counts. We have M ≥ max(p,l), A,B ≥ 1 and M+A+B ≤ p+l−4. There are at most M−p+A remaining point labels and at most M−l+B remaining line labels. Labels unused by a shore can be included with zero occurrences. For up to three labels, the following replay checks their possible signature multiplicities. For more labels it only applies the single-pure-side estimate, which suffices for the bound.

```python
from itertools import product

def shore_possible(k, opposite, mixed, pure):
    if pure == 1 and k >= 7:
        group_limit = 3 if k == 7 else 2
        if mixed < k + (k + group_limit - 1) // group_limit:
            return False

    # Each chosen mixed side is private on this shore. The remaining
    # labels start with the pure sides, followed by any extra mixed sides.
    labels = mixed - k + pure
    if labels > 3:
        return True
    pure_mask = (1 << pure) - 1
    masks = [i for i in range(1, 1 << labels)
             if i.bit_count() <= 2 and i & pure_mask]
    for counts in product(range(4), repeat=len(masks)):
        if sum(counts) != k:
            continue
        duplicates = 0
        valid = True
        for s, n in zip(masks, counts):
            if not n:
                continue
            above = [t for t, h in zip(masks, counts)
                     if h and t != s and t & s == s]
            upper_sizes = [counts[masks.index(t)] for t in above]
            upper = sum(upper_sizes)
            if (3 in upper_sizes or (n == 3 and upper)
                    or n - 1 + upper > 5):
                valid = False
            if n == 2 and upper >= 2:
                duplicates += 1
                if n + upper > 5:
                    valid = False
            if n == 3 and s & ~pure_mask:
                pure_label = s & pure_mask
                outside = [h for t, h in zip(masks, counts)
                           if t != s and t & pure_label]
                if sum(outside) > 5 or 3 in outside:
                    valid = False
        if valid and duplicates <= mixed - opposite:
            return True
    return False

survivors = []
for p in range(1, 21):
    for l in range(1, p + 1):
        if p + l > 20:
            continue
        for mixed in range(p, p + l - 5):
            for a in range(1, p + l - 4 - mixed):
                for b in range(1, p + l - 3 - mixed - a):
                    if (shore_possible(p, l, mixed, a)
                            and shore_possible(l, p, mixed, b)):
                        survivors.append((p, l, mixed, a, b))
assert survivors == [(10, 10, 12, 2, 2)]
```

The extra posted hypothesis bounding the number of gates reading either endpoint of a nonincident point-line pair was not needed. The first count leaves a single size-20 configuration. The stronger argument below excludes it.

## Twenty-six variables survive singleton removal

The bound now uses the placement of the two input sides of each AND gate. With at most 25 surviving variables the separate input-side constraints leave just four triangles on each shore, on a total of 24 vertices. Neither of the two arrangements that can start all the internal edges can also start every edge to an exterior vertex. At 26 vertices, two parameter lists survive the tests below. The [compatibility argument below](#at-least-28-variables-with-equal-shores-at-28) also excludes those two size-26 lists. The full posted claim remains open.

### Partitioning a shore

Use the singleton-free core and the chosen private mixed side W(v) from the counting argument. Select one opposite-shore vertex as a representative of **each mixed side**, once for the whole shore. Each representative occurs on at most two mixed sides, since it also needs a pure side and is read at most three times. Write t for the representative of W(v).

Assign v to one pure side H that it reads. The assignment can be made as follows. If v reads two pure sides, t together with a nonneighbor on each would be an independent set of substitutes. Thus on at least one of those sides every other vertex neighbors t. Choose that side. Call v *simple* whenever its chosen original pure side has this property. If v has just W(v) and one pure side, it too must be simple.

Every remaining v has one pure side H and one more mixed side J. The latter is one of the M−k mixed sides outside the k private choices on a shore of size k, since none of the chosen private sides for other vertices on this shore contains v. Write z for the representative of J. In this case:

- Every other member of H neighbors t or z. Otherwise it supplies an independent set of substitutes together with t and z.
- Every other same-shore member of J neighbors t. To see this, choose a member of the original H other than v that misses t, which exists because v is not simple. These two same-shore substitutes together with t would be independent if the substitute on J also missed t.

Replace each pure side for this count by the group of vertices assigned to it. The groups partition the shore and the two necessary conditions still hold after the restriction. Collect the vertices using each extra J. At most three can use it: if four did so, the witnesses of any two would share the other two neighbors and hence be identical, exhausting the two mixed reads available to that witness. Three such vertices must be noncollinear because the line through any two would otherwise be the witness of all three. Both conclusions apply also when these vertices belong to different pure groups.

### Enumerating one pure group

The [finite verifier](plane-raw-sides-5060.cjs) checks every pure group of up to seven points in the posted geometry, up to incidence-preserving permutations that it verifies before using. It accounts for all 116,280 seven-point subsets. For a group H it enumerates its partitions into simple singletons and parts of sizes one, two or three, one part for each extra mixed side used in that group. For every part it tries every choice of representative z and every private witness t for each member. Simple vertices need only t. It enforces both neighborhood conditions and the limit of two uses of each representative across distinct mixed sides.

No seven-point group passes. A larger group would give a seven-point example by restriction: keep the chosen seven vertices, their private witnesses and the extra sides used by them. The same inequalities still hold, even if some vertices could now be classified as simple. A six-point group passes only with three parts of size two on three distinct extra sides. Point-line duality holds in the posted coordinates by sending point i to line minus i, and line j to point minus j.

The verifier then distributes the feasible pure groups over a shore. Each extra mixed side can receive at most three vertices across all groups, and two different parts of one group require distinct extra sides. This test allows different groups to choose their geometry independently. Enumerating the side counts on both shores up to a total of 26 gives the following possibilities before requiring the operands to be paired into gates.

| Points | Lines | Mixed sides | Pure point sides | Pure line sides |
| ---: | ---: | ---: | ---: | ---: |
| 12 | 12 | 12 | 4 | 4 |
| 13 | 13 | 16 | 3 | 3 |
| 15 | 11 | 15 | 5 | 2 |

### Pairing the sides into gates

In the first row all mixed sides are private on both shores. All twelve points are simple and split into four groups of three, as a purely simple group has size at most three. The same holds for the twelve lines. In each triple the points are noncollinear, and the line paired with each point on its mixed side is the unique line through the other two. Three collinear points would require their common line on three mixed sides as well as a pure side.

**These twenty retained sides cannot read any exterior vertex.** A core vertex cannot occur on a discarded side, so its raw reads in the original circuit can only be among the retained sides. For each simple vertex, the chosen original pure side had all its other core vertices on its witness line. An additional core point on a pure triple would have to lie on all three sides of its triangle. Thus each pure side contains exactly its assigned core triple, and each mixed side contains exactly one vertex per shore within the core. Each core vertex therefore has exactly two raw reads in the original circuit. An exterior variable on a mixed side would have to neighbor both other points of the corresponding pure triple, because choosing it and either one gives substitutes for the missing point. Their unique common neighbor is already on the mixed side. An exterior variable on a pure point triple would have to neighbor all three lines opposite its points, an impossibility. The dual reasoning covers the pure line triples.

On an input consisting of an incident point and line, at least one gate is true. In the first such gate no earlier gate can help either operand, so its two raw sides must read the two endpoints separately. Consequently a matching of the retained sides must cover all core incidences this way. The verifier enumerates ordered choices of four triangles, keeping only points and opposite lines that are pairwise distinct across the choices. It checks the symmetries used to fix the first triangle, and enumerates every compatible grouping of the lines into their own triples. For each layout it branches on every still-possible disjoint pairing for an uncovered incidence. This covers all possible ways to start the internal edges, even if some retained sides are paired to exterior sides.

Of 101,165 layouts visited after symmetry pruning, only two pass that internal test. For any exterior line meeting more than three of the retained points, at least one of their pure point sides must have a partner outside the retained set. Otherwise every such point would require the exterior line to be read at a different gate opposite the point's private mixed side. This exceeds the three-read limit. Apply the same requirement to exterior points. Requiring it on each branch eliminates both remaining layouts.

The four-triangle count is sharp as a test of the raw input sets alone. For example, take the disjoint point triples (0,1,2), (3,4,5), (6,7,9) and (8,10,12), with opposite lines respectively (1,7,0), (4,10,3), (14,5,6) and (17,8,15). Use one pure side per triple on each shore, one mixed side per point and its opposite line, and singleton sides for the other eighteen variables. These 38 raw sets recover membership on every independent input: substitutes on the two sides of a missing triangle vertex would themselves be incident. This construction explains why the gate-pairing step is needed.

Run `node notes/plane-raw-sides-5060.cjs` from the proof fork to replay the pure-group classification, the size count and both gate-pairing tests. Neither surviving 26-variable parameter list is asserted realizable. No part of this result relies on the additional posted five-gate condition for a nonincident point-line pair.

## At least 28 variables, with equal shores at 28

The two shores must use the *same* mixed sides. Taking this into account excludes all cases through 27. At exactly 28 the only counts left by the argument are fourteen points and fourteen lines, with respectively 14, 16 or 18 mixed sides and respectively 5, 4 or 3 pure sides on each shore.

When choosing the representative on each private mixed side W(v), prefer one making v simple if any such choice exists on an original core pure side read by v. This is possible independently for each v since the chosen private sides are distinct. Extra-side representatives are still arbitrary. All the earlier necessary conditions hold with this choice. For a complex v, each opposite vertex t on W(v) therefore misses some member other than v on its sole pure side. Every other same-shore vertex on its extra J must neighbor **each** such t. Also, for the representative chosen on W(v), the pure-side member it misses must neighbor every opposite vertex on J.

Two shore configurations now have a useful consequence: any extra side of the opposite shore can serve at most one of that shore's complex vertices.

- **All simple triples.** If M=k=3A on a shore with A pure sides, there are no extra mixed sides there. The profiles force each pure group to consist of three simple vertices. The three witnesses of any one group are its three triangle sides. Its original core pure side cannot contain any fourth vertex on its shore, since that vertex would neighbor all three witnesses. Every vertex thus reads just its assigned pure triple and its private mixed side. Any opposite vertex on that mixed side must neighbor both other members of the triple, so the mixed side has exactly one opposite vertex. This applies to all mixed sides.
- **Thirteen vertices, sixteen mixed sides and three pure sides.** The only group profiles fitting the three extra labels are `222`, `0111` and `000`. Here 0 denotes one simple vertex, and each positive digit counts the members of that pure group using a particular extra side. Each extra side therefore serves two vertices from the group of six and one from the group of four. These three complex vertices form a noncollinear triple. They preclude any complex vertex using that same extra side on the opposite shore, since such a vertex would need an opposite-shore substitute neighboring all three. Each of the thirteen private mixed sides contains only one opposite vertex. For a complex member, its two companions on its extra side force every witness onto their unique common neighbor. For a simple member, its assigned group has at least three vertices and the other two pure groups are noncollinear. The group of six exceeds the line size, the group of four with profile `0111` is noncollinear by the geometry check, and the simple triple is noncollinear. A simple member cannot appear on an extra side: the three witnesses of the complex triple on that side have no common neighbor. If it also reads a second pure side, no witness can cover that whole other group, which does not contain it as an assigned member. Thus every witness on its private side must cover all the other members of its assigned group, fixing the witness uniquely. The opposite shore can use only these singleton positions to serve complex vertices.

The verifier applies the one-vertex capacity in these two cases and rechecks the feasible opposite-shore profiles. This rules out all counts at 26 and 27. At 28 it also rules out the 15–13 case with fifteen mixed sides.

In the remaining asymmetric case, the thirteen-line shore has the second configuration above. The fifteen-point shore has five pure sides and just one extra mixed side J. At most one point can use J as a complex point. The only possible five pure-group sizes are therefore 3,3,3,3,3, as is also checked by the verifier. Each of the three extra line sides carries a nonconcurrent triple of lines. At least two of those sides are point-private, since only J is not point-private. Let v be the distinct point assigned to any such private side, and let H be its assigned pure group.

The other two members of H have just one common line. At least two of the three lines on W(v) therefore miss some other member of H. A third raw read is necessary: a missing member together with the line that misses it would otherwise be independent substitutes for v. A second pure read cannot suffice. For each of the two lines, its entire other pure group, containing at least three assigned points distinct from v, would have to lie on that line. Two distinct lines cannot share all three. Thus v must also read J. If J carries another nonconcurrent triple of lines, take any q in H other than v; one line in W(v) misses q and one line in J misses q, giving independent substitutes again. Otherwise J is one of the thirteen line-private sides. Such a side has only one point, while at least two distinct point-private vertices just proved that they must both read J. This excludes the asymmetric case.

The equal-shore cases at 28 and larger cores remain open. The proved-lemma tally excludes this partial result.
