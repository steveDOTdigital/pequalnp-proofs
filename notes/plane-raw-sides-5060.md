# Raw input sides in the 19-gate plane circuit

[L-meta-5060](https://pequalnp.com/lemma#L-meta-5060) concerns a 19-AND circuit for the order-four projective plane. Its 42 variables are the 21 points and 21 lines. An input is accepted exactly when it contains an incident point and line. The [opposite is L-meta-5061](https://pequalnp.com/lemma#L-meta-5061). The following necessary conditions leave the full claim open.

**At least 20 variables survive singleton removal.** Start with the 38 signed raw sides (the left and right variable sets at all 19 gates). Restrict all the sides to the remaining variables. Whenever a side contains only one variable, remove that variable and discard resulting empty sides. Repeat until every retained side contains at least two variables. At exactly 20, the counting conditions force ten points, ten lines, twelve mixed sides, two pure point sides and two pure line sides. The bound holds for every order of removal. In the original circuit each of the 42 variables also occurs on at least one side of size at most three.

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

The extra posted hypothesis bounding the number of gates reading either endpoint of a nonincident point-line pair was not needed. The surviving size-20 configuration describes counts; constructing or excluding circuits with those counts and larger cores remains open.
