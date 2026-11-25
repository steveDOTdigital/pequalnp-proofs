# Raw input sides in the 19-gate plane circuit

[L-meta-5060](https://pequalnp.com/lemma#L-meta-5060) concerns a 19-AND circuit for the order-four projective plane. Its 42 variables are the 21 points and 21 lines. An input is accepted exactly when it contains an incident point and line. The [opposite is L-meta-5061](https://pequalnp.com/lemma#L-meta-5061). The following necessary conditions leave the full claim open.

**At least 18 variables survive singleton removal.** Start with the 38 signed raw sides (the left and right variable sets at all 19 gates). Restrict all the sides to the remaining variables. Whenever a side contains only one variable, remove that variable and discard resulting empty sides. Repeat until every retained side contains at least two variables. The bound holds for every order of removal. In the original circuit each of the 42 variables also occurs on at least one side of size at most three.

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

Let p,l be the two shore sizes, M the mixed-side count and A,B the pure-side counts. We have M ≥ max(p,l), A,B ≥ 1 and M+A+B ≤ p+l−4. There are at most M−p+A remaining point labels, and at most M−l+B remaining line labels. Applying the preceding inequalities on both shores leaves no possibilities with fewer than 18 vertices. This short Python replay verifies the integer count and lists all surviving configurations at 18; the order is points, lines, mixed sides, pure point sides, pure line sides, up to exchanging shores.

```python
def allowed(k, mixed, pure):
    labels = mixed - k + pure
    if labels <= 1 and k > 3:
        return False
    if labels <= 2 and k > 6:
        return False
    return pure != 1 or k < 7 or mixed >= k + (k + 2) // 3

survivors = []
for p in range(1, 19):
    for l in range(1, p + 1):
        if p + l > 18:
            continue
        for mixed in range(p, p + l - 5):
            for a in range(1, p + l - 4 - mixed):
                for b in range(1, p + l - 3 - mixed - a):
                    if allowed(p, mixed, a) and allowed(l, mixed, b):
                        survivors.append((p, l, mixed, a, b))
assert sorted(survivors) == [(9, 9, 10, 2, 2), (9, 9, 12, 1, 1),
                             (10, 8, 11, 2, 1)]
```

The extra posted hypothesis about the union of gates reading a nonincident point and line was not needed for this bound. The three configurations at 18 pass only the displayed counting conditions; no circuit realizing any of them is known here.
