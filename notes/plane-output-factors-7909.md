# Omitted inputs in the AND-output projective-plane bound

[L-meta-7909](https://data.pequalnp.com/data/lemma/L-meta-7909.b627f8822689.json) asks for the gate lower bound in orders q at least 400 with a final AND. This note holds at every projective-plane order q at least 2. It gives a constraint on the factors of the final conjunction. The gate bound in the assigned statement remains open.

Let F accept every incident pair and reject incidence-free inputs with at most q lines selected. For a set T of at most q lines, define Z(T) by taking the lines in T and the points outside their union. As in the [forced-clause argument](https://github.com/steveDOTdigital/pequalnp-proofs/blob/68ef7a064453145d25127e53cb6d8c4fec65c61f/notes/plane-forced-clauses.md), the pivotal zeros of Z(T) are exactly its zero coordinates, namely the points in the union of T and the lines outside T. For a point, an incident line in T witnesses acceptance after the flip. For a line outside T, at most q of its q+1 points are covered by T, since two lines share at most one point. An uncovered point witnesses acceptance after the flip. Acceptance uses monotonicity from that incident pair, even when the flipped input has q+1 lines active.

## At least q+2 factors if every factor omits a variable

Write F as the conjunction of k Boolean factors. For each factor that is independent of at least one raw input, choose one such input. If every factor omits an input, let P and L be the sets of chosen point and line variables. A set T of at most q lines with T disjoint from L and with its union covering P would make every chosen input pivotal at Z(T). Each factor would then accept Z(T), since it accepts the input with its own omitted pivotal coordinate flipped and cannot distinguish the two inputs. The conjunction would accept Z(T), a contradiction.

If |P|+|L| is at most q+1, such a T always exists. If P is empty, take T empty. If |P| is at most q and P is nonempty, at most q lines are forbidden. Every point has q+1 lines through it, so one allowed line per point suffices. If |P| is q+1, no line is forbidden and one line covers a pair of points, leaving at most q−1 further lines to choose. Thus if k is at most q+1, some factor depends on all 2N raw inputs. In particular, one of the actual two operands at the desk's AND output depends on every raw input. Its own cone has at least 2N−1 binary gates.

There is also an exact condition at the threshold. If |P|+|L|=q+2, T fails to exist only when the omitted set forms a full star: one point and all its lines, or one line and all its points.

- With one point and q+1 forbidden lines, failure means precisely that every line through the point is forbidden.
- With q+1 points and one forbidden line, failure means precisely that the points all lie on that line. Otherwise some joining line is allowed and the remaining q−1 points can be covered separately.
- With q+2 points and no forbidden lines, pair four distinct points and use the two joining lines. The other q−2 points take at most one line each.
- In all other cases, there are no points or at most q points and q forbidden lines, as above.

The bound on the number of factors is sharp for the exact edge function E, which is a valid completion of the desk tests. For each variable u in a full star, take the cofactor E with u set to one. On a true input all these cofactors are true. At a false input, if a star variable is already one, its cofactor is false. If the entire star is zero, setting the star centre to one cannot create an incident pair, so that cofactor is false. The product of the q+2 cofactors therefore equals E.

The remaining circuit problem is to turn this dependence statement into a gate bound that grows as Nq. An operand can depend on every input with only a linear number of gates, and the two cones can share gates.

## Finite replay

This verifies the omission-set classification for the planes of orders two and three.

```python
from itertools import combinations, product

def plane(q):
    triples = [
        u for u in product(range(q), repeat=3)
        if next((a for a in u if a), 0) == 1
    ]
    n = len(triples)
    assert n == q*q + q + 1
    lines = [
        sum(1 << i for i, p in enumerate(triples) if sum(a*b for a,b in zip(p,l)) % q == 0)
        for l in triples
    ]
    return n, lines

for q in (2, 3):
    n, lines = plane(q)
    masks = [1 << i for i in range(2*n)]
    full_lines = (1 << n) - 1
    clauses = []
    for k in range(q+1):
        for t in combinations(range(n), k):
            p, ell = 0, 0
            for j in t:
                p |= lines[j]
                ell |= 1 << j
            clauses.append(p | ((full_lines ^ ell) << n))
    stars = {
        (1 << (n+j)) | points for j,points in enumerate(lines)
    } | {
        (1 << i) | sum(1 << (n+j) for j,points in enumerate(lines) if (points >> i) & 1)
        for i in range(n)
    }
    for k in (q+1,q+2):
        sets = (sum(c) for c in combinations(masks,k))
        uncovered = {s for s in sets if not any(s & ~m == 0 for m in clauses)}
        assert uncovered == (stars if k == q+2 else set())
        print(f'q={q}, omission size={k}, sets missed by every forced clause={len(uncovered)}')

```
