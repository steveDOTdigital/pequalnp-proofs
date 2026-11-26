# How much sharing can save a gate on the punctured plane?

[L-meta-9741](https://pequalnp.com/lemma#L-meta-9741) asks for a 62-gate binary monotone circuit. The graph has thirteen points and thirteen lines. Point p is adjacent to lines p + {0,4,10,12} modulo 13, with the single flag (0,0) removed. Its opposite is [L-meta-9742](https://pequalnp.com/lemma#L-meta-9742). Neither direction is settled here.

## A sharp 63-gate bound under restricted sharing

Each point contributes one AND of that point with the OR of its neighboring lines. These thirteen terms cost 51 gates in total. Twelve more ORs combine them. A positive input contains a flag, and an input containing no flag makes every term false.

The graph contains no four-cycle. The shift p ↦ p+4 gives a perfect matching, so the minimum cover has size 13. Apply the [two-shore physical-leaf count](plane-pair-sharing-3773.md#arbitrarily-many-raw-pairs-on-both-shores) with 51 flags and cover size 13. It gives s+1 ≥ 64 whenever every shared wire is safe, inactive on the flags, or an OR of two raw inputs on one shore. Safe means that a true wire implies a positive output. Both shores may have arbitrarily many such pairs.

Another class with the same sharp bound has a single shared intermediate of the form (OR P) AND (OR L), with arbitrary nonempty sets of points P and lines L. The [three comparison menus and extra-row test](plane-pair-sharing-3773.md#one-shared-point-by-line-rectangle) apply without a regularity assumption. We checked all 67,092,481 supports. Exactly 5,627 needed the extra-row test and all reached 63. To replay with [the full-plane script](plane-pair-sharing-3773.py), drop (0,0) from flags, rebuild ROWS, NEIGH and LINES from the remaining flags, and take only collineations fixing point 0 and line 0. The group has 108 elements and gives 239 orbits of nonempty point sets. Negate line indices to recover the desk coordinates. In single_shared_rectangle use 51 for the flag count and 63 for the target. Retain all line subsets for every point representative and weight each by its point orbit size.

A single shared disjunction is also insufficient, regardless of width. For a pure shore use the [one-shore bound](plane-pair-sharing-3773.md#a-single-shared-disjunction-of-any-width). For a mixed disjunction delete flags at which the helper is active and its canonical comparison cross is cold. If D is the deleted set and U its endpoints, the physical suffix leaf count A is at least 51−|D|+|U|+ν(E outside U), where ν is the matching number. With d producer inputs and r ≥ 2 suffix reads the gate count is at least A+d+r−2. The same 239-orbit replay in single_mixed_disjunction, replacing 52 by 51 and 64 by 63, leaves just the following cases.

| Smaller side | Larger side | Gate lower bound | Number of supports |
| ---: | ---: | ---: | ---: |
| 1 | 2 | 62 | 54 |
| 1 | 3 | 61 | 252 |
| 1 | 3 | 62 | 60 |
| 1 | 4 | 61 | 6 |
| 1 | 4 | 62 | 252 |
| 2 | 3 | 62 | 18 |

For the singleton cases expand that singleton once per read, leaving the larger side virtual. For a larger side of size b, at most b flags are lost, so A+r ≥ 64−b. This gives s ≥ 63. In the last row a 62-gate witness would need exactly two reads. Expand the two-element side at both reads, leaving the triple virtual. At most three flags are lost, so A+4 ≥ 61. Equality is necessary since s ≥ A+5. It forces three deletions and a minimum enlarged cover containing a damaged vertex on the two-element shore, by the [extra-row cover proof](plane-pair-sharing-3773.md#recovering-the-cover-cost-on-deleted-flags). Every size-thirteen cover of this graph is an entire shore. Indeed, each nonempty proper point subset has strictly more neighbors than points, a condition checked below. All retained diagonals therefore report the two-element shore. At least 48 physical leaves on the opposite shore are required. Every vertex on the two-element shore has a charged leaf because all thirteen are charged in the tight cover. Both labels of the expanded pair occur twice on that shore, so at least 15 leaves are needed there. This exceeds the alleged 61 in total.

## A sole shared signal which rejects all singletons

Let B be the flags on which the shared signal H turns on. Trim its private producer by fixing inputs outside the endpoint set T of B low, in that producer alone. This preserves every positive flag and can only decrease the circuit on negative inputs. A constant or unshared result reduces to the formula case. Each of the d surviving endpoint variables is essential, because its flag turns H on and the other endpoint alone does not. Write t for the producer gate count and r for the suffix reads. On retained flags E minus B the rank comparisons cannot report H. The suffix thus has at least |E minus B|+ν(E minus B) physical raw leaves. Its other leaves are the r occurrences of H. Therefore

    s ≥ |E minus B| + ν(E minus B) + d + (t−d+1) + (r−2).

Both parenthesized terms are nonnegative. For any candidate support T one may first take B to be the entire induced edge set. Removing any edge from B increases the bound by at least one. Exhausting all supports of size at most nine leaves only the following at a bound below 63. Each attains exactly 62 before the last two terms.

| Contributing vertices | Induced edges | Supports |
| ---: | ---: | ---: |
| 8 | 9 | 18 |
| 9 | 9 | 108 |
| 9 | 10 | 1,188 |

At 62 all induced edges must turn on H, r=2 and t=d−1. Its trimmed producer is read-once. An OR at the root of a read-once cold formula splits its edge hits into disjoint variable sets. At an AND root the two endpoints of every hit must lie in different children and must make those children true singly. Every remaining variable contributes, hence both children are disjunctions. Splitting the two cross-shore orientations of each resulting product gives vertex-disjoint rectangles. This retains all flag hits, only decreases the helper on independent inputs, and costs at most d−1 gates. A rectangle can likewise be split along connected components of its induced incidence graph.

A rectangle containing only genuine incidences is safe. Remove it from the producer's OR and add it to the final output by one OR instead. This preserves the output on all flags and all independent sets. A single remaining unsafe rectangle has already been excluded. If two remain, each requires at least four vertices, since a connected one-sided star is safe. With at most nine vertices total each has at most five. In a graph of girth at least six both incidence subgraphs are forests, hence B has at most d−2 incidences, contradicting every remaining row of the table. No 62-gate witness can therefore have a sole cold shared signal with at most nine contributing vertices.

The finite part of this last calculation can be reproduced directly with the following Python, from the directory containing the linked full-plane scripts. The orbit reduction is optional and does not change the matching calculation.

```python
from collections import Counter
from pathlib import Path
import runpy

plane = runpy.run_path(str(Path("plane-shared-or-check.py")))
vertices = range(13)
edges = {(p, (-l) % 13) for p, l in plane["FLAGS"]} - {(0, 0)}
assert edges == {(p, (p+k) % 13) for p in vertices for k in (0, 4, 10, 12)} - {(0, 0)}
neighbors = [sum(1 << l for q, l in edges if q == p) for p in vertices]
group = [p for p, l in plane["collineations"]() if p[0] == l[0] == 0]
assert len(group) == 108

def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask -= low

def matching(rows):
    owner = {}
    def augment(p, visited):
        for l in bits(rows[p]):
            if l in visited:
                continue
            visited.add(l)
            if l not in owner or augment(owner[l], visited):
                owner[l] = p
                return True
        return False
    return sum(augment(p, set()) for p in vertices)

neighbors_of = [0] * 8192
for points in range(1, 8192):
    low = points & -points
    neighbors_of[points] = neighbors_of[points-low] | neighbors[low.bit_length()-1]
    assert points == 8191 or neighbors_of[points].bit_count() > points.bit_count()
seen = set()
counts = Counter()
orbits = 0
for points in range(1, 8192):
    if points in seen:
        continue
    orbit = {sum(1 << perm[p] for p in bits(points)) for perm in group}
    seen.update(orbit)
    orbits += 1
    for lines in range(1, 8192):
        width = points.bit_count() + lines.bit_count()
        if width > 9:
            continue
        kept = tuple(row & ~lines if points & (1 << p) else row
                     for p, row in enumerate(neighbors))
        remaining = sum(row.bit_count() for row in kept)
        # Three perfect matchings give inexpensive lower bounds.
        diagonal = max(sum(bool(row & (1 << ((p+k) % 13))) for p, row in enumerate(kept))
                       for k in (4, 10, 12))
        if width + remaining + diagonal >= 63:
            continue
        bound = width + remaining + matching(kept)
        if bound < 63:
            assert bound == 62
            counts[width, 51-remaining] += len(orbit)
assert len(seen) == 8191 and orbits == 239
assert counts == {(8, 9): 18, (9, 9): 108, (9, 10): 1188}
```

Helpers which accept singletons require a different argument. For example, the same comparison tests excluded all 9,702 choices of one hot singleton and a disjoint two-by-two rectangle whose incidences form a four-vertex path. Adding a second hot singleton left 19,350 supports unresolved by those tests. Circuits with several interacting shared intermediates also remain open. This is partial progress on the desk statement and adds zero to the independent lemma tally.
