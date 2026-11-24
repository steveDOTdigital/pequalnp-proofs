"""Exact finite core check in the proof that Heawood needs seven AND gates.

Uses only the Python standard library. The input labels are the desk's L-meta-2278 labels.
"""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import runpy


graph = runpy.run_path(str(Path(__file__).with_name("heawood-first-gate-bound.py")))
EDGES = set(graph["EDGES"])
POINTS, LINES = frozenset(range(7)), frozenset(range(7, 14))
VERTICES = POINTS | LINES


def near(v):
    return frozenset(b if a == v else a for a, b in EDGES if v in (a, b))


def maximal_false(fixed):
    remaining = sorted(VERTICES - fixed)
    false_rows = set()
    for mask in range(1 << len(remaining)):
        row = fixed | frozenset(v for i, v in enumerate(remaining) if mask >> i & 1)
        if all(a not in row or b not in row for a, b in EDGES):
            false_rows.add(row)
    return {s for s in false_rows if all(s | {v} not in false_rows for v in VERTICES - s)}


def partitions(s):
    # The least member goes in the first group, so unordered partitions occur once.
    for trio in combinations(sorted(s), 3):
        if min(s) in trio:
            yield frozenset(trio), s - frozenset(trio)


def pairings(ids):
    if not ids:
        yield ()
        return
    for j in range(1, len(ids)):
        for rest in pairings(ids[1:j] + ids[j+1:]):
            yield ((ids[0], ids[j]),) + rest


def configurations():
    # The mixed partner of p is forced by the other two members of its point group.
    for omitted in POINTS:
        chosen = POINTS - {omitted}
        for ps in partitions(chosen):
            mate = {}
            for triple in ps:
                for p in triple:
                    a, b = triple - {p}
                    line, = near(a) & near(b)
                    mate[p] = line
            used = frozenset(mate.values())
            if len(used) != 6:
                continue
            for ls in partitions(used):
                if any(not (group - {mate[p]}) <= near(p) for group in ls
                       for p in chosen if mate[p] in group):
                    continue
                features = [frozenset({p, mate[p]}) for p in sorted(chosen)] + list(ps) + list(ls)
                yield features, {(p, l) for p, l in EDGES if p in chosen and l in used}


def maximum_generated(features, core_edges):
    # For a true edge row, the first paid gate to become true must have the
    # two raw endpoints in its opposite raw-input features.
    edges = sorted(core_edges)
    masks = {(i,j):sum(1 << k for k, (p,l) in enumerate(edges)
                       if (p in features[i] and l in features[j])
                       or (l in features[i] and p in features[j]))
             for i, j in combinations(range(len(features)), 2)}
    best = total = 0
    for pairs in pairings(tuple(range(len(features)))):
        covered = 0
        for a, b in pairs:
            covered |= masks[a, b]
        best = max(best, bin(covered).count("1"))
        total += 1
    assert total == 945
    return best


def main():
    assert len(EDGES) == 21 and all(len(near(v)) == 3 for v in VERTICES)
    assert all(len(near(u) & near(v)) == 1 for side in (POINTS, LINES)
               for u, v in combinations(side, 2))
    full = maximal_false(frozenset())
    assert len(full) == 37
    assert all(len(maximal_false(frozenset({v}))) == 12 for v in VERTICES)
    # Test the separation property used in the peeling proof directly.
    for v in VERTICES:
        for a in VERTICES - {v}:
            for b in VERTICES - {v}:
                if b not in near(a):
                    assert any({a,b} <= I and v not in I and near(v) & I for I in full)
    layouts = list(configurations())
    canonical = [frozenset(s) for s in ((1,12),(2,7),(3,13),(4,9),(5,11),(6,10),
                                         (1,2,3),(4,5,6),(7,12,13),(9,10,11))]
    # Independent check: all surviving layouts are images of this one under a
    # permutation of points taking each line to a line.
    line_by_points = {near(l): l for l in LINES}
    orbit = set()
    collineations = 0
    for perm in permutations(sorted(POINTS)):
        images = dict(enumerate(perm))
        for l in LINES:
            image = frozenset(perm[p] for p in near(l))
            if image not in line_by_points:
                break
            images[l] = line_by_points[image]
        else:
            collineations += 1
            orbit.add(frozenset(frozenset(images[v] for v in f) for f in canonical))
    assert collineations == 168
    assert orbit == {frozenset(fs) for fs, _ in layouts}
    small = {(1,7),(1,9),(1,13),(5,12)}
    assert maximum_generated(canonical, small) == 3
    counts = Counter((len(es), maximum_generated(fs, es)) for fs, es in layouts)
    assert counts == {(16,14): 42}
    print("37 maximal false rows; 12 on each of the 14 one-input-true restrictions.")
    print("42 surviving port configurations, 945 pairings each; at most 14 of 16 core edges generated.")
    print("Every six-AND circuit is excluded; seven ordinary point stars attain the bound with free ORs.")


if __name__ == "__main__":
    main()
