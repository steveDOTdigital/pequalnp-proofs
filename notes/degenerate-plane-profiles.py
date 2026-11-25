"""Reproduce the input poset left free by the 236 tests of L-meta-1684.

The earlier pencil search defines exactly the same cyclic plane. Import its
incidence data without writing a bytecode cache. All computations are exact.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy

plane = runpy.run_path(str(Path(__file__).with_name("shared-pencil-search.py")))
lines, pencils, exterior = (plane[k] for k in ("LINE_MASKS", "PENCILS", "disjoint"))
sizes = tuple(bin(n).count("1") for n in range(1 << 13))


def subsets(mask):
    current = mask
    while current:
        yield current
        current = (current - 1) & mask
    yield 0


def contained(a, b):
    return a & ~b == 0


def check():
    # Every incidence-free pair consists of P and a subset of its exterior.
    negatives = set()
    independent = []
    for points in range(1 << 13):
        available = exterior(points, lines)
        if exterior(available, pencils) == points:
            if (any(contained(points, w) for w in lines)
                    or any(contained(available, p) for p in pencils)):
                negatives.add((points, available))
        independent.extend((points, selected) for selected in subsets(available))

    def shapes(pairs):
        return Counter((sizes[a], sizes[b]) for a, b in pairs)

    expected = {(0, 13): 1, (13, 0): 1, (1, 9): 13, (9, 1): 13,
                (2, 6): 78, (6, 2): 78, (3, 3): 52}
    assert shapes(negatives) == expected
    below_tests = {(a, b) for p, w in negatives for a in subsets(p) for b in subsets(w)}
    free = set(independent) - below_tests
    assert shapes(free) == {(3, 3): 936, (3, 4): 234, (4, 3): 234}
    assert all(any(contained(a, w) for w in lines) or any(contained(b, p) for p in pencils)
               for a, b in below_tests)
    assert all(not any(contained(a, w) for w in lines) and
               not any(contained(b, p) for p in pencils) for a, b in free)

    maxima = {(a, b) for a, b in free if sizes[a] + sizes[b] == 7}
    rows = free - maxima
    degrees = Counter()
    edges = set()
    for a, b in rows:
        left, right = (a, exterior(a, lines)), (exterior(b, pencils), b)
        assert left in maxima and right in maxima
        assert all(v == left or v == right for v in maxima
                   if contained(a, v[0]) and contained(b, v[1]))
        edges.add((left, right))
        degrees.update((left, right))
    assert len(edges) == len(rows) and set(degrees.values()) == {4}

    # Any two distinct left triangles have at most one common right triangle.
    # This gives cycle information about correlations between optional truth values.
    neighborhoods = {left: set() for left, _ in edges}
    for left, right in edges:
        neighborhoods[left].add(right)
    overlap = Counter(len(a & b) for a, b in combinations(neighborhoods.values(), 2))
    assert overlap == {0: 25857, 1: 1404}
    print("Independent inputs:", len(independent))
    print("Maximal desk negatives:", len(negatives), sorted(shapes(negatives).items()))
    print("Forced false:", len(below_tests), "forced true:", (1 << 26) - len(independent))
    print("Free:", sorted(shapes(free).items()), "left neighborhood overlaps:", sorted(overlap.items()))
    return neighborhoods


if __name__ == "__main__":
    check()
