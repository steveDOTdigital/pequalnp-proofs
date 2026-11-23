"""Exhaust one assigned L-meta-904 shard, including the minimum witness size."""

import argparse

from collections import Counter
from itertools import combinations


GRAPHS = {
    0: (12, [(2, 3), (1, 4), (0, 5), (4, 6), (5, 6), (3, 7), (5, 7),
             (6, 7), (2, 8), (4, 8), (6, 8), (1, 9), (3, 9), (7, 9),
             (0, 10), (2, 10), (8, 10), (0, 11), (1, 11), (9, 11), (10, 11)]),
    1: (13, [(3, 5), (4, 5), (2, 6), (4, 6), (1, 7), (3, 7), (6, 7),
         (1, 8), (2, 8), (5, 8), (0, 9), (2, 9), (3, 9), (0, 10),
         (1, 10), (4, 10), (0, 11), (6, 11), (7, 11), (0, 12),
         (5, 12), (8, 12), (11, 12)]),
    2: (13, [(2, 4), (3, 4), (1, 5), (3, 5), (1, 6), (2, 6), (0, 7),
             (3, 7), (6, 7), (0, 8), (2, 8), (5, 8), (0, 9), (1, 9),
             (4, 9), (6, 10), (7, 10), (5, 11), (8, 11), (10, 11),
             (4, 12), (9, 12), (10, 12), (11, 12)]),
}


def candidates(vertices, edges):
    for size in range(len(vertices) + 1):
        for chosen in combinations(vertices, size):
            inside = set(chosen)
            if any(a in inside and b in inside for a, b in edges):
                continue
            outside_edges = [(a, b) for a, b in edges if a not in inside and b not in inside]
            # An outside vertex fails absorption if every edge from the
            # chosen set to it points away from the chosen set.
            tests = [[] for _ in vertices]
            for index, (a, b) in enumerate(edges):
                if a in inside:
                    tests[b].append((index, 1))
                if b in inside:
                    tests[a].append((index, 0))
            if any(not tests[a] and not tests[b] for a, b in outside_edges):
                continue
            yield size, outside_edges, tests


def scalar_minimum(vertices, edges, orientation):
    outgoing = [set() for _ in vertices]
    for j, (a, b) in enumerate(edges):
        if orientation & (1 << j):
            outgoing[a].add(b)
        else:
            outgoing[b].add(a)
    for size in range(len(vertices) + 1):
        for chosen in combinations(vertices, size):
            inside = set(chosen)
            if any(a in inside and b in inside for a, b in edges):
                continue
            bad = {a for a in vertices if a not in inside and not outgoing[a] & inside}
            if all(a not in bad or b not in bad for a, b in edges):
                return size
    return None


def main(shard):
    order, edges = GRAPHS[shard]
    vertices = range(order)
    assert len(edges) == len(set(edges)) == (21, 23, 24)[shard]
    assert all(a < b for a, b in edges)
    neighbors = [{b if a == v else a for a, b in edges if v in (a, b)} for v in vertices]
    assert all(len(left & right) <= 1 for left, right in combinations(neighbors, 2))
    sets = list(candidates(vertices, edges))
    width = 1 << 15
    full = (1 << width) - 1
    # Bit t denotes orientation base+t. For edge j a one points a→b.
    low = []
    for j in range(15):
        period = 1 << j
        mask = (full // ((1 << (2 * period)) - 1)) * (((1 << period) - 1) << period)
        low.append((full ^ mask, mask))
    histogram = Counter()
    examples = {}
    for base in range(0, 1 << len(edges), width):
        direction = low + [(0, full) if base & (1 << j) else (full, 0)
                           for j in range(15, len(edges))]
        remaining = full
        for size, outside_edges, tests in sets:
            bad = []
            for required in tests:
                bits = remaining
                for index, sign in required:
                    bits &= direction[index][sign]
                bad.append(bits)
            invalid = 0
            for a, b in outside_edges:
                invalid |= bad[a] & bad[b]
            new = remaining ^ invalid
            if new:
                histogram[size] += new.bit_count()
                examples.setdefault(size, base + (new & -new).bit_length() - 1)
            remaining = invalid
            if not remaining:
                break
        if remaining:
            first = base + (remaining & -remaining).bit_length() - 1
            assert scalar_minimum(vertices, edges, first) is None
            raise AssertionError(f"violating orientation {first}")
    assert sum(histogram.values()) == 1 << len(edges)
    assert all(scalar_minimum(vertices, edges, o) == k for k, o in examples.items())
    print("orientations by minimum independent witness size:", dict(sorted(histogram.items())))
    print("scalar-checked representatives:", dict(sorted(examples.items())))
    print("total:", sum(histogram.values()), "violators: 0")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shard", type=int, choices=sorted(GRAPHS))
    main(parser.parse_args().shard)
