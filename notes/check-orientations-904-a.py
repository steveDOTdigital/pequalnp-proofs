"""Exhaust L-meta-904 shard 1, including the minimum witness size."""

from collections import Counter
from itertools import combinations


EDGES = [(3, 5), (4, 5), (2, 6), (4, 6), (1, 7), (3, 7), (6, 7),
         (1, 8), (2, 8), (5, 8), (0, 9), (2, 9), (3, 9), (0, 10),
         (1, 10), (4, 10), (0, 11), (6, 11), (7, 11), (0, 12),
         (5, 12), (8, 12), (11, 12)]
VERTICES = range(13)


def candidates():
    for size in range(14):
        for chosen in combinations(VERTICES, size):
            inside = set(chosen)
            if any(a in inside and b in inside for a, b in EDGES):
                continue
            outside_edges = [(a, b) for a, b in EDGES if a not in inside and b not in inside]
            # An outside vertex fails absorption if every edge from the
            # chosen set to it points away from the chosen set.
            tests = [[] for _ in VERTICES]
            for index, (a, b) in enumerate(EDGES):
                if a in inside:
                    tests[b].append((index, 1))
                if b in inside:
                    tests[a].append((index, 0))
            if any(not tests[a] and not tests[b] for a, b in outside_edges):
                continue
            yield size, outside_edges, tests


def scalar_minimum(orientation):
    outgoing = [set() for _ in VERTICES]
    for j, (a, b) in enumerate(EDGES):
        if orientation & (1 << j):
            outgoing[a].add(b)
        else:
            outgoing[b].add(a)
    for size in range(14):
        for chosen in combinations(VERTICES, size):
            inside = set(chosen)
            if any(a in inside and b in inside for a, b in EDGES):
                continue
            bad = {a for a in VERTICES if a not in inside and not outgoing[a] & inside}
            if all(a not in bad or b not in bad for a, b in EDGES):
                return size
    return None


def main():
    assert len(EDGES) == len(set(EDGES)) == 23
    assert all(a < b for a, b in EDGES)
    neighbors = [{b if a == v else a for a, b in EDGES if v in (a, b)} for v in VERTICES]
    assert all(len(left & right) <= 1 for left, right in combinations(neighbors, 2))
    sets = list(candidates())
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
    for base in range(0, 1 << len(EDGES), width):
        direction = low + [(0, full) if base & (1 << j) else (full, 0)
                           for j in range(15, len(EDGES))]
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
            assert scalar_minimum(first) is None
            raise AssertionError(f"violating orientation {first}")
    assert sum(histogram.values()) == 1 << len(EDGES)
    assert all(scalar_minimum(o) == k for k, o in examples.items())
    print("orientations by minimum independent witness size:", dict(sorted(histogram.items())))
    print("scalar-checked representatives:", dict(sorted(examples.items())))
    print("total:", sum(histogram.values()), "violators: 0")


if __name__ == "__main__":
    main()
