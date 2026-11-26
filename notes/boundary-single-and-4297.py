"""Check the raw-set implications used for a single unsafe AND on every 3-by-3 graph."""
from collections import Counter
from itertools import combinations


def subsets(mask):
    while mask:
        yield mask
        mask = (mask - 1) & mask


def check():
    counts = Counter()
    vertices = range(6)
    bits = [1 << i for i in vertices]
    for graph in range(1, 512):
        neighbors = [0] * 6
        for i in range(3):
            for j in range(3):
                if graph & (1 << (3 * i + j)):
                    neighbors[i] |= bits[j + 3]
                    neighbors[j + 3] |= bits[i]
        if any((neighbors[i] & neighbors[j]).bit_count() > 1 for i, j in combinations(range(3), 2)):
            continue
        common = [63] * 64
        for mask in range(1, 64):
            v = (mask & -mask).bit_length() - 1
            common[mask] = common[mask & (mask - 1)] & neighbors[v]

        # T contains exactly the raw inputs t for which H AND t lies below the output.
        for first, second in combinations(range(1, 64), 2):
            if not second & ~common[first]:
                continue
            valid = 63
            for i in vertices:
                for j in vertices:
                    if first & bits[i] and second & bits[j] and not neighbors[i] & bits[j]:
                        valid &= neighbors[i] | neighbors[j]
            if not valid:
                continue
            if min(first.bit_count(), second.bit_count()) >= 2:
                p, q = first & valid, second & valid
                if not (p or q):
                    continue
                counts["two nonsingleton operands with candidate hidden leaves"] += 1
                for center, opposite in ((p, second), (q, first)):
                    if center:
                        assert center.bit_count() == 1 and not opposite & ~common[center]
                if not (p and q):
                    continue
                counts["two candidate centers"] += 1
                assert not first & second and not p & q
                for center, other, opposite in ((p, q, second), (q, p, first)):
                    for raw in subsets(valid):
                        if not raw & center or raw == center or not common[raw]:
                            continue
                        # A larger unmarked operand forces the unique alternate center.
                        assert (opposite & ~other).bit_count() == 1
                        assert common[raw] == opposite & ~other
                        counts["larger unmarked operands with a visible product"] += 1
            else:
                for b, leaves in ((first, second), (second, first)):
                    if b.bit_count() != 1 or leaves & b or not leaves & valid:
                        continue
                    counts["singleton operands with candidate hidden leaves"] += 1
                    opposite_shore = 56 if b & 7 else 7
                    if not leaves & opposite_shore & ~common[b]:
                        continue
                    assert not valid & (b | (opposite_shore & ~common[b]))
                    possible = set()
                    for raw in subsets(valid):
                        if raw & leaves and common[raw] & ~b:
                            assert raw.bit_count() == 1
                            possible.add(raw)
                    for i, j in combinations(possible, 2):
                        assert not common[i] & common[j] & ~b
                    counts["singleton case needing separate unmarked roots"] += 1
    return counts


if __name__ == "__main__":
    for name, value in check().items():
        print(name, value)
    # H asks for any vertex on each shore. Its last reader also requires a center.
    # All edges of this double star are hidden from the boundary singleton test.
    for k in (2, 3, 4, 5):
        left = (1 << k) - 1
        right = left << k
        p, q = 1, 1 << k
        for row in range(1 << (2 * k)):
            h = bool(row & left and row & right)
            output = h and bool(row & (p | q))
            wanted = bool((row & p and row & right) or (row & q and row & left))
            assert output == wanted
        print("Double star", k, "edges", 2*k-1, "visible", 0,
              "required", 2*k, "actual", 2*k+1)
