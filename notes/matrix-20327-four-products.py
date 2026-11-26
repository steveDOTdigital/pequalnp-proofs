"""Exact synthesis for four products of input unions on the 8-by-8 promise."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product

MASK = 11871860300395540620
ROWS = [(MASK >> (8 * i)) & 255 for i in range(8)]
FOOLING_COLUMNS = (2, 6, 0, 4, 3, 1, 7, 5)


def cells(rows, cols):
    return sum(cols << (8 * i) for i in range(8) if rows >> i & 1)


def submasks(mask):
    part = mask
    while part:
        yield part
        part = (part - 1) & mask


def maximal_rectangles():
    for rows in range(1, 256):
        cols = 255
        for i, neighbors in enumerate(ROWS):
            if rows >> i & 1:
                cols &= neighbors
        if cols and all(rows >> i & 1 or cols & ~neighbors
                        for i, neighbors in enumerate(ROWS)):
            yield rows, cols, cells(rows, cols)


def covers_of_eight(rectangles, chosen=(), covered=0):
    if covered == MASK:
        assert len(chosen) == 8
        yield tuple(sorted(chosen))
        return
    if len(chosen) == 8:
        return
    missing = MASK ^ covered
    edge = missing & -missing
    for rect in rectangles:
        if rect[2] & edge:
            yield from covers_of_eight(rectangles, chosen + (rect,), covered | rect[2])


def shrink(cover):
    # The cells unique to a maximal rectangle must stay in its smaller rectangle.
    options = []
    for index, (rows, cols, region) in enumerate(cover):
        others = 0
        for j, (_, _, bits) in enumerate(cover):
            if j != index:
                others |= bits
        required = region & ~others
        options.append([(r, c, cells(r, c)) for r in submasks(rows)
                        for c in submasks(cols) if cells(r, c) & required == required])
    for selection in product(*options):
        covered = 0
        for _, _, bits in selection:
            covered |= bits
        if covered == MASK:
            yield selection


def pairings(rects):
    if not rects:
        yield ()
        return
    r, c, _ = rects[0]
    for j, (s, d, _) in enumerate(rects[1:], 1):
        if r & s or c & d:
            continue
        operands = (r | (d << 8), s | (c << 8))
        for tail in pairings(rects[1:j] + rects[j + 1:]):
            yield (operands,) + tail


def optional_shared_masks(targets):
    shared = set()
    for a, b in combinations(targets, 2):
        shared.update(v for v in submasks(a & b) if v.bit_count() >= 2)
    return sorted(shared.difference(targets))


@lru_cache(None)
def minimum_parts(needed, available):
    if not needed:
        return 0
    first = needed & -needed
    return 1 + min(minimum_parts(needed & ~part, available)
                   for part in available if part & first)


def union_cost(targets, shared):
    built = {1 << i for i in range(16)}
    cost = 0
    for mask in sorted(set(targets).union(shared), key=lambda x: (x.bit_count(), x)):
        if mask in built:
            continue
        available = tuple(sorted(part for part in built if part & mask == part))
        cost += minimum_parts(mask, available) - 1
        built.add(mask)
    return cost


def verify():
    assert all(ROWS[i] >> j & 1 for i, j in enumerate(FOOLING_COLUMNS))
    for i, k in combinations(range(8), 2):
        assert not (ROWS[i] >> FOOLING_COLUMNS[k] & ROWS[k] >> FOOLING_COLUMNS[i] & 1)
    rectangles = tuple(maximal_rectangles())
    covers = set(covers_of_eight(rectangles))
    assert (len(rectangles), len(covers)) == (20, 6)
    families = set()
    for cover in covers:
        for selection in shrink(cover):
            for terms in pairings(selection):
                families.add(tuple(sorted({mask for term in terms for mask in term})))
    histogram = Counter()
    for targets in families:
        shared = optional_shared_masks(targets)
        histogram[min(union_cost(targets, chosen) for n in range(len(shared) + 1)
                      for chosen in combinations(shared, n))] += 1
    assert len(families) == 263
    assert dict(histogram) == {18: 6, 19: 38, 20: 93, 21: 89, 22: 31, 23: 6}
    print("Lowest gate count in the four-product class:", min(histogram) + 4 + 3)


if __name__ == "__main__":
    verify()
