"""Check the four Petersen cofactors and the eight-gate lower bound with Python 3."""
from functools import lru_cache
from itertools import combinations


EDGES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
         (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5))
FREE = (1, 3, 4, 5, 6, 7, 8)


def masks(width):
    return range(1 << width)


def projection(row, columns):
    return sum(((row >> wire) & 1) << i for i, wire in enumerate(columns))


def embed(row, columns):
    return sum(((row >> i) & 1) << wire for i, wire in enumerate(columns))


def partitions(columns):
    """Unordered splits with both sides nonempty."""
    for size in range(1, len(columns)):
        for left in combinations(columns, size):
            if columns[0] in left:
                yield left, tuple(v for v in columns if v not in left)


def table(f):
    return tuple(bool(f(x)) for x in masks(7))


def target(row):
    return any((row >> u) & (row >> v) & 1 for u, v in EDGES)


def formulas(row):
    x1, x3, x4, x5, x6, x7, x8 = (bool(row & (1 << i)) for i in range(7))
    return (
        (x3 and (x4 or x8)) or (x5 and (x7 or x8)) or (x6 and (x1 or x8)),
        x1 or x4 or x5 or (x8 and (x3 or x6)),
        x1 or x3 or x7 or (x8 and (x5 or x6)),
        x1 or x3 or x4 or x5 or x7 or (x6 and x8),
    )


def support(values, width):
    return tuple(i for i in range(width)
                 if any(values[x] != values[x ^ (1 << i)] for x in masks(width)))


def factors(values, left, right, absorbing):
    """For AND use the rows equal to one, for OR the rows equal to zero.

    Two factors on disjoint inputs exist exactly when those rows are a rectangle.
    On a nonconstant slice, projecting the rectangle determines both factors.
    """
    selected = [x for x, value in enumerate(values) if value != absorbing]
    if not selected:
        return None
    a = {projection(x, left) for x in selected}
    b = {projection(x, right) for x in selected}
    if len(a) * len(b) != len(selected):
        return None
    return (tuple((x in a) != absorbing for x in masks(len(left))),
            tuple((x in b) != absorbing for x in masks(len(right))))


@lru_cache(None)
def read_once(values):
    """Allow arbitrary signed leaves. De Morgan pushes every NOT to a leaf."""
    width = len(values).bit_length() - 1
    essential = support(values, width)
    if len(essential) < 2:
        return True
    if len(essential) < width:
        return read_once(tuple(values[embed(x, essential)] for x in masks(len(essential))))
    for left, right in partitions(essential):
        for absorbing in (False, True):
            pair = factors(values, left, right, absorbing)
            if pair is not None and all(read_once(f) for f in pair):
                return True
    return False


def check_internal_fanout(values):
    """A subtree feeding a single shared bit has at most two distinct cofactors."""
    columns = tuple(range(7))
    tested = 0
    for size in range(2, 7):
        for block in combinations(columns, size):
            outside = tuple(v for v in columns if v not in block)
            outside_rows = [embed(y, outside) for y in masks(len(outside))]
            distinct = {tuple(values[embed(x, block) | row] for row in outside_rows)
                        for x in masks(size)}
            assert len(distinct) >= 3, block
            tested += 1
    return tested


def check_shared_raw(values):
    """Both branches of the root can read the same source r once each."""
    tested = 0
    for r in range(7):
        other = tuple(i for i in range(7) if i != r)
        slices = [tuple(values[embed(x, other) | (bit << r)] for x in masks(6))
                  for bit in (0, 1)]
        assert all(len(set(s)) == 2 for s in slices)
        for left, right in partitions(tuple(range(6))):
            for absorbing in (False, True):
                tested += 1
                pairs = [factors(s, left, right, absorbing) for s in slices]
                if any(p is None for p in pairs):
                    continue
                # Append r as the highest bit in each branch's truth table.
                branches = [pairs[0][i] + pairs[1][i] for i in (0, 1)]
                assert not all(read_once(f) for f in branches), (r, left, right)
    return tested


def main():
    costs = (8, 5, 5, 6)
    supports = []
    for index, (u, v) in enumerate(((0, 0), (1, 0), (0, 1), (1, 1))):
        values = table(lambda x: target(embed(x, FREE) | u | (v << 2)))
        assert values == table(lambda x: formulas(x)[index])
        supports.append(len(support(values, 7)))
        if index == 0:
            assert not read_once(values)
            print("Proper blocks excluded:", check_internal_fanout(values))
            print("Root splits with one shared raw input excluded:", check_shared_raw(values))
        else:
            assert supports[-1] - 1 == costs[index]
    assert supports == [7, 6, 6, 7]
    print("All 512 Petersen rows agree. Binary gate minima (00, 10, 01, 11):", costs)


if __name__ == "__main__":
    main()
