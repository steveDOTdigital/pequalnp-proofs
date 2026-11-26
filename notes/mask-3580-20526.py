"""Exact nine-gate monotone optimum for L-meta-20526; Python standard library."""
from functools import lru_cache

TARGET = 3580
RAW = tuple(
    sum(1 << cell for cell in range(15)
        if pin in (cell // 5, 3 + cell % 5))
    for pin in range(8)
)


def formula_possible(leaves, budget):
    """Keep each truth table at its minimum formula size."""
    seen = set(leaves)
    if TARGET in seen:
        return True
    levels = [seen.copy()]
    for size in range(1, budget + 1):
        new = set()
        for left_cost in range((size - 1) // 2 + 1):
            for left in levels[left_cost]:
                for right in levels[size - 1 - left_cost]:
                    meet, join = left & right, left | right
                    if TARGET in (meet, join):
                        return True
                    if size < budget:
                        new.update((meet, join))
        levels.append(new - seen)
        seen.update(new)
    return False


@lru_cache(None)
def read_once(support):
    if support.bit_count() == 1:
        return {RAW[support.bit_length() - 1]}
    tables = set()
    left = (support - 1) & support
    while left:
        right = support ^ left
        if left < right:
            for a in read_once(left):
                for b in read_once(right):
                    tables.update((a & b, a | b))
        left = (left - 1) & support
    return tables


def feasible(inputs):
    # Every accepted cell must have some feature absent from each rejected cell.
    return all(any((w >> i) & 1 and not ((w >> j) & 1) for w in inputs)
               for i in range(15) if (TARGET >> i) & 1
               for j in range(15) if not ((TARGET >> j) & 1))


def verify():
    r0, r1, r2, c0, c1, c2, c3, c4 = RAW
    left, middle = c0 | c1, c2 | c3
    witness = ((r1 | r2) & left) | ((r0 | r1) & middle) | (r0 & c4)
    assert witness == TARGET
    for pin in range(8):
        assert not feasible(RAW[:pin] + RAW[pin+1:])
    assert not formula_possible(RAW, 8)
    considered = survivors = 0
    for mask in range(1, 255):
        k = mask.bit_count()
        if k < 2:
            continue
        others = tuple(w for i, w in enumerate(RAW) if not ((mask >> i) & 1))
        for helper in read_once(mask):
            considered += 1
            leaves = others + (helper,)
            if feasible(leaves):
                survivors += 1
                assert not formula_possible(leaves, 9 - k)
    assert (considered, survivors) == (36117, 10)
    print("Nine gates verified; all eight raws essential;",
          considered, "shared tables examined;", survivors, "passed monotonicity.")


if __name__ == "__main__":
    verify()
