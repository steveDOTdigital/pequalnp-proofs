"""Exact enumeration of level spaces invariant under both cyclic shifts in 4 by 5."""

from functools import lru_cache
from itertools import combinations_with_replacement


@lru_cache(None)
def injection_sum(order, frequencies):
    """Sum a product of characters over distinct indices, using integer arithmetic."""
    if not frequencies:
        return 1
    last = frequencies[-1]
    others = frequencies[:-1]
    # Start with an unrestricted last index. Its character sums to zero
    # unless trivial. Remove its disjoint collisions with the earlier indices.
    total = order * injection_sum(order, others) if last == 0 else 0
    for index, previous in enumerate(others):
        combined = others[:index] + ((previous + last) % order,) + others[index + 1:]
        total -= injection_sum(order, tuple(sorted(combined)))
    return total


def obstruction_masks():
    bad = set()
    for degree in range(1, 5):
        for modes in combinations_with_replacement(range(20), degree):
            rows = tuple(sorted(mode // 5 for mode in modes))
            columns = tuple(sorted(mode % 5 for mode in modes))
            if injection_sum(4, rows) and injection_sum(5, columns):
                bad.add(sum(1 << mode for mode in set(modes)))
    minimal = []
    for mask in sorted(bad, key=lambda item: bin(item).count("1")):
        if not any((mask & old) == old for old in minimal):
            minimal.append(mask)
    return minimal


def main():
    forbidden = obstruction_masks()
    levels = [0]
    counts = []
    for dimension in range(1, 21):
        next_level = []
        for space in levels:
            for mode in range(space.bit_length(), 20):
                candidate = space | (1 << mode)
                if not any((candidate & bad) == bad for bad in forbidden):
                    next_level.append(candidate)
        print(dimension, len(next_level))
        counts.append(len(next_level))
        levels = next_level
        if not levels:
            break
    assert counts == [16, 76, 80, 16, 0]


if __name__ == "__main__":
    main()
