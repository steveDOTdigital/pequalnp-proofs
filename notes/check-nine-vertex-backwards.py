"""Enumerate every five-gate reachable-side family, working from the output backwards."""

from itertools import permutations, product
from pathlib import Path
import runpy


def children(family, processed):
    # Each later gate side can contain the next gate as a parent. The gate is
    # active on the union of those sides' columns, or everywhere if an output.
    columns = [sum(1 << i for i, row in enumerate(family) if row & (1 << side))
               for side in range(2 * processed)]
    active_sets = {0}
    for column in columns:
        active_sets |= {active | column for active in active_sets}
    active_sets.add((1 << len(family)) - 1)
    for active in active_sets:
        extended = []
        for i, row in enumerate(family):
            if active & (1 << i):
                extended.extend((row | (1 << (2 * processed)), row | (2 << (2 * processed))))
            else:
                extended.append(row)
        yield tuple(sorted(extended))


def canonical(family, gates):
    # Labels with different incidence counts can be ordered immediately. Try
    # every tied order and orientation, always using an actual side permutation.
    def signature(side):
        return tuple(sum(row.bit_count() == size and bool(row & (1 << side)) for row in family)
                     for size in range(1, gates + 1))

    groups = {}
    for g in range(gates):
        a, b = 2 * g, 2 * g + 1
        left, right = signature(a), signature(b)
        if left < right:
            orientations = [(a, b)]
        elif right < left:
            orientations = [(b, a)]
        else:
            orientations = [(a, b), (b, a)]
        groups.setdefault(tuple(sorted((left, right))), []).append(orientations)
    best = None
    for blocks in product(*(permutations(groups[key]) for key in sorted(groups))):
        for pairs in product(*(options for block in blocks for options in block)):
            order = [side for pair in pairs for side in pair]
            image = tuple(sorted(sum(1 << i for i, side in enumerate(order) if row & (1 << side))
                                 for row in family))
            if best is None or image < best:
                best = image
    return best


def main():
    directory = Path(__file__).parent
    negative, _ = runpy.run_path(str(directory / "check-nine-vertex-internal-gates.py"))["defined_points"]()
    fits = runpy.run_path(str(directory / "check-nine-vertex-corners.py"))["fits"]
    families = {(0,)}
    for processed in range(5):
        raw = {child for family in families for child in children(family, processed)
               if len(child) * (1 << (4 - processed)) >= len(negative)}
        families = {canonical(family, processed + 1) for family in raw}
        print(f"{processed + 1} gates: {len(families)} families", flush=True)
    states = 0
    for family in sorted(families):
        possible, count = fits(family, negative)
        assert not possible
        states += count
    print(f"No match in {len(families)} families, {states} search states")


if __name__ == "__main__":
    main()
