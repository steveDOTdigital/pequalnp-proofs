"""Finite matching checks for two nested AND pairs on the order-three plane."""
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
import runpy


plane = runpy.run_path(str(Path(__file__).with_name("quadrangle-four-clauses.py")))
flags = plane["FLAGS"]
active = [plane["FULL"] ^ absent for absent in plane["ABSENT"]]


@lru_cache(None)
def clauses(indices):
    """Canonical disjunctions hitting all chosen flags and their negative-row masks."""
    endpoints = [(flags[i][0], 13 + flags[i][1]) for i in indices]
    masks = []
    for sides in product((0, 1), repeat=len(indices)):
        hot = 0
        for edge, side in zip(endpoints, sides):
            hot |= active[edge[side]]
        masks.append(hot)
    return tuple(masks)


def common_helper(indices):
    """Can two guarded uses of the same AND jointly accept this four-matching?"""
    for partner in range(1, 4):
        first = (indices[0], indices[partner])
        second = tuple(i for i in indices if i not in first)
        for guard1 in clauses(first):
            for guard2 in clauses(second):
                forced = []
                for edges, guard in ((first, guard1), (second, guard2)):
                    for edge in edges:
                        # Either endpoint can enter this branch's raw disjunction
                        # if no negative passing its guard contains that endpoint.
                        if all(single & guard for single in clauses((edge,))):
                            forced.append(edge)
                # Both operands of the common helper must hit every forced flag.
                choices = clauses(tuple(sorted(forced)))
                for left, right in combinations_with_replacement(choices, 2):
                    if not left & right & (guard1 | guard2):
                        return True
    return False


def main():
    symmetries = plane["group"]()
    four = Counter()
    representatives = plane["orbits"](4, symmetries)
    for edges, size in representatives:
        four[common_helper(edges)] += size
    assert len(representatives) == 39 and four == {False: 120627}

    # A product with at most five clauses cannot contain three complete stars.
    witnessed_centers = [set(), set()]
    for edges, size in plane["orbits"](3, symmetries):
        if len(plane["matching_covers"](edges)) <= 5:
            continue
        for perm in symmetries:
            image = [flags[perm[e]] for e in edges]
            for shore, witnessed in enumerate(witnessed_centers):
                witnessed.add(tuple(sorted(flag[shore] for flag in image)))
    assert all(len(witnessed) == 286 for witnessed in witnessed_centers)
    print("39 orbits, 120627 four-matchings, 0 feasible shared-helper matchings")
    print("All 286 point triples and 286 line triples contain a matching needing six or more clauses")


if __name__ == "__main__":
    main()
