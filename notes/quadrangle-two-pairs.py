"""Finite matching checks for two nested AND pairs on the order-three plane."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, product
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


def dual_star_checks():
    """Check the two orientation-sensitive steps of the ten-developed-star bound."""
    lines = plane["LINES"]
    quadrangles = plane["QUADS"]
    negative = [(points, {i for i, line in enumerate(lines) if points.isdisjoint(line)})
                for points in quadrangles]
    checked = 0
    for center in range(13):
        off = [i for i, line in enumerate(lines) if center not in line]
        for size in range(1, 4):
            for subset in combinations(off, size):
                extends = any(center in points and set(subset) <= misses
                              for points, misses in negative)
                concurrent = set.intersection(*(set(lines[i]) for i in subset))
                assert extends == (size < 3 or not concurrent)
                checked += 1

    cores = runpy.run_path(str(Path(__file__).with_name("quadrangle-star-cores.py")))
    original = cores["profiles"]()
    # Both functions use this private runpy namespace; swap shores only there.
    namespace = cores["profiles"].__globals__
    namespace["LINES"] = [{i for i, line in enumerate(lines) if p in line} for p in range(13)]
    namespace["QUADS"] = [(misses, points) for points, misses in negative]
    dual = cores["profiles"]()
    for (yes, no), frames in dual.items():
        assert any(yes == old_yes and
                   all(any(row & target == row for target in no) for row in old_no)
                   for old_yes, old_no in original)
    assert sorted(dual.values()) == [234, 468, 936]
    return checked


def check_exceptional_term(symmetries):
    """Count ordinary centers using the cheapest possible wires into the exceptional term."""
    stars = [{i for i, (p, line) in enumerate(flags) if vertex in (p, line + 13)}
             for vertex in range(26)]
    remaining = set()
    for first, second in combinations(stars, 2):
        edges = sorted(first | second)
        for size in range(3, len(edges) + 1):
            remaining.update(combinations(edges, size))

    def free_wires(exclusive):
        vertices = {v for i in exclusive for v in (flags[i][0], flags[i][1] + 13)}
        options = {1 << v for v in vertices}
        for vertex, star in enumerate(stars):
            support = 0
            for i in star.difference(exclusive):
                point, line = flags[i]
                neighbor = line + 13 if point == vertex else point
                if neighbor in vertices:
                    support |= 1 << neighbor
            subset = support
            while subset:
                options.add(subset)
                subset = (subset - 1) & support
        return sum(1 << v for v in vertices), tuple(sorted(options))

    def can_separate(exclusive, options, budget):
        constraints = set()
        for edge in exclusive:
            point, line = flags[edge]
            positive = (1 << point) | (1 << (line + 13))
            for negative in plane["ROWS"]:
                constraints.add(sum(1 << k for k, wire in enumerate(options)
                                    if wire & positive and not wire & negative))
        minimal = tuple(sorted((s for s in constraints
                                if not any(t != s and t & s == t for t in constraints)),
                               key=int.bit_count))

        @lru_cache(None)
        def choose(left, count):
            if not left:
                return True
            if not count:
                return False
            candidates = left[0]
            while candidates:
                wire = candidates & -candidates
                candidates -= wire
                if choose(tuple(x for x in left if not x & wire), count - 1):
                    return True
            return False

        return choose(minimal, budget)

    critical = Counter()
    while remaining:
        edges = min(remaining)
        orbit = {tuple(sorted(perm[i] for i in edges)) for perm in symmetries}
        assert orbit <= remaining
        remaining -= orbit
        vertices, options = free_wires(edges)

        @lru_cache(None)
        def min_sources(left):
            if not left:
                return 0
            first = left & -left
            return 1 + min(min_sources(left & ~wire) for wire in options if wire & first)

        # A hypothetical 63-gate circuit with 14 ordinary centers gives this budget.
        budget = 63 - (52 - len(edges)) - 14
        if budget >= 3 and min_sources(vertices) <= budget + 1:
            critical[len(edges), budget + 1] += len(orbit)
            assert not can_separate(edges, options, budget + 1)
    assert critical == {(6, 4): 156, (8, 6): 156}

    # A cover of at most fifteen vertices contains a whole shore.
    for size in range(1, 14):
        for points in combinations(range(13), size):
            misses = sum(line.isdisjoint(points) for line in plane["LINES"])
            assert not misses or size + misses <= 10
    print("14-center exclusions: 156 six-flag families and 156 eight-flag families")


def main():
    print("Dual ten-star extension checks:", dual_star_checks(), "with all 1638 core frames covered")
    symmetries = plane["group"]()
    check_exceptional_term(symmetries)
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
