"""Verify the 28-leaf signed-formula lower bound for PEqualNP case 9754.

Run with Python 3.8 or later. See heawood-signed-formulas.md for the proof
that every formula induces one of the profiles checked here.
"""
from functools import lru_cache
from itertools import combinations, permutations, product

PENCILS = ((7, 8, 10), (7, 9, 13), (8, 12, 13), (7, 11, 12),
           (10, 11, 13), (9, 10, 12), (8, 9, 11))
EDGES = [(p, l) for p, lines in enumerate(PENCILS) for l in lines]
BITS = [(1 << p) | (1 << l) for p, l in EDGES]
INCIDENT = [[i for i, edge in enumerate(EDGES) if v in edge] for v in range(14)]
ALL = (1 << 14) - 1
POINTS = (1 << 7) - 1
LINES = ALL ^ POINTS


def vertices(mask):
    return [v for v in range(14) if mask & (1 << v)]


def automorphisms():
    points_at = [frozenset(p for p, l in EDGES if l == v) for v in range(7, 14)]
    lines_at = [frozenset(lines) for lines in PENCILS]
    maps = []
    for perm in permutations(range(7)):
        for swap in (False, True):
            image = tuple(v + 7 if swap else v for v in perm)
            choices = lines_at if swap else points_at
            pencils = [frozenset(image[p] for p in s) for s in points_at]
            if all(s in choices for s in pencils):
                g = image + tuple(choices.index(s) + (0 if swap else 7) for s in pencils)
                assert set(g) == set(range(14))
                assert {sum(1 << g[v] for v in edge) for edge in EDGES} == set(BITS)
                maps.append(g)
    assert len(set(maps)) == 336
    return maps


@lru_cache(None)
def local_masks(reads, clean):
    """Minimal sets of locally dominated rows, numbered 0, 1, 2."""
    if reads >= 3:
        return (0,)  # Allow independent row labels; no forced domination.
    found = set()
    clean_rows = [i for i in range(3) if clean & (1 << i)]
    for incidence in product(range(1, 1 << reads), repeat=3):
        # The column of all clean neighbors must report v exactly once on
        # every clean row. A bit in incidence[i] is a positive occurrence.
        if not any(all(bin(incidence[i] & active).count("1") == 1 for i in clean_rows)
                   for active in range(1 << reads)):
            continue
        dominated = sum(1 << i for i in range(3)
                        if any(j != i and incidence[j] & ~incidence[i] == 0
                               for j in clean_rows))
        found.add(dominated)
    return tuple(d for d in found if not any(a != d and a & ~d == 0 for a in found))


def compatible(bad, reads):
    choices = []
    for v, rows in enumerate(INCIDENT):
        clean = sum(1 << i for i, e in enumerate(rows) if not BITS[e] & bad & ~(1 << v))
        options = local_masks(reads[v], clean)
        choices.append([sum(1 << e for i, e in enumerate(rows) if d & (1 << i))
                        for d in options])
    choices.sort(key=len)

    def assign(i, occupied):
        if i == len(choices):
            return True
        return any(not occupied & new and assign(i+1, occupied | new) for new in choices[i])
    return assign(0, 0)


def survivors(bad, independent, budget):
    for single in independent:
        if single & bad:
            continue
        reads = [1 if single & (1 << v) else 2 for v in range(14)]
        spare = budget - len(vertices(bad)) - sum(reads)
        if spare < 0:
            continue
        # A larger read allowance only relaxes the mask test. Three reads
        # already allow arbitrary behavior on all three incident rows.
        eligible = [v for v in range(14) if reads[v] == 2]
        for extra in combinations(eligible, min(spare, len(eligible))):
            allowed = [r + (v in extra) for v, r in enumerate(reads)]
            if compatible(bad, allowed):
                yield single, allowed


def main():
    assert len(set(BITS)) == 21 and all(len(rows) == 3 for rows in INCIDENT)
    assert all(len(set(PENCILS[a]) & set(PENCILS[b])) == 1 for a, b in combinations(range(7), 2))
    independent = [s for s in range(1 << 14) if all(e & s != e for e in BITS)]
    maps = automorphisms()
    # Each mixed variable needs two positive and one negative occurrence.
    candidates = {b for b in range(1 << 14) if 14 + 2*len(vertices(b)) <= 27}
    seen = set()
    borderline = []
    orbits = 0
    for bad in sorted(candidates):
        if bad in seen:
            continue
        orbit = {sum(1 << g[v] for v in vertices(bad)) for g in maps}
        assert not seen & orbit
        seen.update(orbit)
        orbits += 1
        for single, allowed in survivors(bad, independent, 27):
            borderline.append((bad, single, allowed))
    assert seen == candidates
    assert borderline == [(63, LINES, [2]*7 + [1]*7)]
    # Every line occurs once, so its private point-only filter contains
    # three positive point occurrences, distinct across the seven lines.
    assert 3*7 > sum(borderline[0][2][:7])
    assert compatible(0, [1]*7 + [3]*7)  # The 28-leaf ordinary star formula.
    print(f"{len(seen)} mixed sets, {orbits} orbits, {len(independent)} independent single sets.")
    print("One local profile survived; private filters require 21 positive point leaves, with 14 available.")
    print("No 27-leaf signed formula; the 28-leaf positive control passed.")


if __name__ == "__main__":
    main()
