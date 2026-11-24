"""Check the triangle negative tests and enumerate feasible sources for residual line circuits."""
from collections import Counter
from itertools import combinations, permutations, product
import argparse

N = 13
DIFF = {0, 1, 3, 9}
ALL = (1 << N) - 1
BLOCKS = [sum(1 << p for p in range(N) if (p - l) % N in DIFF) for l in range(N)]
PENCILS = [sum(1 << l for l, block in enumerate(BLOCKS) if block >> p & 1) for p in range(N)]


def count(s):
    return bin(s).count("1")


def bits(s):
    return [i for i in range(s.bit_length()) if s >> i & 1]


def arcs(blocks):
    return [x for x in range(ALL + 1) if all(count(x & block) <= 2 for block in blocks)]


def exterior(x, blocks):
    return sum(1 << i for i, block in enumerate(blocks) if not x & block)


def test_rows():
    points, lines = arcs(BLOCKS), arcs(PENCILS)
    tests = {(a, exterior(a, BLOCKS)) for a in points if count(a) == 3}
    tests |= {(exterior(b, PENCILS), b) for b in lines if count(b) == 3}
    legal = set()
    for a in points:
        ext = exterior(a, BLOCKS)
        legal.update((a, b) for b in lines if not b & ~ext)
    maximal = {(a, b) for a, b in legal if
               all((a | 1 << p, b) not in legal for p in bits(ALL ^ a)) and
               all((a, b | 1 << l) not in legal for l in bits(ALL ^ b))}
    assert len(legal) == 12234 and len(tests) == 468 and maximal == tests
    return sorted(tests)


def residual(lines, tests, pairing):
    lm = sum(1 << l for l in lines)
    pts = 0
    for l in lines:
        pts |= BLOCKS[l]
    masks = [(a & pts) | ((b & lm) << N) for a, b in tests]
    negatives = sorted(x for x in set(masks) if not any(x != y and not x & ~y for y in masks))
    positive = [1 << p | (1 << (N + l)) for l in lines for p in bits(BLOCKS[l])]
    raw = [1 << i for i in bits(pts)]
    helpers = []
    for l, block in enumerate(BLOCKS):
        if l in lines:
            continue
        group = bits(block & pts)
        if len(group) == 3:
            if pairing < 0:
                helpers.extend((1 << a) | (1 << b) for a, b in combinations(group, 2))
            else:
                i = pairing % 3
                pairing //= 3
                kept = [v for j, v in enumerate(group) if j != i]
                helpers.append(sum(1 << v for v in kept))
        if len(group) > 1:
            helpers.append(sum(1 << v for v in group))
    return raw, sorted(set(helpers)), positive, negatives


def source_sets(raw, helpers, positive, negative, point_cap):
    # For a point whose raw bit is omitted, find the minimal sets of helpers
    # that separate each incident positive from every negative on its own line.
    choices = []
    for p in raw:
        own = [j for j, h in enumerate(helpers) if p & h]
        restrictions = set()
        for edge in positive:
            if not edge & p:
                continue
            restrictions.update(sum(1 << j for j in own if not helpers[j] & row)
                                for row in negative if row & (edge & ~ALL))
        good = []
        for sz in range(1, len(own) + 1):
            for js in combinations(own, sz):
                m = sum(1 << j for j in js)
                if all(r & m for r in restrictions) and not any(not g & ~m for g in good):
                    good.append(m)
        choices.append(good)
    # When a point is retained, a larger source set may still use more helpers.
    # Include supersets so a column sufficient for separation can still share gates.
    result = set()
    for omitted in range(1 << len(raw)):
        keep = len(raw) - count(omitted)
        room = point_cap - keep
        options = {0}
        for j in bits(omitted):
            options = {a | b for a in options for b in choices[j] if count(a | b) <= room}
        for used in options:
            slack = room - count(used)
            more = bits(((1 << len(helpers)) - 1) ^ used)
            for k in range(min(slack, len(more)) + 1):
                for ids in combinations(more, k):
                    result.add((omitted, used | sum(1 << j for j in ids)))
    return sorted(result)



def triangle_orbits(raw, helpers, negatives, options, lines):
    # A residual automorphism permutes the three lines and their two private
    # points per line. Filter these 48 permutations on the actual negative rows.
    cells = {}
    for p in raw:
        signature = tuple(l for l in lines if BLOCKS[l] & p)
        cells.setdefault(signature, []).append(p)

    def image(x, perm):
        return sum(v for u, v in perm.items() if x & u)

    group = []
    for order in permutations(lines):
        lm = dict(zip(lines, order))
        dest = [cells[tuple(sorted(lm[l] for l in sig))] for sig in cells]
        for per in product(*(permutations(v) for v in dest)):
            perm = {1 << (N + l): 1 << (N + lm[l]) for l in lines}
            for original, mapped in zip(cells.values(), per):
                perm.update(zip(original, mapped))
            if ({image(x, perm) for x in negatives} == set(negatives) and
                    {image(x, perm) for x in helpers} == set(helpers)):
                group.append(perm)

    def move(mask, pool, perm):
        return sum(1 << pool.index(image(pool[i], perm)) for i in bits(mask))

    reps = {min((move(a, raw, g), move(b, helpers, g)) for g in group) for a,b in options}
    assert len(group) == 24 and sorted((a,b) for a,b in reps if a) == [(1,1029)]
    return reps

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--pairing", type=int, default=0)
    opt = ap.parse_args()
    tests = test_rows()
    print("12,234 allowed negatives, 468 maximal triangle/exterior tests")
    for lines in [(0, 1), (0, 1, 3), (0, 1, 5)]:
        raw, helpers, yes, no = residual(lines, tests, opt.pairing)
        # k unfinished stars normally cost 5k-1; a one-gate saving leaves at
        # most 5k-1 source wires, of which k are mandatory line indicators.
        cap = 4 * len(lines) - 1
        options = source_sets(raw, helpers, yes, no, cap)
        counts = Counter((count(o), count(h)) for o, h in options)
        print(lines, "local tests", len(yes), len(no), "source sets", sorted(counts.items()))
        if len(lines) == 2:
            assert options == [(0, 0)]
        if lines == (0,1,3) and opt.pairing < 0:
            reps = triangle_orbits(raw,helpers,no,options,lines)
            print("Triangle source sets modulo symmetry", sorted(reps))


if __name__ == "__main__":
    main()
