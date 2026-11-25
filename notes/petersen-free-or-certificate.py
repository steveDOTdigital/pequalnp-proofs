"""Exclude minimum signed circuits of 16 binary gates for the Petersen edge function.

Run from any directory with Python 3.9 or later. The inputs to this certificate
are the one- and two-vertex deletion bounds proved in petersen-raw-bound.md.
"""
from itertools import combinations, product

VERTICES = range(10)
PAIRS = tuple(combinations(VERTICES, 2))
EDGES = {
    (0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
}
BUDGET = 16
ALL = (1 << 1024) - 1
RAW = tuple(sum(1 << row for row in range(1024) if row >> v & 1)
            for v in VERTICES)
TARGET = 0
for a, b in EDGES:
    TARGET |= RAW[a] & RAW[b]

# Each mask selects the assignments to a restricted instance. The last entry
# is the maximum number of gates that can be eliminated by the restriction.
CUTS = [((i,), ALL ^ RAW[i], BUDGET - 14) for i in VERTICES] + [
    ((i, j), ALL ^ (RAW[i] | RAW[j]), BUDGET - (13 if (i, j) in EDGES else 12))
    for i, j in PAIRS
]
SENSITIVE = tuple((ALL ^ raw) & (TARGET ^ (TARGET >> (1 << i)))
                  for i, raw in enumerate(RAW))


def automorphisms(partial=()):
    if len(partial) == 10:
        yield partial
        return
    v = len(partial)
    for w in VERTICES:
        if w in partial:
            continue
        if all(((i, v) in EDGES) == (tuple(sorted((j, w))) in EDGES)
               for i, j in enumerate(partial)):
            yield from automorphisms(partial + (w,))


def repeated_profiles():
    group = list(automorphisms())
    assert len(group) == 120
    for pair, orbit in [((0, 1), EDGES), ((0, 2), set(PAIRS) - EDGES)]:
        assert {tuple(sorted((perm[pair[0]], perm[pair[1]]))) for perm in group} == orbit
    stabilizer = [perm for perm in group if {perm[0], perm[2]} == {0, 2}]
    assert len(stabilizer) == 4

    covered = set()
    for mask in range(1024):
        if mask in covered or (mask & 5) != 5:
            continue
        if any(mask >> a & mask >> b & 1 for a, b in EDGES):
            continue
        orbit = {sum(1 << perm[v] for v in VERTICES if mask >> v & 1)
                 for perm in stabilizer}
        covered.update(orbit)
        yield mask, len(orbit)


def within_restriction_budgets(values, left):
    for pins, mask, cap in CUTS:
        seen = set()
        lost = 0
        for i, table in enumerate(values):
            restricted = table & mask
            canonical = min(restricted, mask ^ restricted)
            if i >= 10 and (canonical == 0 or canonical in seen):
                lost += 1
            seen.add(canonical)
        future = sum(left[v] for v in pins)
        if len(pins) == 2:
            i, j = pins
            if (i, j) not in EDGES and left[i] and left[j]:
                # Only one OR gate can be common to the two raw inputs.
                if (RAW[i] | RAW[j]) not in values[10:]:
                    future -= 1
        if lost + future > cap:
            return False
    return True


def verify(repeated):
    quota = tuple(1 + (repeated >> v & 1) for v in VERTICES)
    levels = [0] * (BUDGET + 1)

    def walk(values, uses, consumed, needs):
        depth = len(values) - 10
        levels[depth] += 1
        if values[-1] == TARGET:
            raise AssertionError("A candidate reached the target")
        if depth == BUDGET:
            return
        for a, b in combinations(range(len(values)), 2):
            for sa, sb in product((0, 1), repeat=2):
                if not depth and (a, b, sa, sb) != (0, 2, 1, 1):
                    continue
                if b < 10 and not (quota[a] == quota[b] == 2 and sa == sb == 1):
                    continue
                if any(v < 10 and (uses[v] == quota[v] or (quota[v] == 2 and s == 0))
                       for v, s in ((a, sa), (b, sb))):
                    continue
                value = (values[a] ^ (ALL if sa else 0)) & (values[b] ^ (ALL if sb else 0))
                if value & 1:
                    value ^= ALL
                if not value or value in values:
                    continue
                counts = list(uses)
                for operand in (a, b):
                    if operand < 10:
                        counts[operand] += 1
                left = [limit - count for limit, count in zip(quota, counts)]
                needs_next = tuple(rows & ~(value ^ (value >> (1 << i)))
                                   for i, rows in enumerate(needs))
                if any(rows and not left[i] for i, rows in enumerate(needs_next)):
                    continue
                used = consumed | {a, b}
                pending = sum(i not in used for i in range(10, len(values) + 1))
                # Each remaining gate takes two inputs and produces one wire.
                # Besides the exact remaining raw reads, every pending gate
                # must reach the output. One wire may be the output itself.
                if sum(left) + pending > BUDGET - depth:
                    continue
                extended = values + (value,)
                if within_restriction_budgets(extended, left):
                    walk(extended, counts, used, needs_next)

    walk(RAW, [0] * 10, set(), SENSITIVE)
    return levels


def check_target():
    # A 20-gate raw formula and a 19-gate formula with the prescribed free OR.
    # They have six centers and one occurrence of a neighbor per assigned edge.
    for row in range(1024):
        active = [bool(row >> i & 1) for i in VERTICES]
        x = active.__getitem__
        hint = x(0) or x(2)
        expected = any(x(a) and x(b) for a, b in EDGES)
        stars = ((x(1) and (hint or x(6))) or (x(3) and (x(2) or x(4) or x(8)))
                 or (x(0) and (x(4) or x(5))) or (x(7) and (x(2) or x(5) or x(9)))
                 or (x(8) and (x(5) or x(6))) or (x(9) and (x(4) or x(6))))
        assert stars == expected == bool(TARGET >> row & 1)
    # Every raw variable is independently essential for each value of any
    # other. Even when the extra hint is present, all ten raw labels are needed.
    for i in VERTICES:
        assert SENSITIVE[i] & ~((RAW[0] | RAW[2]) ^ ((RAW[0] | RAW[2]) >> (1 << i)))
        for j in VERTICES:
            if i != j:
                assert SENSITIVE[i] & RAW[j] and SENSITIVE[i] & (ALL ^ RAW[j])


if __name__ == "__main__":
    check_target()
    expected = [(5, 1, 2), (69, 1, 18), (261, 2, 6), (773, 1, 437)]
    observed = []
    for mask, orbit in repeated_profiles():
        levels = verify(mask)
        print(mask, orbit, [(i, n) for i, n in enumerate(levels) if n], flush=True)
        observed.append((mask, orbit, sum(levels)))
    assert observed == expected
