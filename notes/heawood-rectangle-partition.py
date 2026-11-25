"""Check the rectangle bounds for the 58 columns of Heawood case 3005.

Requires Python 3 and the project's Lean toolchain (for its CaDiCaL binary).
Run with no arguments from any directory.
"""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
import subprocess

RAW = (95229015649943559, 63038587666488, 256462815680, 4292497062759936,
       8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
       155696362464477250, 218994303132270608, 183565875465490436,
       229736628138025984, 270286071508633728, 288160007407550752)
rows = [tuple(v for v, word in enumerate(RAW) if word & (1 << j)) for j in range(58)]
edges, negatives = rows[:21], rows[21:]
full = (1 << len(edges)) - 1
edge_bits = [(1 << x) | (1 << y) for x, y in edges]
incident = [tuple(i for i, edge in enumerate(edges) if v in edge) for v in range(14)]
blocks = [(v, group) for v, flags in enumerate(incident) for n in range(1, 4)
          for group in combinations(flags, n)]


def check_geometry():
    independent = {s for s in range(1 << 14) if all(s & b != b for b in edge_bits)}
    maximal = {s for s in independent if all(s | (1 << v) not in independent
               for v in range(14) if not s & (1 << v))}
    assert maximal == {sum(1 << v for v in col) for col in negatives}
    assert len(set(rows)) == 58 and all(len(group) == 3 for group in incident)
    # Derive automorphisms from the input; verify the orbit representatives
    # used for singleton and pair tests, including projective duality.
    pencils = [frozenset(v for v, w in edges if w == y) for y in range(7, 14)]
    neighbors = [frozenset(w for x, w in edges if x == v) for v in range(7)]
    autos = []
    for perm in permutations(range(7)):
        for swap in (False, True):
            points = tuple(v + 7 if swap else v for v in perm)
            available = neighbors if swap else pencils
            images = [frozenset(points[v] for v in line) for line in pencils]
            if all(target in available for target in images):
                lines = tuple(available.index(target) + (0 if swap else 7) for target in images)
                autos.append(points + lines)
    assert len(autos) == 336
    assert {a[0] for a in autos} == set(range(14))
    pair_orbits = [{tuple(sorted((a[0], a[y]))) for a in autos} for y in (1, 7, 9)]
    assert set.union(*pair_orbits) == set(combinations(range(14), 2))


class CNF:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def var(self):
        self.n += 1
        return self.n

    def at_most(self, inputs, limit):
        # Each prefix counter is forced when that prefix reaches its threshold.
        prev = []
        for i, x in enumerate(inputs):
            current = [self.var() for _ in range(min(i + 1, limit))]
            self.clauses.append([-x, current[0]] if current else [-x])
            for j, v in enumerate(prev):
                self.clauses.append([-v, current[j]])
                self.clauses.append([-x, -v] + ([current[j+1]] if j+1 < limit else []))
            prev = current


def partition(budget, columns, control=False):
    f = CNF()
    used = [f.var() for _ in blocks]
    f.at_most(used, budget)
    if control:
        for z, (v, group) in zip(used, blocks):
            pick = len(group) == (3 if v < 7 else 1)
            f.clauses.append([z if pick else -z])
    witnesses = []
    for t, col in enumerate(negatives):
        if not columns & (1 << t):
            continue
        cover = [[] for _ in edges]
        witness = []
        for i, (v, group) in enumerate(blocks):
            if v in col:
                continue
            y = f.var()
            f.clauses.append([-y, used[i]])
            witness.append((i, y))
            for e in group:
                cover[e].append(y)
        for options in cover:
            f.clauses.append(options)
            f.clauses.extend([-a, -b] for a, b in combinations(options, 2))
        witnesses.append(witness)
    dimacs = f'p cnf {f.n} {len(f.clauses)}\n' + ''.join(
        ' '.join(map(str, clause)) + ' 0\n' for clause in f.clauses)
    root = Path(__file__).resolve().parent.parent / 'lean'
    exe = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip()) / 'bin/cadical'
    res = subprocess.run([str(exe), '-q', '--check', '--checkproof=2', '-t', '90'],
                         input=dimacs, capture_output=True, text=True, timeout=105)
    if res.returncode == 20:
        assert 's UNSATISFIABLE' in res.stdout
        return False
    assert res.returncode == 10, (res.returncode, res.stderr, res.stdout[:160])
    model = {int(s) for line in res.stdout.splitlines() if line.startswith('v ')
             for s in line.split()[1:] if int(s) > 0}
    enabled = {i for i, z in enumerate(used) if z in model}
    assert len(enabled) <= budget
    for witness in witnesses:
        picks = [i for i, y in witness if y in model]
        assert all(i in enabled for i in picks)
        assert sorted(e for i in picks for e in blocks[i][1]) == list(range(21))
    return True


@lru_cache(maxsize=None)
def price(mask):
    """Edges plus maximum matching size, equal to edges plus minimum cover."""
    lines = [[] for _ in range(7)]
    for i, (x, y) in enumerate(edges):
        if mask & (1 << i):
            lines[x].append(y)
    mate = {}

    def augment(x, seen):
        for y in lines[x]:
            if y in seen:
                continue
            seen.add(y)
            if y not in mate or augment(mate[y], seen):
                mate[y] = x
                return True
        return False

    return bin(mask).count('1') + sum(augment(x, set()) for x in range(7))


@lru_cache(maxsize=3500)
def tree_values(leaves):
    """All packed signatures on this exact multiset, including repeated leaves."""
    if len(leaves) == 1:
        return frozenset([RAW[leaves[0]]])
    values = set()
    for split in range(1, (1 << len(leaves)) - 1, 2):
        a = tuple(v for j, v in enumerate(leaves) if split & (1 << j))
        b = tuple(v for j, v in enumerate(leaves) if not split & (1 << j))
        for x in tree_values(a):
            for y in tree_values(b):
                values.update((x & y, x | y))
    return frozenset(values)


def singleton_masks(g):
    c = RAW[0]
    signatures = set()
    for leaves in combinations_with_replacement(range(1, 14), g):
        support = set(leaves)
        possible = sum(1 << i for i, (x, y) in enumerate(edges) if x in support and y in support)
        # The caller treats helpers with two singleton inputs separately.
        # All residual hot flags away from c must have both ends in support.
        if price(possible) <= g or price(full & ~(possible | c)) > 25 - g:
            continue
        for h in tree_values(leaves):
            H = c | h
            hot = H & full
            if h >> 21 == 0 or price(hot & ~c) <= g or price(full & ~hot) > 25 - g:
                continue
            signatures.add(H)
    return {H >> 21 for H in signatures if all((v >> 21) & ~(H >> 21) for v in RAW[1:])}


def read_once_checks():
    """A normalized read-once helper is a union of disjoint component products."""
    star_masks = [sum(1 << i for i in flags) for flags in incident]
    columns = [sum(1 << v for v in col) for col in negatives]
    by_first = [[] for _ in range(14)]
    for vertices in range(1, 1 << 14):
        first = vertices & -vertices
        reached = first
        while True:
            larger = reached
            for edge in edge_bits:
                if edge & reached and edge & vertices == edge:
                    larger |= edge
            if larger == reached:
                break
            reached = larger
        if reached != vertices or reached == first:
            continue
        flags = sum(1 << i for i, edge in enumerate(edge_bits) if edge & vertices == edge)
        warm = sum(1 << j for j, col in enumerate(columns)
                   if col & vertices & 127 and col & vertices & ~127)
        by_first[first.bit_length() - 1].append((vertices, flags, warm))
    assert sum(map(len, by_first)) == 5755
    masks = {g: set() for g in range(7, 14)}
    signatures = set()

    def visit(unused, vertices, flags, warm):
        g = bin(vertices).count('1') - 1
        if g >= 7 and warm and all((v >> 21) & ~warm for v in RAW):
            cold_price = price(full & ~flags)
            # Isolated vertices are outside the cold-row lower bound. Every
            # vertex missing from a warm maximal independent column is forced.
            extra = sum(1 for v, star in enumerate(star_masks)
                        if not star & ~flags and warm & ~(RAW[v] >> 21))
            if cold_price + extra <= 25 - g:
                masks[g].add(warm)
                signatures.add((g, flags, warm))
        while unused:
            low = unused & -unused
            for group, group_flags, group_warm in by_first[low.bit_length() - 1]:
                if group & unused == group:
                    visit(unused & ~group, vertices | group,
                          flags | group_flags, warm | group_warm)
            unused ^= low

    visit((1 << 14) - 1, 0, 0, 0)
    assert len(signatures) == 420
    for g, expected in zip(range(7, 14), (21, 84, 21, 21, 84, 0, 0)):
        minimal = []
        for warm in sorted(masks[g], key=lambda w: bin(w).count('1')):
            if all(other & ~warm for other in minimal):
                minimal.append(warm)
        assert len(minimal) == expected
        assert all(not partition(25 - g, warm) for warm in minimal)
        print(f'Read-once helper, {g} gates: {expected} minimal warm masks excluded.')


def main():
    check_geometry()
    all_columns = (1 << 37) - 1
    assert partition(28, all_columns, control=True)
    assert not partition(27, all_columns)
    for v in (1, 7, 9):
        assert not partition(24, (RAW[0] | RAW[v]) >> 21)
    singleton = RAW[0] >> 21
    assert partition(19, singleton) and not partition(18, singleton)
    for t in range(37):
        if not singleton & (1 << t):
            assert not partition(19, singleton | (1 << t))
    for g, expected in enumerate((0, 0, 0, 24, 114, 0), start=1):
        masks = singleton_masks(g)
        if g == 6:
            masks = {n for n in masks if n == singleton}
        assert len(masks) == expected
        assert all(not partition(25 - g, n) for n in sorted(masks))
        print(f'Helper with a true singleton, {g} inner gates: {len(masks)} residual masks excluded.')
    for g, expected in enumerate((27, 26, 24, 23, 21, 20), start=1):
        lower = min(price(full & ~sum(1 << i for i, (x, y) in enumerate(edges)
                                       if x in support and y in support))
                    for support in combinations(range(14), g + 1))
        assert lower == expected and lower > 25 - g
    for size, bound in ((7, 20), (8, 18)):
        cheapest = min(price(full & ~sum(1 << i for i, (x, y) in enumerate(edges)
                           if x in support and y in support))
                       for support in combinations(range(14), size))
        assert cheapest == bound and cheapest > 25 - size
    read_once_checks()
    print('Formula optimum, singleton helpers, read-once helpers and all helpers up to eight gates verified.')


if __name__ == '__main__':
    main()
