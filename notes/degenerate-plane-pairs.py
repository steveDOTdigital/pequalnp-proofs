"""Transfer the 2+2 pure-pair test to the degenerate negatives of L-meta-1684.

Only layouts whose two point pairs share a point p and whose two line pairs
share a line w can need a new conflict test. That test can only occur on pw.
The flag-transitive group reduces the extra calculation to the flag (0,0).
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy

folder = Path(__file__).parent
old = runpy.run_path(str(folder / "plane-shared-or-check.py"))
plane = runpy.run_path(str(folder / "shared-pencil-search.py"))
flags = old["FLAGS_SET"]
lines, pencils = old["LINES"], old["NEIGH"]
indices = range(13)


def identify_planes():
    cyclic = tuple(frozenset(ls) for ls in plane["LINES"])
    new_pencils = tuple(frozenset(w for w in indices if p in cyclic[w]) for p in indices)
    source = (pencils, lines)
    target = (new_pencils, cyclic)

    def intersect(system, side, a, b):
        common, = system[side][a] & system[side][b]
        return common

    def frame(system):
        return next(q for q in combinations(indices, 4)
                    if all(intersect(system, 0, a, b) != intersect(system, 0, b, c)
                           for a, b, c in combinations(q, 3)))

    maps = [dict(zip(frame(source), frame(target))), {}]
    while sum(map(len, maps)) < 26:
        before = sum(map(len, maps))
        for side in (0, 1):
            for a, b in combinations(sorted(maps[side]), 2):
                u = intersect(source, side, a, b)
                v = intersect(target, side, maps[side][a], maps[side][b])
                assert maps[1-side].setdefault(u, v) == v
        assert sum(map(len, maps)) > before
    assert all(set(m.values()) == set(indices) for m in maps)
    assert {(maps[0][p], maps[1][w]) for p, w in flags} == {
        (p, w) for w in indices for p in cyclic[w]}
    return tuple(tuple(m[i] for i in indices) for m in maps)


def degenerate(points, selected_lines):
    return any(points <= line for line in lines) or any(selected_lines <= pen for pen in pencils)


def price(point_pairs, line_pairs):
    pp = [set() for _ in indices]
    ww = [set() for _ in indices]
    for pairs, table in ((point_pairs, pp), (line_pairs, ww)):
        for x, y in pairs:
            table[x].add(y)
            table[y].add(x)
    keep = frozenset((p, w) for p, w in flags if
                     lines[w].isdisjoint(pp[p]) and pencils[p].isdisjoint(ww[w]))
    bad = set()
    for p, w in keep:
        if not pp[p] and not ww[w]:
            continue
        conflict = False
        for a in lines[w] - {p}:
            if (a, w) not in keep:
                continue
            for b in pencils[p] - {w}:
                if (p, b) not in keep:
                    continue
                ap, bl = pp[p] | {a}, ww[w] | {b}
                if any(not lines[v].isdisjoint(ap) for v in bl) or not degenerate(ap, bl):
                    conflict = True
                    break
            if conflict:
                bad.add((p, w))
                break
    bp, bw = {p for p, _ in bad}, {w for _, w in bad}
    removed = frozenset((p, w) for p, w in flags if (p, w) not in keep or p in bp or w in bw)
    matching = old["matching"](removed)
    return len(keep) + len(bp) + len(bw) - len(bad) + matching + 12 - 1


def main():
    mp, mw = identify_planes()
    group = old["collineations"]()
    assert {(g[0], h[0]) for g, h in group} == flags
    stabilizer = [(g, h) for g, h in group if g[0] == h[0] == 0]
    pairs = tuple(combinations(range(1, 13), 2))
    remain = {(a, b) for a in pairs for b in pairs}
    bounds = Counter()
    representatives = 0
    while remain:
        a, b = min(remain)
        orbit = {(tuple(sorted(g[v] for v in a)), tuple(sorted(h[w] for w in b)))
                 for g, h in stabilizer}
        assert orbit <= remain
        remain -= orbit
        value = price([(0, p) for p in a], [(0, w) for w in b])
        bounds[value] += len(orbit)
        representatives += 1
    assert sum(bounds.values()) == len(pairs) ** 2
    print("Point relabeling:", mp, "line relabeling:", mw)
    print("Fixed-flag orbits:", representatives, "certified gate bounds:", sorted(bounds.items()))
    assert min(bounds) >= 64


if __name__ == "__main__":
    main()
