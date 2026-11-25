"""Check the one-point/multiple-line cases of the shared-helper bound."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy
import subprocess

folder = Path(__file__).parent
g = runpy.run_path(str(folder / "shared-pencil-search.py"))
points, pencils = g["LINE_MASKS"], g["PENCILS"]
E = frozenset((p, w) for p in range(13) for w in range(13) if (points[w] >> p) & 1)


def witnesses(point_support, line_support):
    slots = []
    for a in range(13):
        if pencils[a] & line_support != line_support:
            continue
        for b in range(13):
            if (points[b] & point_support != point_support) or (a, b) in E:
                continue
            for p, w in E:
                if (p, b) in E and (a, w) in E:
                    slots.append(((p, w), (p, b), (a, w)))
    return tuple(slots)


def bound(slots, point_support, line_support, raw_cost, extra=0, omit=frozenset()):
    def possible(pair):
        p, w = pair
        return (point_support >> p) & 1 or (line_support >> w) & 1 or (
            (extra >> p) & 1 and (extra >> (w+13)) & 1)
    bad = {e for e, u, v in slots if e not in omit and u not in omit and v not in omit
           and (possible(u) or possible(v))}
    ps, ws = {p for p, w in bad}, {w for p, w in bad}
    owner = {}

    def augment(p, seen):
        for w in range(13):
            if w in ws or w in seen or (p, w) not in E or (p, w) in omit:
                continue
            seen.add(w)
            if w not in owner or augment(owner[w], seen):
                owner[w] = p
                return True
        return False

    for p in set(range(13)) - ps:
        augment(p, set())
    return len(E) - len(omit) + len(ps) + len(ws) - len(bad) + len(owner) + raw_cost


def find_bound(slots, p, w, cost, extra=0):
    score = bound(slots, p, w, cost, extra)
    if score >= 64:
        return score
    # Dropping rows whose domination implication is expensive can improve the
    # lower bound. Every trial gives a valid certificate on its surviving rows.
    possible = sorted({row for triple in slots for row in triple})
    for count in (1, 2):
        for omitted in combinations(possible, count):
            score = max(score, bound(slots, p, w, cost, extra, frozenset(omitted)))
            if score >= 64:
                return score
    return score


def main():
    for k in range(1, 5):
        values = Counter()
        for subset in combinations(range(13), k):
            lines = sum(1 << w for w in subset)
            entries = witnesses(1, lines)
            values[find_bound(entries, 1, lines, k+1)] += 1
        print("One point and", k, "lines:", sorted(values.items()))
        assert min(values) >= 64


def profile_certificate(pmask, wmask, entries, cost, available, profile, solver):
    # Relax each vertex to its possible four-row leaf containment profiles.
    cnf = profile["CNF"]()
    arcs = profile["arcs"]
    compare = {}
    extra = []
    neighbors = [tuple(w+13 for w in range(13) if (p,w) in E) for p in range(13)]
    neighbors += [tuple(p for p in range(13) if (p,w) in E) for w in range(13)]
    for v, adjacent in enumerate(neighbors):
        bits = [cnf.var() for _ in range(3)]
        extra.extend(bits)
        select = []
        for i, j in arcs:
            compare[v, adjacent[i], adjacent[j]] = cnf.var()
        for r in range(1, 5):
            for pattern in profile["profiles"](r):
                choice = cnf.var()
                select.append(choice)
                cnf.clauses.extend([-choice, bit] for bit in bits[:r-1])
                for n, (i, j) in enumerate(arcs):
                    if pattern & (1 << n):
                        cnf.clauses.append([-choice, compare[v, adjacent[i], adjacent[j]]])
        cnf.clauses.append(select)
    def hot(row):
        i, j = row
        m = (1 << i) | (1 << (j+13))
        return bool((pmask | (wmask << 13)) & m) or available & m == m
    danger = {(e,u,v) for e,u,v in entries if hot(u) or hot(v)}
    for p, w in E:
        for b in neighbors[p]:
            for a in neighbors[w+13]:
                if a == p or b == w+13:
                    continue
                if ((p,w),(p,b-13),(a,w)) not in danger:
                    cnf.clauses.append([-compare[p,b,w+13], -compare[w+13,a,p]])
    profile["at_most"](cnf, extra, 63-cost-26)
    result = subprocess.run([solver,'-q','--check','--checkproof=2','-t','45'],
                            input=cnf.text(),capture_output=True,text=True)
    return result.returncode == 20


def certify_extra(pmask, wmask, entries, verified_cost=None):
    size = lambda x: bin(x).count("1")
    support = pmask | (wmask << 13)
    # Only variables appearing in a witness row can cause further failures.
    relevant = Counter()
    for _, a, b in entries:
        for p, w in (a, b):
            if pmask & (1 << p) or wmask & (1 << w):
                continue
            relevant[p] += 1
            relevant[w+13] += 1
    order = sorted(relevant, key=lambda i: (-relevant[i], i))
    active = sum(1 << i for i in order)
    nodes = 0

    def visit(pos, present, undecided):
        nonlocal nodes
        nodes += 1
        cost = size(support | present)
        # Allow all undecided inputs to create conflicts at zero additional
        # cost. Success here certifies every completion of this branch.
        available = support | present | undecided
        if verified_cost is not None and cost >= verified_cost:
            return True
        if bound(entries, pmask, wmask, cost, available) >= 64:
            return True
        if pos == len(order):
            return find_bound(entries, pmask, wmask, cost, available) >= 64
        bit = 1 << order[pos]
        return visit(pos+1, present, undecided ^ bit) and visit(pos+1, present | bit, undecided ^ bit)

    return visit(0, 0, active), nodes


def extra_orbits():
    shared = runpy.run_path(str(folder / "plane-shared-or-check.py"))
    ident = runpy.run_path(str(folder / "degenerate-plane-pairs.py"))["identify_planes"]
    point_map, line_map = ident()
    stabilizer = [tuple(line_map[h[line_map.index(i)]] for i in range(13))
                  for gs, h in shared["collineations"]() if point_map[gs[point_map.index(0)]] == 0]
    profile = runpy.run_path(str(folder / "plane-shared-profiles.py"))
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=folder.parent/"lean", text=True)
    solver = Path(prefix.strip()) / "bin/cadical"
    for k in (1, 2, 3, 4):
        remaining = set(combinations(range(13), k))
        while remaining:
            a = min(remaining)
            orbit = {tuple(sorted(h[w] for w in a)) for h in stabilizer}
            assert orbit <= remaining
            remaining -= orbit
            wm = sum(1 << w for w in a)
            entries = witnesses(1, wm)
            threshold = None
            if k == 1:
                # Let every potential row activate H. Nine paid raw slots
                # leave at most 54 raw slots in the proof trees.
                assert profile_certificate(1, wm, entries, 9, (1<<26)-1, profile, solver)
                threshold = 9
            passed, count = certify_extra(1, wm, entries, threshold)
            assert passed
            print("Including extra flags:", k, a, len(orbit), passed, count, flush=True)


def restore_ninth(pmask, wmask, base, cols):
    hot = {(p,w) for p,w in E if (pmask >> p) & (wmask >> w) & 1}
    assert len(hot) == 10 and len(base) == 42
    vertices = {next(iter(hot))[0]}
    while True:
        following = vertices | {w+13 for p,w in hot if p in vertices}
        following |= {p for p,w in hot if w+13 in following}
        if following == vertices:
            break
        vertices = following
    assert len(vertices) == 9
    def has(p, w, pointson, lineson):
        return any((not (a >> p & 1)) and (not (b >> w & 1)) and a & pointson == pointson
                   and b & lineson == lineson and (a & pmask and b & wmask)
                   for a,b in cols)
    for e in sorted(hot):
        live = base | {e}
        pe, we = e
        # The only formerly omitted row allowed to use the helper is e.
        # All other rows retain their original proof tree or singleton-cold H.
        atp = sum(1 << w for p,w in live if p==pe)
        atw = sum(1 << p for p,w in live if w==we)
        if not any((a & pmask) and (b & wmask) and b&atp==atp for a,b in cols):continue
        if not any((a & pmask) and (b & wmask) and a&atw==atw for a,b in cols):continue
        valid=True
        for p,w in live:
            for u,b in live:
                if u!=p or b==w:continue
                for a,v in live:
                    if v!=w or a==p or e not in ((p,b),(a,w)):continue
                    if not has(p,w,1<<a,1<<b):
                        valid=False
                        break
                if not valid:break
            if not valid:break
        if valid:return True
    return False


def singleton_free():
    # The possible hot flags of a singleton-free helper lie in the graph on
    # its private raw labels. Enumerate every point set up to size six, then
    # all line sets within the total budget. Interchange shores for the rest.
    from math import comb
    old = runpy.run_path(str(folder / "plane-shared-or-check.py"))
    point_maps = [g for g, _ in old["collineations"]()]
    sizes = [bin(x).count("1") for x in range(8192)]
    exterior, contained = g["disjoint"], g["contained"]
    columns = []
    for pts in range(8192):
        ls = exterior(pts, points)
        if exterior(ls, pencils) == pts and (contained(pts, points) or contained(ls, pencils)):
            columns.append((pts, ls))
    assert len(columns) == 236
    repairs = 0
    unresolved = Counter()
    covered = Counter()
    for k in range(7):
        remain = set(combinations(range(13), k))
        while remain:
            seed = min(remain)
            orbit = {tuple(sorted(m[p] for p in seed)) for m in point_maps}
            assert orbit <= remain
            remain -= orbit
            pmask = sum(1 << p for p in seed)
            degree = [sizes[ls & pmask] for ls in points]
            for wmask, k2 in enumerate(sizes):
                n = k + k2
                if k2 < k or n > 12:
                    continue
                mult = len(orbit) * (1 if k == k2 else 2)
                covered[n] += mult
                t = sum(d for w, d in enumerate(degree) if (wmask >> w) & 1)
                if t + t // 4 <= n + 1:
                    continue
                match = {}
                def aug(p, seen):
                    for w in range(13):
                        if (p,w) not in E or w in seen or (pmask >> p & wmask >> w & 1):
                            continue
                        seen.add(w)
                        if w not in match or aug(match[w],seen):
                            match[w] = p
                            return True
                    return False
                for p in range(13):
                    aug(p,set())
                if 52-t+len(match)+n < 64:
                    if n == 9:
                        assert len(match) == 12
                        base = {(p,w) for p,w in E if not (pmask >> p & wmask >> w & 1)}
                        assert restore_ninth(pmask, wmask, base, columns)
                        repairs += mult
                    else:
                        unresolved[n] += mult
    assert all(covered[n] == comb(26,n) for n in range(13))
    assert repairs == 936 and all(unresolved[n] == 0 for n in range(10))
    print("Nine-input restorations:", repairs)
    print("Singleton-free support. Size, total, unresolved by this bound:")
    for n in range(13):
        print(n, covered[n], unresolved[n])



if __name__ == "__main__":
    main()
    extra_orbits()
    singleton_free()
