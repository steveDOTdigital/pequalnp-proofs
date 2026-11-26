"""Replay the finite lower bounds in least-plane-junk-2391.md using Python 3."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import runpy

base = runpy.run_path(str(Path(__file__).with_name("plane-pair-sharing-3773.py")))
plane, flags = base["plane"], base["flags"]
shore_masks, residual_matching = base["shore_masks"], base["residual_matching"]
vertices, full, bits, mask = range(13), (1 << 13)-1, base["bits"], base["mask"]
group = plane["collineations"]()
# p = l + {0,1,3,9} in the posted coordinates. Negate the stored line.
assert {(p,(-l) % 13) for p,l in flags} == {
    (p,l) for p in vertices for l in vertices if (p-l) % 13 in (0,1,3,9)}
edges = {(p,l+13) for p,l in flags}
neighbors = [{b if a == v else a for a,b in edges if v in (a,b)} for v in range(26)]


def point_orbits():
    seen = set()
    for chosen in range(1, full+1):
        if chosen in seen:
            continue
        orbit = {mask(g[i] for i in bits(chosen)) for g,_ in group}
        seen.update(orbit)
        yield chosen, len(orbit)
    assert len(seen) == full


def covers(damaged, cap):
    for chosen in range(1 << 13):
        points = set(bits(chosen))
        if len(points) > cap or not {v for v in damaged if v < 13} <= points:
            continue
        lines = {l for p,l in edges if p not in points} | {v for v in damaged if v >= 13}
        spare = cap - len(points) - len(lines)
        if spare < 0:
            continue
        optional = set(range(13,26)) - lines
        for count in range(spare+1):
            for extra in combinations(optional, count):
                yield points | lines | set(extra)


def required_leaves(support, virtual, budget):
    expanded = support - virtual
    offsets = tuple(2 * int(v in expanded) for v in range(26))
    # An empty virtual shore specifies the fully expanded formula comparison.
    for mates in product(*(sorted(virtual-{v}) for v in sorted(virtual))):
        deleted, damaged = set(), set()
        for v, mate in zip(sorted(virtual), mates):
            common, = neighbors[v] & neighbors[mate]
            deleted.add((v,common) if v < 13 else (common,v))
            damaged.add(common)
        kept = edges - deleted
        cap = budget + sum(offsets) - len(kept)
        candidates = set()
        for cover in covers(damaged, cap):
            counts = [int(v in cover) for v in range(26)]
            free = []
            for p,l in kept:
                if p not in cover:
                    counts[p] += 1
                elif l not in cover:
                    counts[l] += 1
                else:
                    free.append((p,l))
            for ends in product((0,1), repeat=len(free)):
                charges = counts.copy()
                for end, edge in zip(ends, free):
                    charges[edge[end]] += 1
                lower = tuple(max(1,n-k) for n,k in zip(charges,offsets))
                if sum(lower) <= budget:
                    candidates.add(lower)
        yield candidates


def rejects_two_reads(points, lines):
    support = points | lines
    budget = 64 - len(support)
    choices = [shore for shore in (points,lines) if len(shore) > 1] or [set()]
    possible = {(1,)*26}
    for virtual in choices:
        for candidates in required_leaves(support, virtual, budget):
            refined = set()
            for a in possible:
                for b in candidates:
                    lower = tuple(map(max,a,b))
                    if sum(lower) <= budget:
                        refined.add(lower)
            possible = refined
            if not possible:
                return True
    return False


def single_mixed_disjunction():
    p_inc, p_active, p_missed = shore_masks(0)
    l_inc, l_active, l_missed = shore_masks(1)
    counts = {}
    remaining = set()
    total = 0
    for points, weight in point_orbits():
        for lines in range(1, full + 1):
            deleted = (p_active[points] | l_active[lines]) & p_missed[points] & l_missed[lines]
            damaged_p = mask(i for i in vertices if p_inc[i] & deleted)
            damaged_l = mask(i for i in vertices if l_inc[i] & deleted)
            leaves = (52 - deleted.bit_count() + damaged_p.bit_count() + damaged_l.bit_count()
                      + residual_matching(full ^ damaged_p, full ^ damaged_l))
            p, l = points.bit_count(), lines.bit_count()
            # At least p+l raw slots construct the helper, with at least one
            # excess reader. Add them to the physical leaves of the final trees.
            gates = leaves + p + l
            if gates <= 64:
                remaining.add((points, lines, gates))
                key = (min(p, l), max(p, l), gates)
                counts[key] = counts.get(key, 0) + weight
            total += weight
    assert total == 8191 ** 2
    assert counts == {(1,1,64):117, (1,2,64):936, (1,3,62):312,
                      (1,4,63):312, (2,2,64):702, (2,3,64):312}
    # Stabilize the two shores together for the more expensive labeled tests.
    seen = set()
    for points, lines, lower in sorted(remaining):
        if (points, lines) in seen:
            continue
        pts, ls = tuple(bits(points)), tuple(bits(lines))
        orbit = {(mask(g[i] for i in pts), mask(h[i] for i in ls)) for g,h in group}
        seen.update(orbit)
        if lower == 64:
            assert rejects_two_reads(set(pts), {13+l for l in ls})
        else:
            assert min(len(pts), len(ls)) == 1  # one-shore equality argument in the proof
    assert len(seen) == sum(counts.values())
    print(total, "mixed disjunctions checked")


def single_shared_rectangle():
    # The helper is (OR of chosen points) AND (OR of chosen lines). Its
    # input cone is private. A flag activates it exactly in their rectangle.
    p_inc, p_active, p_missed = shore_masks(0)
    l_inc, l_active, l_missed = shore_masks(1)
    all_flags = (1 << 52) - 1
    neighborhoods = [[mask(plane["NEIGH"][i]) for i in vertices],
                     [mask(plane["LINES"][i]) for i in vertices]]
    endpoints = [[f[0] for f in flags], [f[1] for f in flags]]

    @lru_cache(maxsize=8192)
    def edge_matching(edges):
        owner = {}

        def augment(p, visited):
            for flag in bits(p_inc[p] & edges):
                line = flags[flag][1]
                if line in visited:
                    continue
                visited.add(line)
                if line not in owner or augment(owner[line], visited):
                    owner[line] = p
                    return True
            return False

        return sum(augment(p, set()) for p in vertices)

    def touching(edge_mask):
        points = mask(i for i in vertices if p_inc[i] & edge_mask)
        lines = mask(i for i in vertices if l_inc[i] & edge_mask)
        return p_active[points] | l_active[lines]

    def extra_rows(kept, active, masked, points, lines):
        damaged = [0, 0]
        for side, stars in enumerate((p_inc, l_inc)):
            own, opposite = (points, lines) if side == 0 else (lines, points)
            neighbors = neighborhoods[side]
            for vertex, star in enumerate(stars):
                local = kept & star
                for marker in bits(star & ~kept):
                    # The marker must force this vertex on all its local
                    # comparison columns. The other endpoint is present.
                    if active & (1 << marker) and local & ~masked:
                        continue
                    rows = local | (1 << marker)
                    if rows & active:
                        needed = mask(endpoints[1 - side][f] for f in bits(rows))
                        # Add an allowed helper pair to the required opposite
                        # vertices, remaining independent on the base column.
                        if not any(not (neighbors[a] & needed) and (opposite & ~neighbors[a])
                                   for a in bits(own)):
                            continue
                    damaged[side] |= 1 << vertex
                    break
        outside = kept & ~(p_active[damaged[0]] | l_active[damaged[1]])
        return (kept.bit_count() + sum(m.bit_count() for m in damaged)
                + edge_matching(outside))

    total = used_markers = used_subsets = 0
    for points, weight in point_orbits():
        for lines in range(1, full + 1):
            total += weight
            size = points.bit_count() + lines.bit_count()
            active = p_active[points] & l_active[lines]
            # An inactive helper is removable. Otherwise its private cone
            # uses at least size raw slots, one per essential variable.
            if not active or size + 52 - active.bit_count() >= 65:
                continue
            masked = all_flags & ~(p_missed[points] | l_missed[lines])
            # Each active row kept in a menu needs a forcing column for
            # each endpoint: the other endpoint plus a nonincident mate.
            base_ok = mask(f for f in bits(active)
                           if points & ~neighborhoods[1][flags[f][1]]
                           and lines & ~neighborhoods[0][flags[f][0]])
            clean = all_flags & (~touching(active) | masked) & ~(active & ~base_ok)
            active_kept = clean & active
            hybrid = active_kept | (all_flags & ~active & (~touching(active_kept) | masked))
            menus = (all_flags ^ active, clean, hybrid)
            if any(size + e.bit_count() + edge_matching(e) >= 65 for e in menus):
                continue
            used_markers += weight
            if any(size + extra_rows(e, active, masked, points, lines) >= 65 for e in menus):
                continue
            used_subsets += weight
            available = active & masked & base_ok
            selected = available
            while selected:
                kept = selected | (all_flags & ~active & (~touching(selected) | masked))
                if size + extra_rows(kept, active, masked, points, lines) >= 65:
                    break
                selected = (selected - 1) & available
            assert selected, (points, lines)
    assert total == 8191 ** 2
    assert (used_markers, used_subsets) == (47307, 468)
    print(total, "rectangles checked,", used_subsets, "needed selected active rows")


def component_sizes(vertices_left, selected):
    remaining = set(vertices_left)
    sizes = []
    while remaining:
        stack = [remaining.pop()]
        size = 0
        while stack:
            v = stack.pop()
            size += 1
            new = {w for edge in selected if v in edge for w in edge} & remaining
            remaining -= new
            stack.extend(new)
        sizes.append(size)
    return tuple(sorted(sizes))


def cold_supports():
    counts, one_gate_slack = Counter(), Counter()
    for points, weight in point_orbits():
        for lines in range(1, full+1):
            d = points.bit_count() + lines.bit_count()
            if d > 9:
                continue
            kept = tuple(tuple(l for l in row if not (points >> p & lines >> l & 1))
                         for p,row in enumerate(plane["ROWS"]))
            m = sum(map(len, kept))
            simple = max(sum((k-p) % 13 in row for p,row in enumerate(kept))
                         for k in (0,1,3,9))
            if d + m + simple > 64:
                continue
            owner = {}
            def augment(p, visited):
                for l in kept[p]:
                    if l in visited:
                        continue
                    visited.add(l)
                    if l not in owner or augment(owner[l], visited):
                        owner[l] = p
                        return True
                return False
            bound = d + m + sum(augment(p,set()) for p in vertices)
            if bound > 64:
                continue
            counts[d,52-m] += weight
            assert bound >= 63 and (bound == 64 or d == 9)
            if bound == 63:
                induced = {(p,l+13) for p,l in flags if l not in kept[p]}
                used = {v for edge in induced for v in edge}
                cuts = [component_sizes(used-{x},induced) for x in used]
                assert len(used) == 9 and component_sizes(used,induced) == (9,)
                assert sorted(cuts) == [(1,7)] + [(8,)]*8
                one_gate_slack[d,52-m] += weight
    assert counts == {(8,8):1404,(8,9):468,(9,8):156,(9,9):16848,(9,10):9360}
    assert one_gate_slack == {(9,10):936}
    print("cold supports checked", dict(counts), "one spare gate", dict(one_gate_slack))



def hot_supports():
    p_inc, p_active, p_missed = shore_masks(0)
    l_inc, l_active, l_missed = shore_masks(1)
    all_flags = (1 << len(flags))-1

    @lru_cache(maxsize=8192)
    def matching(kept):
        owner = {}
        def augment(p, visited):
            for i in bits(kept & p_inc[p]):
                l = flags[i][1]
                if l in visited:
                    continue
                visited.add(l)
                if l not in owner or augment(owner[l],visited):
                    owner[l] = p
                    return True
            return False
        return sum(augment(p,set()) for p in vertices)

    mixed = 0
    for ps, ls in ((2,2),(2,3),(3,2)):
        for pts in combinations(vertices, ps):
            for lines in combinations(vertices, ls):
                block = p_active[mask(pts)] & l_active[mask(lines)]
                if block.bit_count() != ps + ls - 1:
                    continue
                # A forest on these vertices with this many edges is a tree.
                kept = all_flags ^ block
                assert matching(kept) == 13
                if ps+ls != 4:
                    continue
                for p in set(vertices)-set(pts):
                    for l in set(vertices)-set(lines):
                        deleted = kept & (p_inc[p] | l_inc[l]) & p_missed[1<<p] & l_missed[1<<l]
                        dp = mask(v for v in vertices if deleted & p_inc[v])
                        dl = mask(v for v in vertices if deleted & l_inc[v])
                        outside = kept & ~(p_active[dp] | l_active[dl])
                        physical = (kept ^ deleted).bit_count()+dp.bit_count()+dl.bit_count()+matching(outside)
                        assert physical >= 59
                        mixed += 1
    assert mixed == 56628
    print(mixed, "mixed hot pairs with a four-vertex path checked")


if __name__ == "__main__":
    single_mixed_disjunction()
    single_shared_rectangle()
    cold_supports()
    hot_supports()
