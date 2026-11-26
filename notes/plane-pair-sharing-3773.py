"""Reproduce the order-three plane checks for L-meta-3773 (Python 3)."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import runpy

plane = runpy.run_path(str(Path(__file__).with_name("plane-shared-or-check.py")))
flags = tuple(plane["FLAGS"])
vertices = range(13)
full = (1 << 13) - 1


def bits(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value -= low


def mask(indices):
    return sum(1 << index for index in indices)


def check_star_controls():
    # A negative input has at most three active vertices on one shore.
    avoiding_four = [sum(all((p, line) not in flags for p in group) for line in vertices)
                     for group in combinations(vertices, 4)]
    assert len(avoiding_four) == 715 and max(avoiding_four) == 3
    # Lines have addresses 13..25. Append any requested first gate before
    # building the stars, so every later internal address is shifted correctly.
    for first in (None, ("and", 0, 13), ("or", 0, 13), ("or", 2, 13)):
        gates = [] if first is None else [first]

        def gate(op, a, b):
            address = 26 + len(gates)
            assert 0 <= a < address and 0 <= b < address
            gates.append((op, a, b))
            return address

        terms = []
        for line in vertices:
            points = sorted(p for p, l in flags if l == line)
            a, b, c, d = points
            neighbors = gate("or", gate("or", a, b), gate("or", c, d))
            terms.append(gate("and", 13 + line, neighbors))
        result = terms[0]
        for term in terms[1:]:
            result = gate("or", result, term)
        assert gates[0] == (first or ("or", 0, 1))
        assert len(gates) == (65 if first else 64)
        flags_from_statement = {(p, l) for p in vertices for l in vertices
                                if (p + l) % 13 in (0, 1, 3, 9)}
        assert set(flags) == flags_from_statement

        def evaluate(points, lines):
            values = [bool(points & (1 << i)) for i in vertices]
            values.extend(bool(lines & (1 << i)) for i in vertices)
            for op, a, b in gates:
                values.append(values[a] and values[b] if op == "and" else values[a] or values[b])
            return values[result]

        assert all(evaluate(1 << p, 1 << l) for p, l in flags)
        checked = 0
        for k in range(4):
            for size_k in combinations(vertices, k):
                selected = mask(size_k)
                avoiding = mask(l for l in vertices if all((p, l) not in flags_from_statement for p in size_k))
                assert not evaluate(selected, avoiding)
                assert not evaluate(avoiding, selected)
                checked += 2
        assert checked == 756
    print("Four prescribed first gates: 64, 65, 65, 65 gates; each passed 52 positives and 756 negative tests.")


def point_orbits():
    # The reused generator verifies each permutation on all 52 incidences.
    group = [p for p, _ in plane["collineations"]()]
    seen = set()
    for chosen in range(1, full + 1):
        if chosen in seen:
            continue
        orbit = {mask(permutation[i] for i in bits(chosen)) for permutation in group}
        seen.update(orbit)
        yield chosen, len(orbit)
    assert len(seen) == full


def shore_masks(shore):
    incident = [mask(i for i, f in enumerate(flags) if f[shore] == v) for v in vertices]
    active = [0] * (full + 1)
    for chosen in range(1, full + 1):
        active[chosen] = active[chosen & (chosen - 1)] | incident[(chosen & -chosen).bit_length() - 1]
    neighbors = [mask(f[shore] for f in flags if f[1 - shore] == v) for v in vertices]
    # A canonical comparison contains all neighbors of the other endpoint
    # on this shore, except for the endpoint of the diagonal flag itself.
    missed = [mask(i for i, f in enumerate(flags)
                   if not (chosen & neighbors[f[1 - shore]] & ~(1 << f[shore])))
              for chosen in range(full + 1)]
    return incident, active, missed


@lru_cache(maxsize=16384)
def residual_matching(points, lines):
    owner = {}

    def augment(p, visited):
        for line in plane["ROWS"][p]:
            if not lines & (1 << line) or line in visited:
                continue
            visited.add(line)
            if line not in owner or augment(owner[line], visited):
                owner[line] = p
                return True
        return False

    return sum(augment(p, set()) for p in bits(points))


def single_mixed_disjunction():
    p_inc, p_active, p_missed = shore_masks(0)
    l_inc, l_active, l_missed = shore_masks(1)
    counts = {}
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
            if gates < 64:
                key = (min(p, l), max(p, l), gates)
                counts[key] = counts.get(key, 0) + weight
            total += weight
    assert total == 8191 ** 2
    assert counts == {(1, 3, 62): 312, (1, 4, 63): 312}
    print(total, "mixed supports; only 312 one-plus-three and 312 one-plus-four supports need the one-shore argument.")


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

    total = used_markers = 0
    for points, weight in point_orbits():
        for lines in range(1, full + 1):
            total += weight
            size = points.bit_count() + lines.bit_count()
            active = p_active[points] & l_active[lines]
            # An inactive helper is removable. Otherwise its private cone
            # uses at least size raw slots, one per essential variable.
            if not active or size + 52 - active.bit_count() >= 64:
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
            if any(size + e.bit_count() + edge_matching(e) >= 64 for e in menus):
                continue
            used_markers += weight
            assert any(size + extra_rows(e, active, masked, points, lines) >= 64 for e in menus), (points, lines)
    assert total == 8191 ** 2
    print(total, "mixed rectangles excluded;", used_markers, "used the additional positive rows.")


if __name__ == "__main__":
    check_star_controls()
    single_mixed_disjunction()
    single_shared_rectangle()
