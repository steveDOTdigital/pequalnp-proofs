"""Reproduce the reduced tests and search a bounded family of 23-gate repairs.

Inputs 0..4 are points; 5..16 are lines 0..8 and 10..12. Inputs 17..19
are the two pairwise ORs and their union inside the already-built point-6 star.
Each 64-bit integer below evaluates one wire on the 20 positive and 44
maximal negative rows simultaneously.
"""
from itertools import combinations_with_replacement, product

D = (0, 1, 3, 9)
LINES = tuple(tuple((w + d) % 13 for d in D) for w in range(13))
LINE_MASKS = tuple(sum(1 << p for p in line) for line in LINES)
PENCILS = tuple(sum(1 << w for w, line in enumerate(LINES) if p in line)
                for p in range(13))
VISIBLE = tuple(w for w in range(13) if w != 9)


def disjoint(mask, blocks):
    return sum(1 << i for i, block in enumerate(blocks) if not (mask & block))


def contained(mask, blocks):
    return any(not (mask & ~block) for block in blocks)


def project(points, lines):
    bits = [bool(points & (1 << i)) for i in range(5)]
    bits += [bool(lines & (1 << w)) for w in VISIBLE]
    u = bool(lines & ((1 << 3) | (1 << 5)))
    v = bool(lines & ((1 << 6) | (1 << 10)))
    bits.extend((u, v, u or v))
    return sum(int(b) << i for i, b in enumerate(bits))


def samples():
    positive = {project(1 << p, 1 << w) for w, line in enumerate(LINES)
                for p in line if p < 5}
    all_negative = []
    projected = set()
    for mask in range(1 << 13):
        ws = disjoint(mask, LINE_MASKS)
        if (disjoint(ws, PENCILS) == mask and
                (contained(mask, LINE_MASKS) or contained(ws, PENCILS))):
            all_negative.append((mask, ws))
        if contained(mask, LINE_MASKS):
            projected.add(project(mask, ws))
        if contained(mask, PENCILS):
            projected.add(project(disjoint(mask, PENCILS), mask))
    maximal = sorted(m for m in projected
                     if not any(m != n and not (m & ~n) for n in projected))
    assert len(all_negative) == 236
    assert (len(positive), len(maximal)) == (20, 44)
    assert all(any(not (project(p, w) & ~n) for n in maximal) for p, w in all_negative)
    return sorted(positive), maximal


def baseline(pairings):
    gates = []
    def append(op, a, b):
        gates.append((op, a, b))
        return 19 + len(gates)
    stars = []
    for p, pairing in enumerate(pairings):
        a, b, c, d = [5 + VISIBLE.index(w) for w, line in enumerate(LINES) if p in line]
        if pairing == 1:
            b, c = c, b
        elif pairing == 2:
            b, d = d, b
        first, second = append("or", a, b), append("or", c, d)
        neighborhood = append("or", first, second)
        stars.append(append("and", p, neighborhood))
    out = stars[0]
    for s in stars[1:]:
        out = append("or", out, s)
    return gates


def evaluate(op, a, b):
    return a & b if op == "and" else a | b


def repaired(gates, bypass, source, changed=None, replacement=None):
    def remap(i):
        if i == 20 + bypass:
            return source
        return i - int(i > 20 + bypass)
    result = []
    for j, gate in enumerate(gates):
        if j == bypass:
            continue
        op, a, b = replacement if j == changed else gate
        result.append((op, remap(a), remap(b)))
    return result, remap(20 + len(gates) - 1)


def search():
    pos, neg = samples()
    rows = pos + neg
    source = [sum(((m >> i) & 1) << n for n, m in enumerate(rows)) for i in range(20)]
    goal = (1 << len(pos)) - 1
    ones = (1 << len(rows)) - 1
    candidates = 0

    def report(result):
        gates, out = result
        wires = list(source)
        for op, a, b in gates:
            wires.append(evaluate(op, wires[a], wires[b]))
        assert len(gates) == 23 and wires[out] == goal
        print("23-gate witness", gates, "output", out)
        return True

    for pattern in product(range(3), repeat=5):
        gates = baseline(pattern)
        def finish(wires, start):
            for op, a, b in gates[start:]:
                wires.append(evaluate(op, wires[a], wires[b]))
            return wires[-1]
        clean = list(source)
        assert finish(clean, 0) == goal
        for k in range(len(gates)):
            # Wires equal on all tested rows are interchangeable at the bypass.
            seen = set()
            for s, value in enumerate(clean[:20+k]):
                if value in seen:
                    continue
                seen.add(value)
                live = clean[:20+k] + [value]
                if finish(live, k + 1) == goal:
                    return report(repaired(gates, k, s))
                for j in range(k+1, len(gates)):
                    old = live[:20+j]
                    lo = finish(old + [0], j + 1)
                    hi = finish(old + [ones], j + 1)
                    if (lo & ~goal) or (goal & ~hi):
                        continue
                    must_on, must_off = goal & ~lo, hi & ~goal
                    unique = {}
                    for i, bits in enumerate(old):
                        unique.setdefault(bits, i)
                    for a, b in combinations_with_replacement(unique.values(), 2):
                        for op in ("and", "or"):
                            v = evaluate(op, old[a], old[b])
                            candidates += 1
                            if not (must_on & ~v or must_off & v):
                                return report(repaired(gates, k, s, j, (op, a, b)))
    print("243 balanced star templates exhausted; eligible replacement gates checked:", candidates)
    return False


if __name__ == "__main__":
    p, n = samples()
    print("Positive masks:", p)
    print("Maximal negative masks:", n)
    search()
