"""Verify nearby Fano circuits and test deletions from the 29-gate construction."""
from itertools import combinations, product

POINTS = range(7)
EDGES = {(p, 7 + l) for p in POINTS for l in POINTS if (p - l) % 7 in (0, 1, 3)}
ROWS = 1 << 14
ALL_ROWS = (1 << ROWS) - 1
INPUT_TABLES = [(ALL_ROWS // ((1 << (1 << i)) + 1)) << (1 << i) for i in range(14)]
TARGET = sum(1 << row for row in range(ROWS)
             if any(row & (1 << p) and row & (1 << l) for p, l in EDGES))


def build(extra, dual=False):
    gates = []
    def gate(op, a, b):
        assert a != b
        gates.append((op, a, b))
        return 13 + len(gates)

    anchor, neighbor = (7, 0) if dual else (0, 7)
    marked = neighbor
    if extra:
        marked = gate("and", anchor, neighbor)
    if extra == 2:
        marked = gate("and", marked, neighbor)
    stars = []
    for i in POINTS:
        center = 7 + i if dual else i
        other = sorted(p if dual else l for p, l in EDGES if (l if dual else p) == center)
        if i == 0:
            other[other.index(neighbor)] = marked
        union = gate("or", gate("or", other[0], other[1]), other[2])
        stars.append(gate("and", center, union))
    output = stars[0]
    for star in stars[1:]:
        output = gate("or", output, star)
    return gates, output


def truth(gates, output):
    wires = INPUT_TABLES.copy()
    for op, a, b in gates:
        wires.append(wires[a] & wires[b] if op == "and" else wires[a] | wires[b])
    return wires[output]


def derivative(gates, output, base, added):
    values = [i == base for i in range(14)]
    delta = [i == added for i in range(14)]
    for op, a, b in gates:
        if op == "and":
            d = (values[a] and delta[b]) or (delta[a] and values[b])
            v = values[a] and values[b]
        else:
            d = delta[a] or delta[b]
            v = values[a] or values[b]
        delta.append(d)
        values.append(v)
    return delta[output]


def bypass(gates, output, changes):
    # Rewire requested gates, prune the output cone, and renumber earlier wires.
    alias = list(range(14))
    rewired = []
    for index, (op, a, b) in enumerate(gates):
        if index in changes:
            alias.append(alias[changes[index]])
        elif alias[a] == alias[b]:
            alias.append(alias[a])
        else:
            alias.append(14 + len(rewired))
            rewired.append((op, alias[a], alias[b]))
    output = alias[output]
    live = {output}
    for index in reversed(range(len(rewired))):
        if 14 + index in live:
            live.update(rewired[index][1:])
    remap = list(range(14))
    result = []
    for index, (op, a, b) in enumerate(rewired):
        remap.append(14 + len(result) if 14 + index in live else None)
        if 14 + index in live:
            result.append((op, remap[a], remap[b]))
    return result, remap[output]


def main():
    positive = {(1 << p) | (1 << l) for p, l in EDGES}
    negative = []
    for selected in range(128):
        off = sum(1 << l for l in POINTS if
                  not any(selected & (1 << p) for p in (l, (l+1) % 7, (l+3) % 7)))
        if all(selected & (1 << p) or any(off & (1 << l) for l in
               (p, (p-1) % 7, (p-3) % 7)) for p in POINTS):
            negative.append(selected | (off << 7))
    assert len(positive) == 21 and len(negative) == 37
    for x in range(ROWS):
        contains_edge = any(x & y == y for y in positive)
        inside_negative = any(x & y == x for y in negative)
        assert contains_edge != inside_negative
        assert contains_edge == bool((TARGET >> x) & 1)
    print("Boundary verified on all rows: 21 positive and 37 maximal negative.")
    seen = set()
    matches = 0
    for dual in (False, True):
        for extra in (0, 1, 2):
            gates, out = build(extra, dual)
            assert len(gates) == 27 + extra and truth(gates, out) == TARGET
            d = (derivative(gates, out, 0, 7), derivative(gates, out, 7, 0))
            expected = [(True, True), (False, True) if dual else (True, False), (False, False)]
            assert d == expected[extra], (extra, dual, d)
            print("Line centers" if dual else "Point centers", len(gates), "gates; derivatives", d)
        def check(changes):
            nonlocal matches
            gs, wire = bypass(gates, out, changes)
            if not gs or gs[0][0] != "and" or len(gs) > 27:
                return
            key = (tuple(gs), wire)
            if key in seen:
                return
            seen.add(key)
            if truth(gs, wire) != TARGET:
                return
            matches += 1
            if not derivative(gs, wire, 0, 7) and not derivative(gs, wire, 7, 0):
                raise AssertionError(("Exact counterexample", gs, wire))
        for j in range(len(gates)):
            for wire in range(14 + j):
                check({j: wire})
        for i, j in combinations(range(len(gates)), 2):
            for a, b in product(gates[i][1:], gates[j][1:]):
                check({i: a, j: b})
    print("Distinct first-AND circuits within budget tested:", len(seen))
    print("Computed the target on all 16,384 rows:", matches)


if __name__ == "__main__":
    main()
