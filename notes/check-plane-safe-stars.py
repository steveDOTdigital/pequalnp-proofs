"""Verify the sharp safe-nesting examples for PEqualNP case L-meta-2069."""
from itertools import combinations

ORDER = 13
INPUTS = 2 * ORDER
DIFFERENCES = {0, 1, 3, 9}
INCIDENT = {(p, l) for p in range(ORDER) for l in range(ORDER)
            if (p - l) % ORDER in DIFFERENCES}
NEIGHBORS = [{l for q, l in INCIDENT if q == p} for p in range(ORDER)]


def maximal_negatives():
    """Saturate a point subset by all compatible lines, then all compatible points."""
    rows = set()
    for points in range(1 << ORDER):
        available = set(range(ORDER))
        for p in range(ORDER):
            if points & (1 << p):
                available -= NEIGHBORS[p]
        closed = sum(1 << p for p in range(ORDER) if NEIGHBORS[p].isdisjoint(available))
        rows.add(closed | sum(1 << (ORDER + l) for l in available))
    return sorted(rows)


def star_circuit(extra, dual=False):
    gates = []

    def gate(op, a, b):
        assert a != b and 0 <= min(a, b) and max(a, b) < INPUTS + len(gates)
        gates.append((op, a, b))
        return INPUTS + len(gates) - 1

    def join(wires):
        out, *rest = wires
        for i in rest:
            out = gate("or", out, i)
        return out

    stars = []
    for c in range(ORDER):
        center = ORDER + c if dual else c
        leaves = ([p for p in range(ORDER) if (p, c) in INCIDENT] if dual
                  else [ORDER + l for l in sorted(NEIGHBORS[c])])
        if c == 0 and extra:
            original = leaves[0]
            leaves[0] = gate("and", center, original)
            if extra == 2:
                leaves[0] = gate("and", leaves[0], original)
        stars.append(gate("and", center, join(leaves)))
    return gates, join(stars)


def wires(gates, values):
    values = list(values)
    for op, a, b in gates:
        values.append(values[a] & values[b] if op == "and" else values[a] | values[b])
    return values


def derivative(gates, out, at, direction):
    single = wires(gates, [i == at for i in range(INPUTS)])
    ds = [i == direction for i in range(INPUTS)]
    for op, a, b in gates:
        ds.append((single[a] and ds[b]) or (ds[a] and single[b])
                  if op == "and" else ds[a] or ds[b])
    return ds[out]


def check():
    assert len(INCIDENT) == 52 and all(len(v) == 4 for v in NEIGHBORS)
    assert all(len(a & b) == 1 for a, b in combinations(NEIGHBORS, 2))
    edges = sorted(INCIDENT)
    negatives = maximal_negatives()
    rows = [1 << p | 1 << (ORDER + l) for p, l in edges] + negatives
    inputs = [sum(1 << k for k, row in enumerate(rows) if row & (1 << i))
              for i in range(INPUTS)]
    truth = (1 << len(edges)) - 1
    print(f"{len(edges)} minimal positives and {len(negatives)} maximal negatives")
    for dual in (False, True):
        for extra in range(3):
            gates, out = star_circuit(extra, dual)
            assert len(gates) == 64 + extra
            values = wires(gates, inputs)
            assert values[out] == truth
            contains_and = [False] * INPUTS
            nested = False
            for j, (op, a, b) in enumerate(gates):
                lower = contains_and[a] or contains_and[b]
                if op == "and":
                    assert values[INPUTS + j] & ~truth == 0
                    nested |= lower
                contains_and.append(op == "and" or lower)
            assert nested == (extra > 0)
            misses = []
            for p, l in edges:
                a = derivative(gates, out, p, ORDER + l)
                b = derivative(gates, out, ORDER + l, p)
                if not (a and b):
                    misses.append(((p, l), a, b))
            expected = [] if extra == 0 else [((0, 0), not dual, dual)]
            if extra == 2:
                expected = [((0, 0), False, False)]
            assert misses == expected, (extra, dual, misses)
            print(f"dual={dual}, size={len(gates)}, nested={nested}, derivative misses={misses}")


if __name__ == "__main__":
    check()
