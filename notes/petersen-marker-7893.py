"""Petersen L-meta-7893: the flat ordinary output bound and sharp 19-gate control."""
from functools import lru_cache
from itertools import combinations

POS = (3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640)
NEG = (50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773)
COLD = (50, 104, 116, 138, 208, 276, 402, 548, 554, 770)
NEIGHBORS = 2 | 16 | 32


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask -= bit


def disjunctions(missing, ordinary, centers):
    """All free sources after pinning variables outside the missing edges low."""
    endpoints = 0
    for edge in missing:
        endpoints |= edge
    sources = set(bits(endpoints))
    for center in bits(centers):
        neighbors = 0
        for edge in ordinary:
            if edge & center:
                neighbors |= (edge ^ center) & endpoints
        subset = neighbors
        while subset:
            sources.add(subset)
            subset = (subset - 1) & neighbors
    return tuple(sorted(sources))


@lru_cache(None)
def cover(constraints):
    if not constraints:
        return 0
    return 1 + min(cover(tuple(c for c in constraints if not c & wire))
                   for wire in bits(constraints[0]))


def required_sources(missing, sources):
    constraints = {sum(1 << i for i, src in enumerate(sources) if src & edge and not src & row)
                   for edge in missing for row in COLD}
    assert 0 not in constraints
    minimal = tuple(sorted((c for c in constraints if not any(t != c and t & c == t
                                                              for t in constraints)),
                           key=int.bit_count))
    return cover(minimal)


def flat_bound(size):
    crossing = [edge for edge in POS if not edge & 1 and edge & NEIGHBORS]
    assert len(crossing) == 6
    survivors = []
    for k in range(1, 7):
        for missing in combinations(crossing, k):
            ordinary = set(POS).difference(missing)
            for centers in range(1024):
                r = centers.bit_count()
                budget = size - (len(ordinary) + r - 1)
                if budget < 1 or not all(edge & centers for edge in ordinary):
                    continue
                sources = disjunctions(missing, ordinary, centers)
                if required_sources(missing, sources) <= budget + 1:
                    survivors.append((missing, centers, budget))
    return survivors


def control():
    # The first two gates form the marker x5 AND (x7 OR x8). They never read x0.
    gates = []
    def gate(op, left, right):
        assert left != right and 0 <= min(left, right) < max(left, right) < 10 + len(gates)
        gates.append((op, left, right))
        return 9 + len(gates)
    def any_of(pins):
        head, *tail = pins
        for pin in tail:
            head = gate("or", head, pin)
        return head
    marker = gate("and", 5, gate("or", 7, 8))
    stars = [(0, [1, 4, 5]), (2, [1, 3, 7]), (3, [4, 8]),
             (6, [1, 8, 9]), (9, [4, 7])]
    ordinary = any_of([gate("and", center, any_of(neighbors)) for center, neighbors in stars])
    def values(row):
        wires = [bool(row & (1 << i)) for i in range(10)]
        for op, left, right in gates:
            wires.append((wires[left] and wires[right]) if op == "and" else
                         (wires[left] or wires[right]))
        return wires
    assert len(gates) == 19 and marker != 0 and marker < 10 + len(gates)
    assert all(0 not in inputs[1:] for inputs in gates[:marker - 10 + 1])
    assert all(not values(row & ~1)[marker] for row in COLD)
    for row in range(1024):
        augmented = row | int(values(row & ~1)[marker])
        assert values(augmented)[ordinary] == any((row & edge) == edge for edge in POS)
    return marker, ordinary


if __name__ == "__main__":
    negative = {x for x in range(1024) if not any(x & e == e for e in POS)}
    maxima = {x for x in negative if not any(y != x and x & y == x for y in negative)}
    assert maxima == set(NEG) and set(COLD) == {x for x in NEG if not x & 1}
    exceptions = {x for x in negative if not x & 1 and not any(x & y == x for y in COLD)}
    assert exceptions == {200, 772}
    assert not flat_bound(18)
    survivors = flat_bound(19)
    assert len(survivors) == 3 and all(len(edges) == 2 and k == 2 for edges, _, k in survivors)
    print("At 18 gates no flat ordinary output survives. At 19 gates:")
    for edges, centers, budget in survivors:
        print(" missing", edges, "center mask", centers, "marker budget", budget)
    print("19-gate control passes all 1024 inputs; marker and output:", control())
