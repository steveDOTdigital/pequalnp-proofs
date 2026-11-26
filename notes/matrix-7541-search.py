"""Exhaustive eight-gate AND/OR search for the 3-by-5 matrix 7541."""
from functools import lru_cache
from itertools import combinations

SAMPLES = [(i, j+3) for i in range(3) for j in range(5)]
CELLS = range(len(SAMPLES))
ALL = (1 << len(SAMPLES)) - 1
MASK = sum(1 << k for k, (i, j) in enumerate(SAMPLES) if 7541 >> (5*i+j-3) & 1)
RAW = tuple(sum(1 << k for k, pair in enumerate(SAMPLES) if pin in pair) for pin in range(8))
POS = [cell for cell in CELLS if MASK >> cell & 1]
NEG = [cell for cell in CELLS if not (MASK >> cell & 1)]
ALL_PAIRS = (1 << (len(POS) * len(NEG))) - 1


@lru_cache(None)
def pair_bits(wire):
    # Monotone gates can separate an accepted input from a rejected input
    # only when an incoming wire already decreases in that direction.
    down = up = 0
    for p in POS:
        for n in NEG:
            down = 2 * down + bool(wire >> p & 1 and not (wire >> n & 1))
            up = 2 * up + bool(wire >> n & 1 and not (wire >> p & 1))
    return down, down | up


def viable(wires, budget):
    if len(wires) > budget + 1:
        return False
    union = 0
    for w in wires:
        union |= pair_bits(w)[0]
    return union == ALL_PAIRS


def advance(wires, budget):
    # Leave an operand available exactly when it has another future use.
    # Duplicate and constant outputs are permitted in this replay.
    for i, x in enumerate(wires):
        for j in range(i):
            y = wires[j]
            rest = wires[:j] + wires[j + 1:i] + wires[i + 1:]
            for value in (x & y, x | y):
                yield (*rest, value)
                if len(wires) <= budget:
                    yield (*rest, value, x)
                    yield (*rest, value, y)
                if len(wires) < budget:
                    yield (*wires, value)


def verify():
    budget = 8
    frontier = {tuple(sorted(ws)) for n in range(1, budget + 2)
                for ws in combinations(RAW, n) if viable(ws, budget)}
    counts = []
    while True:
        counts.append(len(frontier))
        assert all(MASK not in state for state in frontier)
        if not frontier or not budget:
            break
        next_frontier = set()
        for state in frontier:
            for candidate in advance(state, budget):
                if viable(candidate, budget - 1):
                    next_frontier.add(tuple(sorted(candidate)))
        budget -= 1
        frontier = next_frontier
    assert not frontier
    assert counts == [1, 29, 130, 166, 59, 4, 0]
    print("Eight-gate frontier counts:", counts)


def verify_witness():
    gates = [('or',4,0), ('or',5,1), ('or',9,8), ('or',6,8), ('or',7,9),
             ('and',12,11), ('or',3,13), ('and',2,10), ('or',15,14)]
    for row in range(3):
        for col in range(5):
            wires = [i == row for i in range(3)] + [j == col for j in range(5)]
            for op, x, y in gates:
                wires.append((wires[x] and wires[y]) if op == 'and' else (wires[x] or wires[y]))
            assert wires[16] == bool(7541 >> (5*row+col) & 1)
    print('Nine gates checked on all 15 promised inputs.')


if __name__ == "__main__":
    verify_witness()
    verify()
