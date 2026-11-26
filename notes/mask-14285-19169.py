"""Exhaustive eight-gate check for graph 14285."""
from functools import lru_cache
from itertools import combinations

MASK = 14285
CELLS = range(16)
ALL = (1 << 16) - 1
RAW = tuple(sum(1 << cell for cell in CELLS if pin in (cell // 4, 4 + cell % 4))
            for pin in range(8))
POS = [cell for cell in CELLS if MASK >> cell & 1]
NEG = [cell for cell in CELLS if not (MASK >> cell & 1)]
ALL_PAIRS = (1 << (len(POS) * len(NEG))) - 1


@lru_cache(None)
def pair_bits(wire):
    # Before the last possible NOT we require distinct feature vectors.
    # When only consuming binary gates remain, we require a directed decrease.
    down = up = 0
    for p in POS:
        for n in NEG:
            down = 2 * down + bool(wire >> p & 1 and not (wire >> n & 1))
            up = 2 * up + bool(wire >> n & 1 and not (wire >> p & 1))
    return down, down | up


def viable(wires, budget):
    if len(wires) > budget + 1:
        return False
    either_direction = budget >= len(wires)
    union = 0
    for w in wires:
        union |= pair_bits(w)[either_direction]
    return union == ALL_PAIRS


def advance(wires, budget):
    # Leave an operand available exactly when it has another future use.
    # Duplicate and constant outputs are permitted in this replay.
    for i, x in enumerate(wires):
        if len(wires) <= budget:
            rest = wires[:i] + wires[i + 1:]
            yield (*rest, ALL ^ x)
            yield (*wires, ALL ^ x)
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
    print("Eight-gate frontier counts:", counts)


if __name__ == "__main__":
    verify()
