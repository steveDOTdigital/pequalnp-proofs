from functools import lru_cache
from itertools import combinations

SAMPLES = [(i, j+4) for i in range(4) for j in range(6)]
CELLS = range(len(SAMPLES))
ALL = (1 << len(SAMPLES)) - 1
MASK = sum(1 << k for k, (i, j) in enumerate(SAMPLES) if 327167 >> (6*i+j-4) & 1)
RAW = tuple(sum(1 << k for k, pair in enumerate(SAMPLES) if pin in pair) for pin in range(10))
POS = [cell for cell in CELLS if MASK >> cell & 1]
NEG = [cell for cell in CELLS if not (MASK >> cell & 1)]
ALL_PAIRS = (1 << (len(POS) * len(NEG))) - 1


@lru_cache(None)
def pair_bits(wire):
    # A monotone continuation needs a wire that is high at p and low at n.
    down = up = 0
    for p in POS:
        for n in NEG:
            down = 2 * down + bool(wire >> p & 1 and not (wire >> n & 1))
            up = 2 * up + bool(wire >> n & 1 and not (wire >> p & 1))
    return down, down | up


def viable(wires, budget):
    if len(wires) > budget + 1:
        return False
    either_direction = False
    union = 0
    for w in wires:
        union |= pair_bits(w)[either_direction]
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
        print('layer',budget,len(frontier),flush=True)
        if any(MASK in state for state in frontier):
            raise AssertionError('unexpected eight-gate witness')
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
    assert counts == [1, 6, 13, 13, 6, 1, 0]
    print("Eight-gate frontier counts:", counts)


if __name__ == "__main__":
    verify()

    gates = [["or",4,0],["or",6,5],["or",7,11],["and",12,2],["or",10,13],["or",8,11],["or",9,15],["and",16,1],["or",14,17]]
    wires = list(RAW)
    for op, x, y in gates:
        wires.append(wires[x] & wires[y] if op == 'and' else wires[x] | wires[y])
    assert len(gates) == 9 and wires[-1] == MASK == 327167
    print('Nine gates verified on all 24 promised inputs.')
