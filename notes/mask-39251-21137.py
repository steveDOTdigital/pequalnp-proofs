"""Live-wire enumeration for the promised graph 39251. Run with Python 3."""
from functools import lru_cache
from itertools import combinations

TARGET = 39251
CELLS = range(20)
RAW = tuple(sum(1 << k for k in CELLS if pin in (k // 5, 4 + k % 5))
            for pin in range(9))
FALLS = [(a, b) for a in CELLS if TARGET >> a & 1
         for b in CELLS if not (TARGET >> b & 1)]
FULL = (1 << len(FALLS)) - 1


@lru_cache(None)
def separated(wire):
    """Bit i certifies that this wire decreases on the i-th required pair."""
    return sum(1 << i for i, (a, b) in enumerate(FALLS)
               if wire >> a & 1 and not (wire >> b & 1))


def distinguishes(wires):
    covered = 0
    for w in wires:
        covered |= separated(w)
    return covered == FULL


@lru_cache(None)
def search(wires, budget):
    if TARGET in wires:
        return ()
    spare = budget - (len(wires) - 1)
    if budget == 0 or spare < 0:
        return None
    for i, j in combinations(range(len(wires)), 2):
        x, y = wires[i], wires[j]
        others = [w for k, w in enumerate(wires) if k not in (i, j)]
        keeps = [()]
        if spare >= 1:
            keeps.extend([(x,), (y,)])
        if spare >= 2:
            keeps.append((x, y))
        for op, new in (("and", x & y), ("or", x | y)):
            if new in wires or new in (0, (1 << 20) - 1):
                continue
            for keep in keeps:
                after = tuple(sorted([*others, new, *keep]))
                if distinguishes(after):
                    rest = search(after, budget - 1)
                    if rest is not None:
                        return ((op, x, y, new),) + rest
    return None


def verify():
    assert all(not distinguishes(RAW[:i] + RAW[i+1:]) for i in range(len(RAW)))
    r0, r1, r2, r3, c0, c1, c2, c3, c4 = RAW
    upper = (r0 & (c0 | c1 | c4)) | (r1 & (c1 | c3)) | (r2 & (c1 | c2)) | (r3 & c0)
    assert upper == TARGET
    witness = search(tuple(sorted(RAW)), 10)
    assert witness is None
    print("Minimum 11. All 9 inputs are essential. No ten-gate circuit.", search.cache_info())


if __name__ == "__main__":
    verify()
