"""Enumerate up to four live gates for L-meta-19272. No external dependencies."""
from itertools import combinations_with_replacement

FULL = 65535
ROWS = tuple(15 << (4 * i) for i in range(4))
COLS = tuple(sum(1 << (4 * i + j) for i in range(4)) for j in range(4))
BASE = frozenset((0, FULL, *ROWS, *COLS))
TARGET = 278


def verify():
    left = ROWS[0] & (COLS[1] | COLS[2])
    right = COLS[0] & (ROWS[1] | ROWS[2])
    assert left | right == TARGET
    states = {frozenset()}
    counts = []
    for size in range(1, 5):
        counts.append(len(states))
        following = set()
        for state in states:
            available = BASE | state
            outputs = {FULL ^ x for x in available}
            for x, y in combinations_with_replacement(available, 2):
                outputs.add(x & y)
                outputs.add(x | y)
            assert TARGET not in outputs
            if size < 4:
                following.update(state | {z} for z in outputs - available)
        states = following
    assert counts == [1, 52, 1710, 46580]
    print("Minimum five gates. Exhausted prefix counts:", counts)


if __name__ == "__main__":
    verify()
