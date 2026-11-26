"""Exhaust bounded monotone circuits on one row and one column indicator.

Usage: python monotone-frontiers.py ROWS COLS MASK BUDGET
The number of unordered live signal lists is printed at each depth.
"""
from functools import lru_cache
from itertools import combinations
import argparse


def check(rows, cols, target, gates):
    cells = range(rows * cols)
    if not 0 < target < (1 << len(cells)) - 1:
        raise ValueError("This search assumes a nonconstant target")
    raw = tuple(sum(1 << k for k in cells if pin in (k // cols, rows + k % cols))
                for pin in range(rows + cols))
    falls = [(i, j) for i in cells if target >> i & 1
             for j in cells if not (target >> j & 1)]
    required = (1 << len(falls)) - 1

    @lru_cache(None)
    def separated(wire):
        return sum(1 << k for k, (i, j) in enumerate(falls)
                   if wire >> i & 1 and not (wire >> j & 1))

    def possible(wires):
        seen = 0
        for wire in wires:
            seen |= separated(wire)
        return seen == required

    frontier = {tuple(sorted(s)) for n in range(1, min(len(raw), gates + 1) + 1)
                for s in combinations(raw, n) if possible(s)}
    counts = []
    for left in range(gates, -1, -1):
        counts.append(len(frontier))
        if any(target in wires for wires in frontier):
            return True, counts
        if not left or not frontier:
            break
        later = set()
        for wires in frontier:
            for i, j in combinations(range(len(wires)), 2):
                x, y = wires[i], wires[j]
                others = [w for k, w in enumerate(wires) if k not in (i, j)]
                for value in (x & y, x | y):
                    # A later use may keep either or both operands alive.
                    for keep in ((), (x,), (y,), (x, y)):
                        candidate = (*others, value, *keep)
                        if len(candidate) <= left and possible(candidate):
                            later.add(tuple(sorted(candidate)))
        frontier = later
    return False, counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("rows", "cols", "target", "gates"):
        parser.add_argument(arg, type=int)
    args = parser.parse_args()
    found, counts = check(args.rows, args.cols, args.target, args.gates)
    print("Witness reached:", found, "| Frontier sizes:", counts)
