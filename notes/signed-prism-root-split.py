"""Count the prism search states that survive the root-partition condition."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from runpy import run_path


FULL = (1 << 64) - 1
TARGET = 0xFFFEFFFCFEFEEEA0


def possible_root(wires):
    """Test every root partition against the 64 actual input rows."""
    count = len(wires)
    full_set = (1 << count) - 1
    blocked = [[0] * (full_set + 1) for _ in range(2)]

    for row in range(64):
        color = (TARGET >> row) & 1
        matches = [0] * (full_set + 1)
        matches[0] = FULL ^ TARGET if color else TARGET
        signals = [wire if wire >> row & 1 else FULL ^ wire for wire in wires]
        for subset in range(1, full_set):
            least = subset & -subset
            matches[subset] = matches[subset ^ least] & signals[least.bit_length() - 1]
            if matches[subset]:
                blocked[color][subset] |= 1 << row

    # One side contains the first wire. Exchanging sides changes neither test.
    for left in range(1, full_set, 2):
        right = full_set ^ left
        if any((masks[left] & masks[right]) == 0 for masks in blocked):
            return True
    return False


def main():
    generator = Path(__file__).with_name("prism-frontier-lean.py")
    pools, images, _ = run_path(str(generator))["read_layers"]()
    lookup = [{tuple(wires): index for wires, index, _ in layer} for layer in images]
    active = [set() for _ in pools]
    active[9].add(0)

    @lru_cache(maxsize=None)
    def allowed(budget, index):
        wires = pools[budget][index]
        return len(wires) != budget + 1 or len(wires) < 2 or possible_root(wires)

    for budget in range(9, 0, -1):
        for index in active[budget]:
            wires = pools[budget][index]
            for a, b in combinations(wires, 2):
                rest = [w for w in wires if w != a and w != b]
                for out in (a & b, a & ~b, ~a & b, a | b):
                    if out == 0 or out in wires:
                        continue
                    assert out != TARGET
                    for retained in ([], [a], [b], [a, b]):
                        successor = tuple(sorted([out] + rest + retained))
                        if len(successor) > budget:
                            continue
                        other = lookup[budget - 1].get(successor)
                        if other is not None and allowed(budget - 1, other):
                            active[budget - 1].add(other)

    before = list(map(len, pools))
    after = list(map(len, active))
    print("Budget", "Original", "After root test")
    for budget in range(len(pools)):
        print(budget, before[budget], after[budget])
    print("Total", sum(before), sum(after))


if __name__ == "__main__":
    main()
