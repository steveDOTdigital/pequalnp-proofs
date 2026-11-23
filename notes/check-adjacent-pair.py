"""Exact local gate count with arbitrary outside-only signals available for free."""

from itertools import product


def settings_mask(bit_count, test):
    return sum(int(test(*bits)) << i
               for i, bits in enumerate(product((False, True), repeat=bit_count)))


# Each 4-bit group lists the four (x,y) inputs for one choice of the four
# outside bits. Even repeated uses of an outside signal may vary independently.
FULL = (1 << 64) - 1
X = settings_mask(6, lambda a, b, c, d, x, y: x)
Y = settings_mask(6, lambda a, b, c, d, x, y: y)
EXTERNAL = [settings_mask(6, lambda *bits: bits[j]) for j in range(4)]
TARGET = {8, 12, 10, 14, 15}  # AND, x, y, OR, true


def enumerate_gates(wires, depth, totals, matches):
    """Topological enumeration, with fresh free input allowed at every gate."""
    for i, left in enumerate(wires):
        candidates = [FULL ^ left, left & EXTERNAL[depth], left | EXTERNAL[depth]]
        for right in wires[:i]:
            candidates.extend((left & right, left | right))
        for out in candidates:
            totals[depth] += 1
            rows = {(out >> shift) & 15 for shift in range(0, 64, 4)}
            if TARGET <= rows:
                matches[depth] += 1
            if depth < 3:
                enumerate_gates(wires + [out], depth + 1, totals, matches)


def main():
    totals, matches = [0] * 4, [0] * 4
    enumerate_gates([X, Y], 0, totals, matches)
    print("gates, candidate programs, programs realizing all five rows")
    for depth, (total, found) in enumerate(zip(totals, matches), 1):
        print(depth, total, found)
    assert not any(matches)

    # Five gates realize the graph expression: one OR inside the first AND,
    # a second AND for the other endpoint, and two OR gates to join terms.
    rows = set()
    for outside_edge, p, q in product((False, True), repeat=3):
        rows.add(settings_mask(2, lambda x, y:
                               ((x or q) and y) or (x and p) or outside_edge))
    assert rows == TARGET
    print("Five-gate construction realizes exactly", sorted(rows))


if __name__ == "__main__":
    main()
