"""Exhaust a one-NOT repair family around a checked 20-gate circuit.

Bypass one gate to any earlier wire. Replace a remaining gate by NOT of
any earlier wire. At one other remaining gate allow any AND or OR of two
earlier wires, including repetitions. The bypass may affect the output.
This enumerates a neighborhood of one circuit, not all 19-gate circuits.
"""

from itertools import combinations_with_replacement


EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
         (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
GATES = [
    ("or", 1, 4), ("or", 10, 5), ("and", 0, 11),
    ("or", 2, 6), ("and", 1, 13),
    ("or", 2, 4), ("or", 15, 8), ("and", 3, 16),
    ("or", 2, 5), ("or", 18, 9), ("and", 7, 19),
    ("or", 6, 5), ("and", 8, 21), ("or", 4, 6), ("and", 9, 23),
    ("or", 12, 14), ("or", 25, 17), ("or", 26, 20),
    ("or", 27, 22), ("or", 28, 24),
]
ALL = (1 << 1024) - 1
INPUTS = [sum(((x >> i) & 1) << x for x in range(1024)) for i in range(10)]
TARGET = sum(1 << x for x in range(1024)
             if any((x >> i) & (x >> j) & 1 for i, j in EDGES))


def run(gates, prefix):
    wires = prefix.copy()
    for op, i, j in gates:
        if op == "not":
            wires.append(ALL ^ wires[i])
        elif op == "and":
            wires.append(wires[i] & wires[j])
        else:
            wires.append(wires[i] | wires[j])
    return wires


def bypass(deleted, replacement):
    wire = 10 + deleted

    def remap(i):
        return replacement if i == wire else i - int(i > wire)

    gates = [(op, remap(i), remap(j)) for k, (op, i, j) in enumerate(GATES)
             if k != deleted]
    return gates, remap(29)


def find_repair(gates, output, unary):
    wires = run(gates, INPUTS)
    if wires[output] == TARGET:
        return list(gates)
    for gate in range(19):
        if gate == unary:
            continue
        i = gate + 10
        available = wires[:i]
        tail = gates[gate + 1:]
        low = run(tail, available + [0])[output]
        high = run(tail, available + [ALL])[output]
        # At inputs where both cofactors agree, rewiring cannot help.
        if (low ^ TARGET) & (ALL ^ (low ^ high)):
            continue
        select = low ^ high
        required = (low ^ TARGET) & select
        for a, b in combinations_with_replacement(range(i), 2):
            for op, candidate in (("and", available[a] & available[b]),
                                  ("or", available[a] | available[b])):
                if (candidate & select) == required:
                    repaired = gates.copy()
                    repaired[gate] = (op, a, b)
                    assert run(repaired, INPUTS)[output] == TARGET
                    return repaired
    return None


def search():
    assert run(GATES, INPUTS)[29] == TARGET
    skeletons = 0
    descriptions = 0
    for deleted in range(20):
        for replacement in range(10 + deleted):
            gates, output = bypass(deleted, replacement)
            for unary in range(19):
                i = 10 + unary
                for operand in range(i):
                    gates[unary], old = ("not", operand, operand), gates[unary]
                    skeletons += 1
                    descriptions += sum((10 + g) * (11 + g)
                                        for g in range(19) if g != unary)
                    repaired = find_repair(gates, output, unary)
                    if repaired is not None:
                        print("Verified witness:", repaired, "output:", output)
                        return
                    gates[unary] = old
    print(f"No witness in {skeletons:,} skeletons and "
          f"{descriptions:,} repair descriptions (duplicates included).")


if __name__ == "__main__":
    search()
