"""Exact search for the six-gate threshold obstruction on the two middle layers."""

from itertools import combinations


def main():
    rows = [x for x in range(16) if bin(x).count("1") in (2, 3)]
    full = (1 << len(rows)) - 1
    goal = sum(1 << j for j, x in enumerate(rows) if bin(x).count("1") == 3)
    roots = tuple(sum(1 << j for j, x in enumerate(rows) if x & (1 << i))
                  for i in range(4))

    def outputs(wires):
        possible = {x ^ full for x in wires}
        for x, y in combinations(wires, 2):
            possible.add(x & y)
            possible.add(x | y)
        return possible

    # Given left operand a, encode all truth tables b for which a AND b
    # or a OR b is the target. Constants are allowed without charging a gate.
    mates = [sum(1 << b for b in range(full+1) if a & b == goal or a | b == goal)
             for a in range(full+1)]
    fixed = (0, full) + roots
    states = {()}
    for depth in range(5):
        print(f"{depth} gates: {len(states)} distinct sets of new wire functions", flush=True)
        following = set()
        for state in states:
            wires = fixed + state
            possible = outputs(wires) | set(wires)
            # With two gates left, only one parent of the last gate can be new.
            good = (1 << goal) | (1 << (full ^ goal))
            for a in wires:
                good |= mates[a]
            assert all(not ((good >> b) & 1) for b in possible)
            if depth < 4:
                for b in possible.difference(wires):
                    following.add(tuple(sorted((*state, b))))
        states = following

    for x in range(16):
        a,b,c,d = (bool(x & (1 << j)) for j in range(4))
        seven = ((a and b) and (c or d)) or ((c and d) and (a or b))
        assert seven == (bin(x).count("1") >= 3)
    print("No six-gate circuit separates the layers. Seven suffice on all sixteen inputs.")


if __name__ == "__main__":
    main()
