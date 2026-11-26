"""Exact minimum for the one-on-each-side circuit on graph mask 1275."""
from itertools import combinations

TARGET = 1275
CELLS = range(15)
RAW = tuple(sum(1 << cell for cell in CELLS
                if pin in (cell // 5, 3 + cell % 5))
            for pin in range(8))
FALLS = tuple((a, b) for a in CELLS if TARGET >> a & 1
              for b in CELLS if not (TARGET >> b & 1))


def possible(wires):
    """Every target decrease must also decrease at least one visible wire."""
    return all(any(w >> a & 1 and not (w >> b & 1) for w in wires)
               for a, b in FALLS)


def verify():
    r0, r1, _, c0, c1, c2, c3, c4 = RAW
    assert TARGET == c0 | (r1 & (c1 | c2)) | (r0 & (c1 | (c3 | c4)))
    essential = [i for i in range(8) if not possible(RAW[:i] + RAW[i + 1:])]
    assert essential == [0, 1, 3, 4, 5, 6, 7]

    # With seven essential raw wires and only six gates, the live cone must
    # be a binary tree. A bottom-up step consumes its two children permanently.
    frontier = {tuple(sorted(RAW[i] for i in essential))}
    counts = []
    while frontier:
        following = set()
        for wires in frontier:
            for i, j in combinations(range(len(wires)), 2):
                rest = [w for k, w in enumerate(wires) if k not in (i, j)]
                for joined in (wires[i] & wires[j], wires[i] | wires[j]):
                    candidate = tuple(sorted(rest + [joined]))
                    if possible(candidate):
                        following.add(candidate)
        counts.append(len(following))
        frontier = following
    assert counts == [4, 4, 1, 0]
    print("Seven gates suffice. Live read-once frontiers:", counts)


if __name__ == "__main__":
    verify()
