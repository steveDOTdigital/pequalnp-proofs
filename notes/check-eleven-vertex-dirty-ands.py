"""Check AND-gate lower bounds for range 19 of L-meta-1343 with unrestricted OR gates."""
from itertools import combinations
from pathlib import Path
from runpy import run_path
import subprocess
import sys

Formula = run_path(str(Path(__file__).with_name("check-nine-vertex-internal-gates.py")))["Formula"]
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
EDGE_MASKS = [(1 << u) | (1 << v) for u, v in EDGES]
ANCHOR = sum(1 << x for x in (0, 1, 3, 5))


def positive(point):
    return any(point & edge == edge for edge in EDGE_MASKS)


NEGATIVES = [p for p in range(2048) if not positive(p) and
             all(positive(p | (1 << i)) for i in range(11) if not p >> i & 1)]
assert len(NEGATIVES) == 24 and ANCHOR in NEGATIVES


def problem(count, dirty):
    f = Formula()
    sides = []
    for i in range(count):
        arity = 12 + min(i, dirty)
        left, right = [[f.fresh() for _ in range(arity)] for _ in range(2)]
        sides.append((left, right))
        f.lex_order(left, right)
        if i < dirty:
            continue
        # A useful clean terminal needs disjoint nonempty operands. Each raw
        # cross-pair from its two operands must be an edge.
        f.clauses.extend(([-left[0]], [-right[0]], left, right))
        f.clauses.extend([-a, -b] for a, b in zip(left, right))
        for u in range(11):
            for v in range(11):
                if ((1 << u) | (1 << v)) not in EDGE_MASKS:
                    f.clauses.append([-left[1+u], -right[1+v]])
        if i > dirty:
            a, b = sides[i-1]
            f.lex_order(a+b, left+right)

    negative_values = [[] for _ in range(dirty)]
    for p in NEGATIVES + EDGE_MASKS:
        values = []
        for left, right in sides:
            ports = []
            for selected in (left, right):
                # Source zero is constant true. An empty disjunction is false.
                active = [selected[0]]
                active.extend(selected[1+v] for v in range(11) if p >> v & 1)
                active.extend(f.both(sel, bit) for sel, bit in zip(selected[12:], values))
                ports.append(f.any_of(active))
            values.append(f.both(*ports))
        if p in NEGATIVES:
            f.clauses.extend([-v] for v in values[dirty:])
            for i in range(dirty):
                negative_values[i].append(values[i])
            if p == ANCHOR:
                f.clauses.append(values[:dirty])
        else:
            f.clauses.append(values[dirty:])
    f.clauses.extend(negative_values)
    return f, sides


def fixed_control(f, sides):
    cover = next(c for k in range(12) for c in combinations(range(11), k)
                 if all(a in c or b in c for a, b in EDGES))
    assert len(cover) == 7
    groups = {v: [] for v in cover}
    for a, b in EDGES:
        root = a if a in groups else b
        groups[root].append(b if root == a else a)

    def ordered(i, left, right):
        def vector(raw):
            return tuple(int(j-1 in raw) for j in range(12+min(i, 2)))
        return sorted((vector(left), vector(right)))
    settings = [ordered(0, [0], [1]), ordered(1, [3], [5])]
    settings.extend(sorted(ordered(2, [v], nbrs) for v, nbrs in groups.items()))
    for ports, pair in zip(sides, settings):
        for variables, bits in zip(ports, pair):
            f.clauses.extend([var if bit else -var] for var, bit in zip(variables, bits))
    for p in range(2048):
        answer = any(p >> v & 1 and any(p >> u & 1 for u in nbrs)
                     for v, nbrs in groups.items())
        assert answer == positive(p)


def check_witness():
    # Raw wires are numbered 0 through 10. Each entry appends its gate output.
    gates = [
        ("or", 7, 10), ("or", 6, 9), ("and", 11, 12),
        ("or", 1, 4), ("or", 14, 9), ("or", 0, 8), ("and", 15, 16),
        ("and", 10, 0),
        ("or", 8, 9), ("or", 5, 17), ("and", 19, 20),
        ("or", 6, 7), ("or", 3, 13), ("and", 22, 23),
        ("or", 5, 10), ("and", 25, 2),
        ("or", 1, 10), ("and", 27, 4),
        ("or", 18, 21), ("or", 29, 24), ("or", 30, 26), ("or", 31, 28),
    ]
    assert len(gates) == 22 and sum(op == "and" for op, _, _ in gates) == 7
    dirty = set()
    anchored = set()
    for mask in range(2048):
        values = [bool(mask >> j & 1) for j in range(11)]
        for i, (op, a, b) in enumerate(gates, start=11):
            val = values[a] and values[b] if op == "and" else values[a] or values[b]
            values.append(val)
            if op == "and" and val and not positive(mask):
                dirty.add(i)
                if mask == ANCHOR:
                    anchored.add(i)
        assert values[-1] == positive(mask)
    assert dirty == {13, 17} and anchored == {17}
    live = {32}
    for i in range(32, 10, -1):
        if i in live:
            _, a, b = gates[i-11]
            live.update((a, b))
    assert set(range(11, 33)) <= live
    print("22 gates, 7 ANDs, 2 dirty; verified on all 2,048 inputs", flush=True)


def run(solver, k, d, control=False):
    f, sides = problem(k, d)
    if control:
        fixed_control(f, sides)
    result = subprocess.run([solver, "-q", "--check", "-t", "120"], input=f.dimacs(),
                            text=True, stdout=subprocess.PIPE)
    expected = 10 if control else 20
    if result.returncode != expected:
        raise RuntimeError(f"{k} ANDs, {d} dirty: solver exit {result.returncode}")
    print(k, d, "SAT control" if control else "UNSAT", flush=True)


if __name__ == "__main__":
    solver = sys.argv[1] if len(sys.argv) > 1 else "cadical"
    check_witness()
    run(solver, 9, 2, control=True)
    for k, d in [(5, 2), (5, 3), (5, 4), (6, 2)]:
        run(solver, k, d)
