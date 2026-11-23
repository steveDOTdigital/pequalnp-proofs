"""Check the residual nine-input cases for L-meta-955 with CaDiCaL on PATH."""

from collections import Counter
from itertools import combinations, groupby, permutations, product
from math import factorial, prod
import subprocess
import sys


def input_columns(core, n, order):
    """A column lists the rows containing a given input. Input names are immaterial."""
    return tuple(sorted(
        sum(1 << j for j, i in enumerate(order) if core[i] >> x & 1)
        for x in range(n)
    ))


def row_orders(core, n):
    degrees = [sum(s >> x & 1 for s in core) for x in range(n)]
    keys = [(s.bit_count(), tuple(sorted(degrees[x] for x in range(n) if s >> x & 1)))
            for s in core]
    groups = [tuple(indices) for _, indices in
              groupby(sorted(range(len(core)), key=keys.__getitem__), keys.__getitem__)]
    return (sum(blocks, ()) for blocks in product(*(permutations(g) for g in groups)))


def canonical(core, n):
    return min(input_columns(core, n, order) for order in row_orders(core, n))


def orbit_size(core, n):
    orders = row_orders(core, n)
    base = input_columns(core, n, next(orders))
    row_symmetries = 1 + sum(input_columns(core, n, order) == base for order in orders)
    column_symmetries = prod(factorial(k) for k in Counter(base).values())
    return factorial(n) // (row_symmetries * column_symmetries)


def surviving_cores(n):
    """Extend representatives by one row, keeping every isomorphism type once."""
    masks = {k: [sum(1 << x for x in points) for points in combinations(range(n), k)]
             for k in range(3, n + 1)}
    seen = set()

    def extend(core, largest_allowed, excess):
        key = len(core), canonical(core, n)
        if key in seen:
            return
        seen.add(key)
        if excess >= 3 and sum(s.bit_count() - 2 for s in core[1:]) > 1:
            yield core
        for k in range(largest_allowed, 2, -1):
            if k == 3 and excess < 3:
                break
            for row in masks[k]:
                if all((row & other).bit_count() <= 1 for other in core):
                    yield from extend(core + (row,), k, excess + k - 3)
    yield from extend((), n, 0)


def connectivity_excludes(core):
    budget = sum(s.bit_count() - 1 for s in core)
    for size in range(1, len(core) + 1):
        for retained in combinations(core, size):
            components = []
            for row in retained:
                touching = [part for part in components if part & row]
                for part in touching:
                    components.remove(part)
                    row |= part
                components.append(row)
            merges = sum(part.bit_count() - 1 for part in components)
            if len(core) - size + merges + 1 >= budget:
                return True
    return False


class Formula:
    """Literal 1 is permanently true. Its negation represents false."""
    def __init__(self):
        self.count = 1
        self.clauses = [[1]]

    def fresh(self):
        self.count += 1
        return self.count

    def put(self, *literals):
        if 1 in literals:
            return
        clause = set(literals) - {-1}
        if not any(-x in clause for x in clause):
            self.clauses.append(sorted(clause))

    def dimacs(self):
        lines = [f"p cnf {self.count} {len(self.clauses)}"]
        lines.extend(" ".join(map(str, row)) + " 0" for row in self.clauses)
        return ("\n".join(lines) + "\n").encode()


def encode(core, n, spares):
    f = Formula()
    full = (1 << n) - 1
    points = sorted({0, full, *(1 << i for i in range(n)), *(full ^ row for row in core)})

    def target(row):
        return [1 if row & point else -1 for point in points]

    gates = ["h"] + [f"w{i}" for i in range(spares)]
    for i in range(len(core)):
        gates.extend((f"a{i}", f"t{i}"))
    before = {}
    for a, b in combinations(gates, 2):
        order = f.fresh()
        before[a, b], before[b, a] = order, -order
    for a, b, c in permutations(gates, 3):
        f.put(-before[a, b], -before[b, c], before[a, c])

    wires = {"zero": [-1] * len(points), "one": [1] * len(points)}
    for i in range(n):
        wires[f"x{i}"] = target(1 << i)
    for i, j in combinations(range(n), 2):
        pair = (1 << i) | (1 << j)
        if all(row & pair != pair for row in core):
            wires[f"p{i}_{j}"] = target(pair)
    for gate in gates:
        wires[gate] = (target(core[int(gate[1:])]) if gate.startswith("t")
                       else [f.fresh() for _ in points])

    def choose(gate, options):
        bits = [f.fresh() for _ in points]
        selectors = {}
        for source in options:
            sel = selectors[source] = f.fresh()
            if source in gates:
                f.put(-sel, before[source, gate])
            for bit, value in zip(bits, wires[source]):
                f.put(-sel, -bit, value)
                f.put(-sel, bit, -value)
        # Multiple selected sources must agree at every sample. Any one works.
        f.put(*selectors.values())
        return bits, selectors

    for gate in gates:
        options = [name for name in wires if name != gate]
        if gate == "h":
            left, _ = choose(gate, options)
            for x, z in zip(left, wires[gate]):
                f.put(-z, -x)
                f.put(z, x)
            continue
        is_and = f.fresh()
        if gate.startswith("t"):
            i = int(gate[1:])
            row, helper = core[i], f"a{i}"
            f.put(before[helper, gate])
            left = wires[helper]
            right, _ = choose(gate, [b for b in options if b != helper])
            singletons = [left[points.index(1 << x)] for x in range(n) if row >> x & 1]
            # OR private parent covers two singletons. AND private parent is
            # false with all outside variables on.
            for j in range(len(singletons)):
                f.put(is_and, *singletons[:j], *singletons[j + 1:])
            f.put(-is_and, -left[points.index(full ^ row)])
        else:
            left, lhs = choose(gate, options)
            right, rhs = choose(gate, options)
            for j, larger in enumerate(options):
                for smaller in options[:j]:
                    f.put(-lhs[larger], -rhs[smaller])
        for x, y, z in zip(left, right, wires[gate]):
            f.put(-is_and, -z, x)
            f.put(-is_and, -z, y)
            f.put(-is_and, z, -x, -y)
            f.put(is_and, z, -x)
            f.put(is_and, z, -y)
            f.put(is_and, -z, x, y)
    return f


def solve(solver, formula):
    run = subprocess.run([solver, "-q", "--check", "-t", "60"], input=formula.dimacs(),
                         stdout=subprocess.PIPE)
    if run.returncode not in (10, 20):
        raise RuntimeError(f"solver exited with status {run.returncode}")
    return run.returncode == 10


if __name__ == "__main__":
    solver = sys.argv[1] if len(sys.argv) > 1 else "cadical"
    cores = list(surviving_cores(9))
    assert len(cores) == 15
    # Independently counted by extending all labelled families in descending row size.
    assert sum(orbit_size(c, 9) for c in cores) == 467145
    cases = [c for c in cores if not connectivity_excludes(c)]
    assert len(cases) == 8
    for core in cases:
        excess = sum(s.bit_count() - 3 for s in core)
        assert excess == 3
        # Strict saving leaves E-2 spare binary gates. With E spares the
        # separate monotone constructions fit, with the NOT unused.
        assert not solve(solver, encode(core, 9, excess - 2)), core
        assert solve(solver, encode(core, 9, excess)), core
        print(core, "excluded; positive control passed", flush=True)
