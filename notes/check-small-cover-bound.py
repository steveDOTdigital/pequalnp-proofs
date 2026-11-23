"""Exact monotone circuit search for the small cases of L-meta-612.

The true test inputs are the edges. The false test inputs are all maximal
independent sets. These determine the function on the full Boolean cube by
monotonicity. The program emits no files and reports timeouts separately.

With --bowtie, all singleton inputs are also present. The search excludes
each possible gate count from one through nine at weighted cost at most nine.
Zero gates cannot compute this edge function. Cost ten is attained by
ORing three terms: x0 AND (x1 OR x2 OR x3 OR x4), x1 AND x2, x3 AND x4.
Its three AND gates, three wide OR gates and two narrow OR gates cost ten.

Invalid wire indices and empty/unary gates in the project's circuit model
do not extend the search. Propagate constants and bypass copies before
sorting and discarding dead gates. Retained gates keep the same function,
including their values on singleton inputs, so weight cannot increase.
"""

import argparse
import subprocess
from itertools import combinations, permutations


def representatives(n):
    pairs = list(combinations(range(n), 2))
    symmetries = [[1 << pairs.index(tuple(sorted((p[u], p[v])))) for u, v in pairs]
                  for p in permutations(range(n))]
    seen = set()
    for mask in range(1, 1 << len(pairs)):
        if mask in seen:
            continue
        bits = [i for i in range(len(pairs)) if mask & (1 << i)]
        edges = [pairs[i] for i in bits]
        orbit = {sum(perm[i] for i in bits) for perm in symmetries}
        seen.update(orbit)
        neighbors = [{w for edge in edges if v in edge for w in edge if w != v}
                     for v in range(n)]
        if all(neighbors) and all(len(a & b) <= 1 for a, b in combinations(neighbors, 2)):
            yield edges, len(orbit)


def search(n, edges, solver, seconds, budget=None, weight_limit=None, first_gate=None):
    positives = [(1 << a) | (1 << b) for a, b in edges]
    independent = {x for x in range(1 << n) if all(x & e != e for e in positives)}
    negatives = sorted(x for x in independent if all(
        x & (1 << v) or (x | (1 << v)) not in independent for v in range(n)))
    if weight_limit is not None:
        negatives = sorted(set(negatives) | {1 << v for v in range(n)})
    cover = n - max(bin(x).count("1") for x in independent)
    if budget is None:
        budget = len(edges) + cover - 2
    tests = positives + negatives
    target = [x in positives for x in tests]
    edge_set = set(edges)
    autos = [p for p in permutations(range(n))
             if all(tuple(sorted((p[a], p[b]))) in edge_set for a, b in edges)]
    def first_allowed(a, b):
        # Select the least possible first pair over all relabelings and
        # compatible sorted circuit orders. Identity gates can be omitted.
        return a != b and all((b, a) <= (max(p[a], p[b]), min(p[a], p[b])) for p in autos)
    # A zero-gate nonconstant output would be a single input.
    if budget == 0:
        assert all([bool(x & (1 << i)) for x in tests] != target for i in range(n))
        return "UNSAT"
    count = 0
    clauses = []

    def fresh():
        nonlocal count
        count += 1
        return count

    tables = [[fresh() for _ in tests] for _ in range(n)]
    for i, table in enumerate(tables):
        for x, y in zip(tests, table):
            clauses.append([y if x & (1 << i) else -y])
    previous = []
    instructions = []
    narrow = []
    for _ in range(budget):
        out = [fresh() for _ in tests]
        choices = []
        order = []
        if weight_limit is not None:
            is_or = fresh()
            narrow.append(fresh())
            singleton = [out[tests.index(1 << v)] for v in range(n)]
            for i in range(n):
                clauses.append([-is_or, narrow[-1], *singleton[:i], *singleton[i + 1:]])
        for b in range(len(tables)):
            for a in range(b + 1):
                k = len(order)
                order.append(fresh())
                if k:
                    clauses.append([-order[k], order[k - 1]])
                if not instructions and not first_allowed(a, b):
                    continue
                for op in ("AND", "OR"):
                    if not instructions and first_gate is not None and (op, a, b) != first_gate:
                        continue
                    selector = fresh()
                    choices.append((selector, op, a, b))
                    clauses.append([-selector, order[k]])
                    if weight_limit is not None and op == "OR":
                        clauses.append([-selector, is_or])
                    if k + 1 < len(previous):
                        clauses.append([-selector, -previous[k + 1]])
                    for u, v, y in zip(tables[a], tables[b], out):
                        if op == "AND":
                            clauses.extend(([-selector, -y, u], [-selector, -y, v],
                                            [-selector, y, -u, -v]))
                        else:
                            clauses.extend(([-selector, y, -u], [-selector, y, -v],
                                            [-selector, -y, u, v]))
        # At least one choice suffices: every selected instruction imposes
        # the same output truth table. Topologically sort by the larger
        # source index, then smaller. Padding can copy the last output.
        clauses.append([s for s, _, _, _ in choices])
        previous = order
        tables.append(out)
        instructions.append(choices)
    for i in range(len(instructions) - 1):
        wire = n + i
        clauses.append([s for later in instructions[i + 1:] for s, _, a, b in later
                        if a == wire or b == wire])
    clauses.extend([y if b else -y] for y, b in zip(tables[-1], target))
    if weight_limit is not None:
        for too_many in combinations(narrow, weight_limit - budget + 1):
            clauses.append([-v for v in too_many])
    cnf = f"p cnf {count} {len(clauses)}\n" + "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in clauses)
    result = subprocess.run([solver, "-q", "--check", "--checkproof=2", "-t", str(seconds)],
                            input=cnf, text=True, capture_output=True, timeout=seconds + 15)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        return "UNSAT"
    if result.returncode == 10 and "s SATISFIABLE" in result.stdout:
        model = {int(w) for line in result.stdout.splitlines() if line.startswith("v ")
                 for w in line.split()[1:]}
        gates = [next((op, a, b) for s, op, a, b in group if s in model)
                 for group in instructions]
        for x in range(1 << n):
            wires = [bool(x & (1 << i)) for i in range(n)]
            for op, a, b in gates:
                wires.append(wires[a] and wires[b] if op == "AND" else wires[a] or wires[b])
            assert wires[-1] == (x not in independent)
        print("Counterexample", edges, gates, flush=True)
        return "SAT"
    if result.returncode == 0 and "UNKNOWN" in result.stdout:
        return "UNKNOWN"
    raise RuntimeError((result.returncode, result.stderr[-300:]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("--max-vertices", type=int, choices=range(2, 8), default=6)
    parser.add_argument("--seconds", type=int, default=15)
    parser.add_argument("--bowtie", action="store_true", help="test the weighted bound in L-meta-700")
    parser.add_argument("--prism", action="store_true", help="test the full nine-gate prism search in L-meta-741")
    parser.add_argument("--first", nargs=3, metavar=("OP", "A", "B"),
                        help="limit the prism search to a canonical first gate")
    options = parser.parse_args()
    if options.prism:
        prism = [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)]
        cut = None
        if options.first:
            op, a, b = options.first
            cut = (op, int(a), int(b))
            if op not in ("AND", "OR") or cut[1:] not in ((0, 1), (0, 3), (1, 3)):
                parser.error("the prism has three canonical pairs: (0,1), (0,3), (1,3)")
        print(search(6, prism, options.solver, options.seconds, budget=9, first_gate=cut), flush=True)
        raise SystemExit(0)
    if options.bowtie:
        bowtie = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]
        for k in range(1, 10):
            print(f"{k} gates with weight at most 9:",
                  search(5, bowtie, options.solver, options.seconds, k, 9), flush=True)
        raise SystemExit(0)
    for n in range(2, options.max_vertices + 1):
        counts = {}
        labeled = 0
        for edges, orbit in representatives(n):
            status = search(n, edges, options.solver, options.seconds)
            counts[status] = counts.get(status, 0) + 1
            labeled += orbit
            if status != "UNSAT":
                print(n, status, edges, flush=True)
        print(f"{n} nonisolated vertices: {counts}; {labeled} labeled graphs", flush=True)
