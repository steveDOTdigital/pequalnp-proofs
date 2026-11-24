"""Check small monotone Petersen restrictions with CaDiCaL and free-inversion lower bounds.

Run from the repository's lean directory, for example:
    python3 ../notes/check-petersen-monotone.py degree-two 10 --seconds 300

The CNF enumerates globally minimal circuits of exactly the requested size.
An UNSAT result excludes a minimum of that size. Check smaller possible minima
separately or apply the proved unrestricted lower bound. A timeout is inconclusive.
"""
import argparse
from itertools import combinations
from pathlib import Path
import runpy
import subprocess


notes = Path(__file__).resolve().parent
elimination = runpy.run_path(str(notes / "petersen-gate-elimination.py"))
original = elimination["checks"]["EDGES"]


class Clauses:
    def __init__(self):
        self.variables = 0
        self.clauses = []

    def variable(self):
        self.variables += 1
        return self.variables

    def one(self, count):
        choices = [self.variable() for _ in range(count)]
        self.clauses.append(choices)
        self.clauses.extend([-x, -y] for x, y in combinations(choices, 2))
        return choices

    def conjunction(self, x, y):
        result = self.variable()
        self.clauses.extend(([-result, x], [-result, y], [result, -x, -y]))
        return result

    def select(self, choices, wires):
        result = self.variable()
        for choice, value in zip(choices, wires):
            self.clauses.extend(([-choice, -value, result], [-choice, value, -result]))
        return result


def graph_data(labels):
    edges = [(labels.index(i), labels.index(j)) for i, j in original if i in labels and j in labels]
    table = tuple(any(row >> i & row >> j & 1 for i, j in edges) for row in range(1 << len(labels)))
    positive = [(1 << i) | (1 << j) for i, j in edges]
    negative = [row for row, hit in enumerate(table) if not hit and
                all(table[row | (1 << i)] for i in range(len(labels)) if not row & (1 << i))]
    return table, positive, negative


def encode(width, gates, table, positive, negative):
    cnf = Clauses()
    structure = []
    for j in range(gates):
        a, b, use_or = cnf.one(width+j), cnf.one(width+j), cnf.variable()
        structure.append((a, b, use_or))
        # Commutativity sorts each pair. A minimal binary gate has different inputs.
        for i, x in enumerate(a):
            cnf.clauses.extend([-x, -y] for y in b[:i+1])

    # Greedily topologically order by (larger operand, smaller operand).
    # A newly available gate's larger operand is the wire just produced.
    for (a0, b0, _), (a1, b1, _) in zip(structure, structure[1:]):
        for j, x in enumerate(b0):
            cnf.clauses.extend([-x, -y] for y in b1[:j])
            for k, u in enumerate(a0):
                cnf.clauses.extend([-x, -b1[j], -u, -v] for v in a1[:k])

    for v in range(width):
        cnf.clauses.append([port[v] for a, b, _ in structure for port in (a, b)])
    for j in range(gates-1):
        cnf.clauses.append([port[width+j] for a, b, _ in structure[j+1:] for port in (a, b)])

    for v in range(width):
        slices = [elimination["restrict"](table, v, value) for value in (0, 1)]
        assert all(len(set(s)) == 2 for s in slices)
        caps = [gates-elimination["lower"](s) for s in slices]
        readers, operators = [], []
        for a, b, use_or in structure:
            read = cnf.variable()
            readers.append(read)
            operators.append(use_or)
            cnf.clauses.extend(([-a[v], read], [-b[v], read], [-read, a[v], b[v]]))
        cap = min(caps)
        for subset in combinations(range(gates), cap+1):
            cnf.clauses.append([-readers[i] for i in subset])
        for count in range(1, cap+1):
            for subset in combinations(range(gates), count):
                absent = [-readers[j] for j in subset]
                for value, limit in enumerate(caps):
                    required = limit-count+1
                    if not 1 <= required <= min(2, count):
                        continue
                    for chosen in combinations(subset, required):
                        cnf.clauses.append(absent + [(-operators[j] if value else operators[j])
                                                     for j in chosen])

    evidence = [dict(p1=[], p2=[], n1=[], n2=[], on=[], off=[]) for _ in structure]
    for row in positive + negative:
        wires = [cnf.variable() for _ in range(width)]
        cnf.clauses.extend([w if row >> i & 1 else -w] for i, w in enumerate(wires))
        for (a, b, use_or), tests in zip(structure, evidence):
            left, right = cnf.select(a, wires), cnf.select(b, wires)
            out = cnf.variable()
            cnf.clauses.extend(([use_or, -out, left], [use_or, -out, right],
                                [use_or, out, -left, -right], [-use_or, out, -left],
                                [-use_or, out, -right], [-use_or, -out, left, right]))
            prefix = "p" if table[row] else "n"
            tests[prefix+"1"].append(cnf.conjunction(left, -right))
            tests[prefix+"2"].append(cnf.conjunction(-left, right))
            tests["on" if table[row] else "off"].append(out if table[row] else -out)
            wires.append(out)
        cnf.clauses.append([wires[-1] if table[row] else -wires[-1]])
    for (_, _, use_or), t in zip(structure, evidence):
        cnf.clauses.extend(([-use_or]+t["p1"], [-use_or]+t["p2"],
                            [use_or]+t["n1"], [use_or]+t["n2"], t["on"], t["off"]))
    return cnf, structure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph", choices=("degree-two", "theta"))
    parser.add_argument("gates", type=int)
    parser.add_argument("--seconds", type=int, default=300)
    args = parser.parse_args()
    labels = [0, 1, 2, 3, 5, 6, 7, 8] if args.graph == "degree-two" else [1, 2, 3, 5, 6, 7, 8]
    table, positive, negative = graph_data(labels)
    cnf, structure = encode(len(labels), args.gates, table, positive, negative)
    data = f"p cnf {cnf.variables} {len(cnf.clauses)}\n" + "".join(
        " ".join(map(str, clause))+" 0\n" for clause in cnf.clauses)
    solver = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin/cadical"
    print(args.graph, args.gates, "gates,", len(positive), "positive,", len(negative),
          "negative,", cnf.variables, "variables,", len(cnf.clauses), "clauses", flush=True)
    result = subprocess.run([str(solver), "-q", "--check", "--checkproof=2", "-t", str(args.seconds)],
                            input=data, capture_output=True, text=True, timeout=args.seconds+15)
    if result.returncode == 20:
        assert "s UNSATISFIABLE" in result.stdout
        print("UNSAT; minimum of this size excluded.")
    elif result.returncode == 10:
        model = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
                 for v in line.split()[1:] if int(v) > 0}
        def chosen(port):
            return next(i for i, variable in enumerate(port) if variable in model)
        gates = [(use_or in model, chosen(a), chosen(b)) for a, b, use_or in structure]
        for row, expected in enumerate(table):
            wires = [bool(row >> i & 1) for i in range(len(labels))]
            for use_or, a, b in gates:
                wires.append((wires[a] or wires[b]) if use_or else (wires[a] and wires[b]))
            assert wires[-1] == expected
        print("Verified witness (use_or, left, right):", gates)
    elif result.returncode == 0:
        print("Time limit. No conclusion.")
    else:
        raise RuntimeError(result.stderr)


if __name__ == "__main__":
    main()
