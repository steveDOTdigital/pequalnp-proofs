"""Search the Heawood edge function with free OR gates and a bounded number of ANDs.

Run from lean/ with python3 ../notes/heawood-and-budget.py K --seconds S.
A positive result is replayed on all raw inputs. The exact gate count allows padding.
"""
import argparse
from itertools import combinations
from pathlib import Path
import runpy
import subprocess


data = runpy.run_path(str(Path(__file__).with_name("heawood-first-gate-bound.py")))
N, EDGES = data["N"], data["EDGES"]


class CNF:
    def __init__(self):
        self.count = 0
        self.clauses = []

    def var(self):
        self.count += 1
        return self.count

    def meet(self, a, b):
        w = self.var()
        self.clauses.extend(([-w, a], [-w, b], [w, -a, -b]))
        return w

    def join(self, xs):
        w = self.var()
        self.clauses.extend([-v, w] for v in xs)
        self.clauses.append([-w] + xs)
        return w


def target(row):
    return any(row >> a & row >> b & 1 for a, b in EDGES)


def records():
    positive = [(1 << u) | (1 << v) for u, v in EDGES]
    negative = [r for r in range(1 << N) if not target(r) and
                all(target(r | (1 << i)) for i in range(N) if not r >> i & 1)]
    assert len(positive) == 21 and len(negative) == 37
    return positive, negative


def encode(k, control):
    c = CNF()
    # Each paid gate takes an AND of two arbitrary ORs of raw and earlier paid wires.
    gates = [([c.var() for _ in range(N+j)], [c.var() for _ in range(N+j)]) for j in range(k)]
    outputs = [c.var() for _ in range(k)]
    # No raw input can be included in the output OR (singleton test).
    c.clauses.append(outputs)
    if control:
        assert k == 7
        for j, (left, right) in enumerate(gates):
            c.clauses.append([outputs[j]])
            for i in range(N+j):
                c.clauses.append([left[i] if i == j else -left[i]])
                c.clauses.append([right[i] if (j,i) in EDGES else -right[i]])
    # At the first gate, bits common to both sides can be moved to any OR
    # reading its output: (A∨X)∧(B∨X) = X∨(A∧B). This holds at every gate.
    # Pure OR values, including constants, need no AND. Fewer gates can be
    # padded with unused dummy gates. Disjoint input sets are thus sufficient.
    for a, b in gates:
        c.clauses.extend([-x, -y] for x, y in zip(a, b))
        # Commutativity: put the smallest selected wire on the left.
        for i, y in enumerate(b):
            c.clauses.append([-y] + a[:i])
    pos, neg = records()
    for row in pos + neg:
        values = []
        for left, right in gates:
            ports = []
            for side in (left, right):
                # Raw wire values are known for this input; only a selected true
                # raw bit contributes. Earlier paid wires have SAT variables.
                active = [side[i] for i in range(N) if row >> i & 1]
                active.extend(c.meet(sel, value) for sel, value in zip(side[N:], values))
                ports.append(c.join(active))
            values.append(c.meet(*ports))
        out = c.join([c.meet(s, v) for s, v in zip(outputs, values)])
        c.clauses.append([out if row in pos else -out])
    return c, gates, outputs


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("budget", type=int)
    p.add_argument("--seconds", type=int, default=120)
    p.add_argument("--control", action="store_true")
    args = p.parse_args()
    c, gates, outputs = encode(args.budget, args.control)
    dimacs = f"p cnf {c.count} {len(c.clauses)}\n" + "".join(
        " ".join(map(str, clause)) + " 0\n" for clause in c.clauses)
    lean = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    result = subprocess.run([str(Path(lean)/"bin/cadical"), "-q", "--check", "--checkproof=2",
                             "-t", str(args.seconds)], input=dimacs, capture_output=True,
                            text=True, timeout=args.seconds+15)
    print(args.budget, "ANDs;", c.count, "variables,", len(c.clauses), "clauses.")
    if result.returncode == 20:
        assert "s UNSATISFIABLE" in result.stdout
        print("Proof-checked UNSAT.")
    elif result.returncode == 10:
        model = {int(s) for ln in result.stdout.splitlines() if ln.startswith("v ")
                 for s in ln.split()[1:] if int(s) > 0}
        ports = [([i for i, x in enumerate(a) if x in model],
                  [i for i, x in enumerate(b) if x in model]) for a, b in gates]
        final = [j for j, x in enumerate(outputs) if x in model]
        for row in range(1 << N):
            values = [bool(row >> i & 1) for i in range(N)]
            for a, b in ports:
                values.append(any(values[i] for i in a) and any(values[i] for i in b))
            assert any(values[N+j] for j in final) == target(row)
        print("SAT, validated on all 16,384 rows.", ports, final)
    elif result.returncode == 0:
        print("Time limit; inconclusive.")
    else:
        raise RuntimeError(result.stderr)


if __name__ == "__main__":
    main()
