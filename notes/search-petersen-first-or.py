"""Bounded exact synthesis after OR(0,2), allowing AND, OR and NOT throughout."""

import argparse
import subprocess
from pathlib import Path
from runpy import run_path
from time import monotonic


HERE = Path(__file__).parent
Formula = run_path(str(HERE / "search-three-matchings.py"))["Formula"]
PETERSEN = run_path(str(HERE / "search-petersen-one-not.py"))
TARGET = PETERSEN["TARGET"]


def boundary():
    rows = []
    for x in range(1024):
        value = (TARGET >> x) & 1
        flag = bool(x & 5)
        neighbors = [x ^ (1 << i) for i in range(10) if (x >> i) & 1 == value]
        if not any(bool(y & 5) == flag and (TARGET >> y) & 1 == value for y in neighbors):
            rows.append(x)
    return rows


def instance(rows, budget):
    f = Formula()
    tables = []
    for j in range(11):
        table = f.vars(len(rows))
        for v, x in zip(table, rows):
            bit = (x >> j) & 1 if j < 10 else bool(x & 5)
            f.clauses.append([v if bit else -v])
        tables.append(table)
    choices = []
    for _ in range(budget - 1):
        ops = f.one_of(3)
        left, right = (f.one_of(len(tables)) for _ in range(2))
        for i, a in enumerate(left):
            f.clauses.extend([-a, -b] for b in right[:i])
            # A NOT reads only its first operand. Use two equal ports.
            f.clauses.append([-ops[2], -a, right[i]])
        if choices:
            _, last_left, last_right = choices[-1]
            equal = f.vars(1)[0]
            for i, r in enumerate(last_right):
                f.clauses.extend([-r, -s] for s in right[:i])
                f.clauses.append([-r, -right[i], equal])
            for i, l in enumerate(last_left):
                f.clauses.extend([-equal, -l, -s] for s in left[:i])
        ports = []
        for selectors in (left, right):
            port = f.vars(len(rows))
            for sel, table in zip(selectors, tables):
                for bit, v in zip(port, table):
                    f.clauses.extend(([-sel, -bit, v], [-sel, bit, -v]))
            ports.append(port)
        out = f.vars(len(rows))
        for a, b, y in zip(*ports, out):
            f.clauses.extend(([-ops[0], -y, a], [-ops[0], -y, b], [-ops[0], y, -a, -b],
                              [-ops[1], y, -a], [-ops[1], y, -b], [-ops[1], -y, a, b],
                              [-ops[2], y, a], [-ops[2], -y, -a]))
        tables.append(out)
        choices.append((ops, left, right))
    for y, x in zip(tables[-1], rows):
        f.clauses.append([y if TARGET & (1 << x) else -y])
    return f, choices


def search(solver, budget, seconds):
    rows = boundary()
    deadline = monotonic() + seconds
    while monotonic() < deadline:
        f, choices = instance(rows, budget)
        left = max(1, int(deadline - monotonic()))
        print(f"{len(rows)} test inputs, {f.count} variables, {len(f.clauses)} clauses",
              flush=True)
        proc = subprocess.run([solver, "-q", "--check", "--checkproof=2", "-t", str(left)],
                              input=f.dimacs(), text=True, capture_output=True, timeout=left+20)
        if proc.returncode == 20 and "s UNSATISFIABLE" in proc.stdout:
            return "UNSAT"
        if proc.returncode == 0 and "UNKNOWN" in proc.stdout:
            return "UNKNOWN"
        if proc.returncode != 10 or "s SATISFIABLE" not in proc.stdout:
            raise RuntimeError((proc.returncode, proc.stderr[-300:]))
        model = {int(v) for line in proc.stdout.splitlines() if line.startswith("v ")
                 for v in line.split()[1:]}
        gates = [("or", 0, 2)]
        for choice in choices:
            op, a, b = [next(i for i, v in enumerate(port) if v in model) for port in choice]
            gates.append((("and", "or", "not")[op], a, b))
        values = PETERSEN["run"](gates, PETERSEN["INPUTS"])[-1]
        diff = values ^ TARGET
        if not diff:
            print("Verified on all 1,024 inputs:", gates)
            return "SAT"
        assert all(not (diff >> x & 1) for x in rows)
        # Add counterexamples spread across the ordered truth table.
        wrong = [x for x in range(1024) if diff >> x & 1]
        rows.extend(wrong[::max(1, len(wrong)//12)][:12])
    return "UNKNOWN"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("--budget", type=int, choices=range(2, 21), default=19)
    parser.add_argument("--seconds", type=int, default=120)
    args = parser.parse_args()
    print(search(args.solver, args.budget, args.seconds), flush=True)
