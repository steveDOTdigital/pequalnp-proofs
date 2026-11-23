"""Search the nonedge AND case with one NOT applied to that first gate."""

import argparse
from pathlib import Path
from runpy import run_path
import subprocess


HERE = Path(__file__).parent
PETERSEN = run_path(str(HERE / "search-petersen-one-not.py"))
Formula = run_path(str(HERE / "search-three-matchings.py"))["Formula"]
EDGES = PETERSEN["EDGES"]


def flag(x):
    return (x & 5) == 5


def active(x):
    return any((x >> u) & (x >> v) & 1 for u, v in EDGES)


def boundary():
    rows = []
    for x in range(1024):
        value = active(x)
        # The output is monotone within each fixed-flag slice. In this
        # order interval between comparable points every point has that flag.
        neighbors = [x ^ (1 << i) for i in range(10) if bool(x & (1 << i)) == value]
        if not any(flag(y) == flag(x) and active(y) == value for y in neighbors):
            rows.append(x)
    return rows


def search(solver, seconds):
    tests = boundary()
    f = Formula()
    tables = []
    for j in range(12):
        table = f.vars(len(tests))
        tables.append(table)
        for var, x in zip(table, tests):
            value = (x >> j) & 1 if j < 10 else flag(x) == (j == 10)
            f.clauses.append([var if value else -var])
    choices = []
    for _ in range(17):
        left, right = (f.one_of(len(tables)) for _ in range(2))
        ports = []
        for selectors in (left, right):
            port = f.vars(len(tests))
            ports.append(port)
            for sel, table in zip(selectors, tables):
                for val, src in zip(port, table):
                    f.clauses.extend(([-sel, -val, src], [-sel, val, -src]))
        for i, sel in enumerate(left):
            f.clauses.extend([-sel, -smaller] for smaller in right[:i])
        if choices:
            # Sort independent gates by larger operand, then smaller.
            _, prev_l, prev_r = choices[-1]
            equal = f.vars(1)[0]
            for i, prev in enumerate(prev_r):
                f.clauses.extend([-prev, -smaller] for smaller in right[:i])
                f.clauses.append([-prev, -right[i], equal])
            for i, prev in enumerate(prev_l):
                f.clauses.extend([-equal, -prev, -smaller] for smaller in left[:i])
        is_or = f.vars(1)[0]
        out = f.vars(len(tests))
        for a,b,y in zip(*ports, out):
            f.clauses.extend(([is_or,-y,a], [is_or,-y,b], [is_or,y,-a,-b],
                              [-is_or,y,-a], [-is_or,y,-b], [-is_or,-y,a,b]))
        tables.append(out)
        choices.append((is_or,left,right))
    for j, _ in enumerate(choices[:-1]):
        wire = 12+j
        f.clauses.append([port[wire] for _,l,r in choices[j+1:] for port in (l,r)])
    for y,x in zip(tables[-1],tests):
        f.clauses.append([y if active(x) else -y])
    print(f"{len(tests)} boundary rows; {f.count} variables; {len(f.clauses)} clauses", flush=True)
    res = subprocess.run([solver, "-q", "--check", "--checkproof=2", "-t", str(seconds)],
                         input=f.dimacs(), text=True, capture_output=True, timeout=seconds+20)
    if res.returncode == 10 and "s SATISFIABLE" in res.stdout:
        model = {int(z) for line in res.stdout.splitlines() if line.startswith("v ")
                 for z in line.split()[1:]}
        gates = [("and",0,2), ("not",10,10)]
        for is_or,left,right in choices:
            a,b = (next(i for i,v in enumerate(port) if v in model) for port in (left,right))
            gates.append(("or" if is_or in model else "and",a,b))
        assert PETERSEN["run"](gates,PETERSEN["INPUTS"])[-1] == PETERSEN["TARGET"]
        print("Verified on all 1,024 inputs:", gates)
    elif res.returncode == 20 and "s UNSATISFIABLE" in res.stdout:
        print("UNSAT")
    elif res.returncode == 0 and "UNKNOWN" in res.stdout:
        print("UNKNOWN")
    else:
        raise RuntimeError((res.returncode,res.stderr[-300:]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver")
    parser.add_argument("--seconds", type=int, default=120)
    opts = parser.parse_args()
    search(opts.solver,opts.seconds)
