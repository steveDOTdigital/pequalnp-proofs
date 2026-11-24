"""Search a 3-line residual with fixed source wires and the exact restricted tests."""
import argparse
from itertools import combinations
from pathlib import Path
from runpy import run_path
import subprocess

arc = run_path(str(Path(__file__).with_name("plane-arc-tests.py")))


def search(lines, pairing, omitted, selected, budget, seconds):
    raw, helpers, pos, neg = arc["residual"](lines, arc["test_rows"](), pairing)
    pool = [1 << (13 + l) for l in lines]
    pool += [m for i, m in enumerate(raw) if not omitted >> i & 1]
    pool += [m for i, m in enumerate(helpers) if selected >> i & 1]
    tests = pos + neg
    clauses = []
    largest = 0

    def fresh():
        nonlocal largest
        largest += 1
        return largest

    def choose(n):
        variables = [fresh() for _ in range(n)]
        clauses.append(variables)
        clauses.extend([-a, -b] for a, b in combinations(variables, 2))
        return variables

    # Input columns hold constants. Every listed source must actually be read.
    tables = [[bool(mask & row) for row in tests] for mask in pool]
    gates = []
    for j in range(budget):
        left, right = choose(len(tables)), choose(len(tables))
        for k, sel in enumerate(left):
            clauses.extend([-sel, -y] for y in right[:k + 1])
        if gates:
            old_l, old_r, _ = gates[-1]
            for k, sel in enumerate(old_r):
                clauses.extend([-sel, -y] for y in right[:k])
                for h, old in enumerate(old_l):
                    clauses.extend([-sel, -right[k], -old, -new] for new in left[:h])
        ports = []
        for port in (left, right):
            vs = [fresh() for _ in tests]
            for sel, col in zip(port, tables):
                for value, v in zip(col, vs):
                    if isinstance(value, bool):
                        clauses.append([-sel, v if value else -v])
                    else:
                        clauses.extend(([-sel, -v, value], [-sel, v, -value]))
            ports.append(vs)
        is_or = fresh()
        out = [fresh() for _ in tests]
        for x, y, z in zip(*ports, out):
            clauses.extend(([is_or,-z,x],[is_or,-z,y],[is_or,z,-x,-y],
                            [-is_or,z,-x],[-is_or,z,-y],[-is_or,-z,x,y]))
        tables.append(out)
        gates.append((left, right, is_or))
    for i in range(len(tables)-1):
        uses = [s[i] for left,right,_ in gates for s in (left,right) if i < len(s)]
        clauses.append(uses)
        # For the read-once subcase, this also gives the solver binary implications.
        if len(pool) == budget+1:
            clauses.extend([-a,-b] for a,b in combinations(uses,2))
    clauses.extend([v if j < len(pos) else -v] for j,v in enumerate(tables[-1]))
    cnf = f"p cnf {largest} {len(clauses)}\n"+"".join(" ".join(map(str,c))+" 0\n" for c in clauses)
    solver = Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"bin/cadical"
    result = subprocess.run([str(solver),"-q","--check","--checkproof=2","-t",str(seconds)],
                            input=cnf,capture_output=True,text=True,timeout=seconds+20)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        return "UNSAT"
    if result.returncode == 0 and "UNKNOWN" in result.stdout:
        return "UNKNOWN"
    if result.returncode != 10 or "s SATISFIABLE" not in result.stdout:
        raise RuntimeError((result.returncode,result.stderr[-400:]))
    model = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
             for v in line.split()[1:]}
    witness = [(op in model,next(i for i,x in enumerate(l) if x in model),
                next(i for i,x in enumerate(r) if x in model)) for l,r,op in gates]
    for row in tests:
        vals = [bool(row & mask) for mask in pool]
        for is_or,a,b in witness:
            vals.append(vals[a] or vals[b] if is_or else vals[a] and vals[b])
        assert vals[-1] == (row in pos)
    return "SAT", pool, witness


if __name__ == "__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lines",nargs="+",type=int,default=[0,1,3])
    ap.add_argument("--pairing",type=int,default=0)
    ap.add_argument("--omitted",type=int,default=0)
    ap.add_argument("--helpers",type=int,default=0)
    ap.add_argument("--gates",type=int,default=13)
    ap.add_argument("--seconds",type=int,default=120)
    opt=ap.parse_args()
    print(search(opt.lines,opt.pairing,opt.omitted,opt.helpers,opt.gates,opt.seconds),flush=True)
