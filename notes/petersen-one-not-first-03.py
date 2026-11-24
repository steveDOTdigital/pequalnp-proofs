"""Search L-meta-2768 with one NOT, a prescribed first OR, and row refinement.

Run from lean/ with python3 ../notes/petersen-one-not-first-03.py --seconds 240.
An UNSAT result on even a subset of rows excludes the desk circuit. Timeouts are inconclusive.
"""
import argparse
from itertools import combinations
from pathlib import Path
import runpy
import subprocess
from time import monotonic


notes = Path(__file__).resolve().parent
graph = runpy.run_path(str(notes / "check-petersen-cofactors.py"))
synthesis = runpy.run_path(str(notes / "search-petersen-first-or.py"))
edges = graph["EDGES"]
rows_all = (1 << 512) - 1
inputs = [sum(1 << r for r in range(512) if r >> i & 1) for i in range(9)]
target = sum(1 << r for r in range(512) if graph["target"](r))


def seeds():
    rows = set()
    for r in range(512):
        val = graph["target"](r)
        for i in range(9):
            if bool(r & (1 << i)) == val and graph["target"](r ^ (1 << i)) == val:
                break
        else:
            rows.add(r)
    # Each of the five distinct functions of the two endpoints must be realized.
    representatives = {}
    for r in range(512):
        if r & 9:
            continue
        sig = tuple(graph["target"](r | m) for m in (0,1,8,9))
        representatives.setdefault(sig, r)
    assert len(representatives) == 5
    for r in representatives.values():
        rows.update(r | m for m in (0,1,8,9))
    return sorted(rows)


def control():
    # A minimum vertex cover gives a 16-gate positive example beginning with
    # the prescribed OR. Inserting a disconnected NOT gives exactly 17 gates.
    owners = (1, 2, 4, 5, 8)
    leaves = {v: [] for v in owners}
    for a, b in edges:
        c = a if a in leaves else b
        leaves[c].append(b if c == a else a)
    assert set(leaves[4]) == {0, 3}
    wires = inputs.copy()
    wires.append(inputs[0] | inputs[3])
    wires.append(rows_all ^ inputs[0])  # One syntactically valid unused NOT.
    terms = []
    for v in owners:
        if v == 4:
            neighbor = wires[9]
        else:
            ns = leaves[v]
            neighbor = inputs[ns[0]]
            for u in ns[1:]:
                neighbor |= inputs[u]
                wires.append(neighbor)
        wires.append(neighbor & inputs[v])
        terms.append(wires[-1])
    total = terms[0]
    for term in terms[1:]:
        total |= term
        wires.append(total)
    assert len(wires) == 9+17 and wires[-1] == target
    print("17-gate, single-NOT control verified on all 512 rows.", flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--seconds", type=int, default=240)
    args = p.parse_args()
    control()
    executable = Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"bin/cadical"
    base = inputs + [inputs[0] | inputs[3], 0, rows_all]
    rows = seeds()
    deadline = monotonic() + args.seconds
    while monotonic() < deadline:
        f, choices = synthesis["truth_instance"](rows, base, 14, target)
        inv = [ops[2] for ops, _, _ in choices]
        f.clauses.append(inv)
        f.clauses.extend([-a,-b] for a,b in combinations(inv,2))
        seconds = max(1,int(deadline-monotonic()))
        print(len(rows), "rows;", f.count, "variables;", len(f.clauses), "clauses.", flush=True)
        result = subprocess.run([str(executable),"-q","--check","--checkproof=2","-t",str(seconds)],
                                input=f.dimacs(),text=True,capture_output=True,timeout=seconds+15)
        if result.returncode == 20:
            assert "s UNSATISFIABLE" in result.stdout
            print("Proof-checked UNSAT."); return
        if result.returncode == 0:
            print("Time limit; inconclusive."); return
        if result.returncode != 10:
            raise RuntimeError(result.stderr)
        model = {int(v) for l in result.stdout.splitlines() if l.startswith("v ")
                 for v in l.split()[1:] if int(v) > 0}
        def chosen(xs):
            return next(i for i,v in enumerate(xs) if v in model)
        wires = base.copy()
        gates = []
        for ops, l, r in choices:
            op, a, b = chosen(ops), chosen(l), chosen(r)
            gates.append((op,a,b))
            wires.append((wires[a] & wires[b], wires[a] | wires[b], rows_all ^ wires[a])[op])
        wrong = wires[-1] ^ target
        assert all(not wrong >> r & 1 for r in rows)
        if not wrong:
            print("All-row model (two free constants, indices 10 and 11):",gates); return
        counter = [r for r in range(512) if wrong >> r & 1]
        rows = sorted(set(rows) | set(counter[::max(1,len(counter)//10)][:10]))
    print("Time limit; inconclusive.")


if __name__ == "__main__":
    main()
