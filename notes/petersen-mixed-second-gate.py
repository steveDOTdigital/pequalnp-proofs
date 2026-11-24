"""Count source occurrences required after cutting a single shared binary signal.

Represent all 512 truth-table rows by a Python integer. Leaf inversions and the
sign of the cut wire are free. Each gate in its tree has two signed operands.
"""
from functools import lru_cache
from itertools import product
from pathlib import Path
import subprocess
import tempfile

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
FULL = (1 << 512) - 1
RAW = [sum(1 << r for r in range(512) if (r >> i) & 1) for i in range(9)]
GRAPH = 0
for a,b in EDGES:
    GRAPH |= RAW[a] & RAW[b]


def cardinal(mask):
    return bin(mask).count("1")


ORDER = sorted(range(512), key=cardinal)


@lru_cache(None)
def cover(active):
    return next(cardinal(s) for s in ORDER if all(
        (not (active >> k) & 1) or s & ((1 << i) | (1 << j))
        for k,(i,j) in enumerate(EDGES)))


def row_tests(u):
    essential = []
    corners = []
    for i in range(9):
        step = 1 << i
        essential.append(~RAW[i] & (GRAPH ^ (GRAPH >> step)) & ~(u ^ (u >> step)))
    for i,j in EDGES:
        p,q = 1 << i, 1 << j
        base = FULL & ~RAW[i] & ~RAW[j] & ~GRAPH & (GRAPH >> (p+q))
        base &= ~(u ^ (u >> p)) & ~(u ^ (u >> q)) & ~(u ^ (u >> (p+q)))
        corners.append((base & ~(GRAPH >> p) & ~(GRAPH >> q), base & (GRAPH >> p) & (GRAPH >> q)))
    return essential, corners


def forced(h, tests):
    singles, corners = tests
    essential = sum(bool(s & ~(h ^ (h >> (1 << i)))) for i,s in enumerate(singles))
    edges = 0
    for k,((i,j),(conj,disj)) in enumerate(zip(EDGES,corners)):
        p,q = 1 << i, 1 << j
        fixed = ~(h ^ (h >> p)) & ~(h ^ (h >> q)) & ~(h ^ (h >> (p+q)))
        if conj & fixed and disj & fixed:
            edges |= 1 << k
    return essential, edges


def canonical(h):
    return h ^ FULL if h & 1 else h


def append_level(levels):
    # Every binary tree has two smaller child trees, including single leaves.
    d = len(levels)
    new = {}
    for i in range((d-1)//2+1):
        j = d-1-i
        for p, raw_p in levels[i].items():
            for q, raw_q in levels[j].items():
                if i == j and q <= p:
                    continue
                for a,b in product((p,p^FULL),(q,q^FULL)):
                    h = canonical(a & b)
                    if h and not any(h in prior for prior in levels):
                        new[h] = new.get(h,False) or (raw_p and raw_q)
    return new


def tight_case(h, u, q, use_u, tests, edges, repeats, budget, rectangle):
    """At equality only essential raw labels and a minimum repeated cover fit."""
    singles, _ = tests
    mask = sum(1 << i for i,t in enumerate(singles) if t & ~(h ^ (h >> (1 << i))))
    targets = {}
    for row in range(512):
        key = (row & mask, (h >> row) & 1, ((u >> row) & 1) if use_u else 0)
        target = (GRAPH >> row) & 1
        if key in targets and targets[key] != target:
            return False
        targets[key] = target

    for reps in ORDER:
        if cardinal(reps) != repeats:
            continue
        if any((edges >> k) & 1 and not reps & ((1 << i) | (1 << j))
               for k,(i,j) in enumerate(EDGES)):
            continue
        # A raw label used once must be positive: independent essentiality
        # supplies a fixed-helper cofactor where the graph is strictly increasing.
        bits = "".join(str((h >> r) & 1) for r in range(512))
        args = [str(rectangle),str(2 | (1 << q)),str(mask),str(reps),bits]
        cost = int(subprocess.check_output(args,text=True))
        if cost <= budget:
            return True
    return False


def check(q, maximum, rectangle):
    u = RAW[1] | RAW[q]
    tests = (row_tests(0), row_tests(u))
    # Tables are canonical up to complementation. The flag records whether a
    # cheapest generating tree uses raw labels only.
    levels = [dict([(s,True) for s in RAW]+[(u,False)])]
    for gates in range(1,maximum+1):
        levels.append(append_level(levels))
        budget = 14-gates
        tight = remaining = 0
        for h, raw in levels[-1].items():
            for use_u in (False,True):
                e,edges = forced(h,tests[use_u])
                c = cover(edges)
                # Substituting the cut tree adds at most gates leaves per copy.
                baseline = 17 if raw and not use_u else 16
                copies = (baseline-budget+gates-1)//gates
                bound = e+c+copies+int(use_u)
                if bound < budget:
                    remaining += 1
                elif bound == budget:
                    tight += 1
                    remaining += tight_case(h,u,q,use_u,tests[use_u],edges,c,budget,rectangle)
        print("pair 1",q,"cut gates",gates,"residual budget",budget,
              "signed functions",len(levels[-1]),"tight modes",tight,"remaining",remaining,flush=True)
        if remaining:
            raise AssertionError("Some cut functions remain")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="pnp-cut-") as tmp:
        rectangle = Path(tmp)/"rectangle"
        source = Path(__file__).with_name("petersen-mixed-rectangles.cpp")
        subprocess.run(["c++","-std=c++20","-O3",str(source),"-o",str(rectangle)],check=True)
        for q in (2,3,8):
            check(q,4,rectangle)
