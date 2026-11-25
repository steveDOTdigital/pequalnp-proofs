"""Exhaust direct-reader profiles for the vertex deletion and the full Petersen graph.

Run from any directory with Python 3.9+, and a C++17 compiler.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
from pathlib import Path
import runpy
import subprocess
import tempfile

HERE = Path(__file__).parent.resolve()
old = runpy.run_path(str(HERE / "petersen-raw-prefix.py"))
full = runpy.run_path(str(HERE / "petersen-free-or-certificate.py"))
EDGES = full["EDGES"]
GROUP = tuple(full["automorphisms"]())
sizes = tuple(bin(x).count("1") for x in range(1024))


def bounds(n, monotone):
    active, leaves = [], []
    for mask in range(1 << n):
        es = [(a,b) for a,b in EDGES if mask >> a & mask >> b & 1]
        verts = sum(1 << i for i in range(n) if any(i in e for e in es))
        cover = min(sizes[s] for s in range(1 << n) if not s & ~verts and
                    all((s >> a | s >> b) & 1 for a,b in es))
        active.append(verts)
        leaves.append(len(es) + cover)
    circuit = {}
    for mask in range(1 << n):
        if mask in circuit:
            continue
        orbit = {sum(1 << p[i] for i in range(n) if mask >> i & 1) for p in GROUP}
        rep = min(orbit)
        labels = [i for i in range(10) if rep >> i & 1]
        if len(labels) == 10:
            floor = 18 if monotone else 17
        elif len(labels) == 9:
            floor = (16 if monotone else 15) if n == 10 else (15 if monotone else 14)
        elif monotone:
            floor = max(0, leaves[mask]-1)
        else:
            assert 9 not in labels
            floor = old["signed_bound"](labels)
        circuit.update((x, floor) for x in orbit)
    lower = [circuit[m] for m in range(1 << n)]
    if monotone:
        return leaves, lower
    formula = []
    for mask, vertices in enumerate(active):
        r = vertices
        best = leaves[mask]
        while r:
            other = vertices ^ r
            best = min(best, 3*sizes[r] + sizes[other ^ active[other]] + leaves[other])
            r = (r-1) & vertices
        if sizes[mask] == 9:
            best = max(best, 17)
        if sizes[mask] == 10:
            best = max(best, 20)
        formula.append(max(best, lower[mask]+1) if vertices else 0)
    return formula, lower


def problems(n, monotone, budget, seconds, floors, lower):
    all_vars = (1 << n)-1
    V = range(n)
    pairs = list(combinations(V, 2))
    es = sorted((a,b) for a,b in EDGES if b < n)
    group = [g[:n] for g in GROUP if set(g[:n]) == set(V)]
    zero = [lower[all_vars ^ (1 << v)] for v in V]
    high = []
    for v in V:
        neighbors = sum(1 << (b if a == v else a) for a,b in es if v in (a,b))
        graph_floor = lower[all_vars ^ (1 << v) ^ neighbors]
        high.append(graph_floor + sizes[neighbors] if graph_floor else sizes[neighbors]-1)
    # All vertices remain essential when any other variable is set to either
    # controlling value. A raw pair therefore uses two repeated variables.
    target = [any(r >> a & r >> b & 1 for a,b in es) for r in range(1 << n)]
    for a in V:
        for b in V:
            if a != b:
                assert all(any(target[r] != target[r | 1<<a] for r in range(1<<n)
                               if not (r>>a & 1) and (r>>b & 1) == k) for k in (0,1))
    counts_seen = set()
    assert max(budget-z for z in zero) <= 3
    for counts in product(*(range(1, min(3, budget-z)+1) for z in zero)):
        if counts in counts_seen or sum(counts) > budget:
            continue
        if any(sum(counts[v] for v in V if not (mask >> v & 1)) > budget - lower[mask]
               for mask in range(1 << n) if lower[mask]):
            continue
        counts_seen.update(tuple(counts[g[v]] for v in V) for g in group)
        stabilizer = [g for g in group if all(counts[g[v]] == counts[v] for v in V)]
        allowed = set()
        for a,b in pairs:
            if min(counts[a], counts[b]) < 2: continue
            for op in ((0,3) if monotone else range(4)):
                if monotone and op == 0 and (a,b) not in EDGES:
                    continue
                ca, cb = op & 1, op >> 1
                if (counts[a]+1 > budget-(high[a] if ca else zero[a]) or
                        counts[b]+1 > budget-(high[b] if cb else zero[b])):
                    continue
                allowed.add((op,a,b))
        def image(g, gate):
            op,a,b = gate
            if g[a] < g[b]: return op,g[a],g[b]
            return ((op&1)<<1) | (op>>1),g[b],g[a]
        while_first = set(allowed)
        while while_first:
            seed = min(while_first)
            while_first -= {image(g,seed) for g in stabilizer}
            encoded = sum((count-1) << (2*v) for v,count in enumerate(counts))
            data = [budget,seconds,len(es),encoded,*[(1<<a)|(1<<b) for a,b in es]]
            for v in V: data.extend((zero[v],high[v]))
            for a,b in pairs: data.extend((a,b,lower[all_vars ^ (1<<a) ^ (1<<b)]))
            data.extend((1,*seed,len(allowed)))
            for g in sorted(allowed): data.extend(g)
            data.extend(floors)
            data.extend(lower)
            data.extend((1,*seed))
            yield (encoded,seed), " ".join(map(str,data))+"\n"


def control(n, seconds, floors, lower, edges=None):
    """Construct and canonically schedule one optimal vertex-cover star formula."""
    all_vars = (1<<n)-1
    es = sorted((a,b) for a,b in (EDGES if edges is None else edges) if b < n)
    sizes = [bin(mask).count("1") for mask in range(1<<n)]
    cover = min((mask for mask in range(1<<n) if all((mask>>a | mask>>b)&1 for a,b in es)),
                key=lambda mask: (sizes[mask], mask))
    stars = {v: [] for v in range(n) if cover >> v & 1}
    for a,b in es:
        center = a if a in stars else b
        stars[center].append(b if center == a else a)
    original = []
    def gate(op, a, b):
        original.append((op,a,b))
        return n+len(original)-1
    def alternative(values):
        out = values[0]
        for v in values[1:]:
            out = gate(3,out,v)
        return out
    out = alternative([gate(0,p,alternative(qs)) for p,qs in stars.items()])
    counts = [sum(int(a==v)+int(b==v) for _,a,b in original) for v in range(n)]
    names = {i:i for i in range(n)}
    todo = dict(enumerate(original,n))
    fixed = []
    while todo:
        b,a,op,j = min((max(names[a],names[b]),min(names[a],names[b]),op,j)
                       for j,(op,a,b) in todo.items() if a in names and b in names)
        names[j]=n+len(fixed)
        fixed.append((op,a,b))
        del todo[j]
    assert names[out] == n+len(fixed)-1
    allowed = sorted({g for g in fixed if g[2] < n})
    pairs = list(combinations(range(n),2))
    data = [len(fixed),seconds,len(es),sum((x-1) << (2*v) for v,x in enumerate(counts))]
    data.extend((1<<a)|(1<<b) for a,b in es)
    for v in range(n):
        nb=sum(1<<(b if a==v else a) for a,b in es if v in (a,b))
        cost=lower[all_vars ^ (1<<v) ^ nb]
        data.extend((lower[all_vars^(1<<v)],cost+sizes[nb] if cost else sizes[nb]-1))
    for a,b in pairs:data.extend((a,b,lower[all_vars^(1<<a)^(1<<b)]))
    data.extend((1,*fixed[0],len(allowed)))
    for g in allowed:data.extend(g)
    data.extend(floors); data.extend(lower); data.append(len(fixed))
    for g in fixed:data.extend(g)
    return ' '.join(map(str,data))+'\n'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("width", type=int, choices=(9,10))
    ap.add_argument("--monotone", action="store_true")
    ap.add_argument("--free-raw", action="store_true", help="allow either sign of one raw input")
    ap.add_argument("--profile", type=int, action="append", help="limit the run to named raw profiles")
    ap.add_argument("--mixed-only", action="store_true", help="require use of both signs of the exceptional input")
    ap.add_argument("--control-only", action="store_true")
    ap.add_argument("--seconds", type=int, default=30)
    ap.add_argument("--workers", type=int, default=2)
    args = ap.parse_args()
    n = args.width
    budget = (15 if args.monotone else 14) if n == 9 else (18 if args.monotone else 17)
    if args.free_raw and args.monotone: ap.error("select one circuit model")
    if args.free_raw: budget = 15 if n == 9 else 18
    floors, lower = bounds(n, args.monotone)
    if args.free_raw and n == 10:
        # Depends on the completed nine-variable free-raw exclusion at 15.
        for mask in range(1<<n):
            if sizes[mask] == 9: lower[mask] = 16
    cases = list(problems(n,args.monotone,budget,args.seconds,floors,lower))
    if args.mixed_only and not args.free_raw: ap.error("mixed-only requires free-raw")
    if args.profile:
        cases = [case for case in cases if case[0][0] in args.profile]
        if not cases: ap.error("no matching profiles")
    print("Width",n,"budget",budget,"profile/first-gate cases",len(cases),flush=True)
    with tempfile.TemporaryDirectory(prefix="petersen-unary-profiles-") as temp:
        binary = Path(temp)/"check"
        subprocess.run(["c++","-O3","-std=c++17",f"-DWIDTH={n}","-DSIGNED_MODE=1",f"-DFREE_RAW_REQUIRED={int(args.mixed_only)}",
                        "-DPETERSEN_PAIR_MODE="+("4" if args.free_raw else "3" if args.monotone else "2"),
                        str(HERE/"petersen-raw-prefix.cpp"),"-o",str(binary)],check=True)
        if not args.mixed_only:
            positive = subprocess.run([str(binary)],input=control(n,args.seconds,floors,lower),
                                      capture_output=True,text=True,check=True)
            assert positive.stdout.splitlines()[-1].startswith("SAT "), positive.stdout
            print("Star positive control passed on every row.",flush=True)
        if args.control_only:
            return
        def run(case):
            tag, inputs = case
            result = subprocess.run([str(binary)],input=inputs,capture_output=True,text=True,
                                    check=True,timeout=args.seconds+30)
            lines = result.stdout.strip().splitlines()
            verdict, nodes = lines[-1].split()
            return tag,verdict,int(nodes),lines[:-1]
        totals = Counter()
        visited = 0
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for tag,verdict,nodes,gates in pool.map(run,cases):
                totals[verdict] += 1
                visited += nodes
                if verdict != "UNSAT":
                    print(tag,verdict,nodes,gates,flush=True)
        print("Outcomes",dict(totals),"prefixes",visited,flush=True)
    assert not Path(temp).exists()
    if totals != {"UNSAT":len(cases)}:
        raise SystemExit("The search is incomplete.")


if __name__ == "__main__":
    main()
