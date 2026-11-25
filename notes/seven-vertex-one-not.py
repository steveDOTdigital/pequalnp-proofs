"""Check signed circuit sizes for case 11088 and its triangular-prism deletion."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LIB = runpy.run_path(str(HERE / "heawood-high-cofactor.py"))
canonical = runpy.run_path(str(HERE / "nine-vertex-table-two.py"))["canonical"]
EDGES = [(0,3),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(2,5),(3,5),(0,6),(2,6),(3,6),(4,6)]
FULL = 127


def bits(s):
    return [v for v in range(7) if s & (1 << v)]


def rectangle_upper(n, edges):
    # A product of two raw ORs covers precisely the edges of a biclique.
    # Combine the products with OR. A rectangle with a+b vertices uses
    # a+b units before deducting the final output merge.
    sets = {(a,b): {(v,w) for v in bits(a) for w in bits(b)}
            for a in range(1,1<<n) for b in range(1,a) if not a & b}
    rectangles = {}
    for (a,b), pairs in sets.items():
        chosen = {tuple(sorted(e)) for e in pairs}
        if chosen <= set(edges):
            rectangles[sum(1 << edges.index(e) for e in chosen)] = len(bits(a)) + len(bits(b))
    goal = (1 << len(edges)) - 1
    prices = [10**4] * (goal + 1)
    prices[0] = 0
    for s in range(goal):
        if prices[s] == 10**4:
            continue
        for rectangle, price in rectangles.items():
            u = s | rectangle
            prices[u] = min(prices[u],prices[s]+price)
    return prices[goal] - 1


def verify(seconds):
    active = []
    for mask in range(FULL+1):
        es = [(a,b) for a,b in EDGES if a in bits(mask) and b in bits(mask)]
        active.append(sum(1<<v for v in {u for e in es for u in e}))
    known,solved = {0:0},{}
    binaries = {}
    with tempfile.TemporaryDirectory(prefix="pnp-seven-signed-") as temp:
        for mask in sorted(set(active)-{0}, key=lambda s:(len(bits(s)),s)):
            verts = bits(mask)
            n = len(verts)
            edges = [(verts.index(a),verts.index(b)) for a,b in EDGES if a in verts and b in verts]
            key,group = canonical(n,edges)
            if key in solved:
                known[mask] = solved[key]
                continue
            upper = rectangle_upper(n,edges)
            lift = [sum(1<<verts[v] for v in bits(i)) for i in range(1<<n)]
            end = len(lift)-1
            lower = [known[active[m]] for m in lift[:-1]] + [n-1]
            floor = n-1
            for v in range(n):
                rest = end ^ (1<<v)
                neighbors = sum(1<<(b if a==v else a) for a,b in edges if v in (a,b))
                core = rest & ~neighbors
                zero_active = len(bits(active[lift[rest]]))
                if zero_active:
                    floor = max(floor, lower[rest]+n-zero_active)
                high = lower[core]+len(bits(neighbors))-int(lower[core]==0)
                high_active = len(bits(neighbors))+len(bits(active[lift[core]]))
                floor = max(floor,high+n-high_active)
            assert floor <= upper
            searches,nodes = 0,0
            for budget in range(floor,upper):
                assert all(active[lift[end ^ (1<<v)]] for v in range(n))
                lower[end] = budget
                formula = [g+1 if g else 0 for g in lower]
                if n not in binaries:
                    exe = Path(temp)/f"search-{n}"
                    subprocess.run(["c++","-O3","-std=c++17",f"-DWIDTH={n}","-DSIGNED_MODE=1",
                                    "-DPETERSEN_PAIR_MODE=2",str(HERE/"petersen-raw-prefix.cpp"),
                                    "-o",str(exe)],check=True)
                    binaries[n] = exe
                def run(job):
                    r = subprocess.run([str(binaries[n])],input=job[2],text=True,capture_output=True,
                                       check=True,timeout=seconds+40)
                    verdict,count = r.stdout.splitlines()[-1].split()
                    if verdict not in ("SAT","UNSAT"):
                        raise RuntimeError((mask,budget,job[0],verdict))
                    return verdict,int(count)
                jobs = LIB["reader_jobs"](n,edges,group,formula,lower,budget,seconds,aggregate=True)
                found = False
                with ThreadPoolExecutor(max_workers=2) as pool:
                    for verdict,count in pool.map(run,jobs):
                        found |= verdict == "SAT"
                        searches += 1
                        nodes += count
                if found: # Every SAT witness was evaluated on the full truth table in C++.
                    floor = budget
                    break
                floor = budget+1
            known[mask] = solved[key] = floor
            if searches or mask in (126,127):
                print(f"mask={mask} signed={floor} rectangle_upper={upper} "
                      f"profiles={searches} prefixes={nodes}",flush=True)
        assert known[126]==10 and known[127]==12
        print("Six-input prism minimum 10; seven-input minimum 12.")
    assert not Path(temp).exists()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds",type=int,default=30)
    args = parser.parse_args()
    if args.seconds < 1:
        parser.error("use a positive time limit")
    verify(args.seconds)
