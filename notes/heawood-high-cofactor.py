"""Verify signed circuit sizes and restriction bounds in the Fano incidence graph."""
import argparse
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from itertools import combinations, product
from pathlib import Path
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PROFILE = runpy.run_path(str(HERE / "petersen-unary-profiles.py"))
FANO = runpy.run_path(str(HERE / "heawood-signed-formulas.py"))
def configure(mask):
    global V, EDGES, N, ALL, BITS, COUNT
    kept = set(FANO["vertices"](mask))
    V = sorted({v for e in FANO["EDGES"] if set(e)<=kept for v in e})
    EDGES = [(V.index(a),V.index(b)) for a,b in FANO["EDGES"] if a in V and b in V]
    N = len(V)
    ALL = (1 << N)-1
    BITS = [(1 << a) | (1 << b) for a,b in EDGES]
    COUNT = [bin(m).count("1") for m in range(1 << N)]


def floors(temp, checked_order=0, monotone_mode=False, adjacent_floor=0, single_floor=0):
    # The existing signed gate-elimination recurrence supplies each induced floor.
    code = '''#define main mcgee_main
#include "cubic-pair-restrictions.cpp"
#undef main
int main(){
  std::vector<Mask> near(WIDTH);
  for (auto [a,b] : std::vector<std::pair<int,int>>{PAIRS}) {
    near[a] |= 1u<<b; near[b] |= 1u<<a;
  }
  Bounder base(near,true,-1), mono(near,true,0,nullptr,&base);
  auto &b = MONOTONE ? mono : base;
  if (PROVED>0) for(Mask s=1;s<(1u<<WIDTH);++s)
    if(count(s)<=PROVED && b.active(s)==s)base.memo[s]=b.memo[s]=b.upper(s);
  for (Mask s : std::vector<Mask>{ADJACENT}) b.memo[s]=ADJFLOOR;
  if(WIDTH==14 && SINGLE>0) for(int v=0;v<14;++v) b.memo[16383^(1u<<v)]=SINGLE;
  for(Mask s=0;s<(1<<WIDTH);++s) std::cout<<b.solve(s)<<" ";
}
'''.replace("WIDTH",str(N)).replace("PROVED",str(checked_order)).replace("MONOTONE",str(int(monotone_mode))).replace("PAIRS", ",".join("{%d,%d}" % e for e in EDGES))
    adjacent = set()
    if adjacent_floor:
        for g in FANO["automorphisms"]():
            image = {g[v] for v in FANO["vertices"](8175)}
            if image.issubset(V):
                adjacent.add(sum(1<<V.index(v) for v in image))
    code = code.replace("ADJACENT", ",".join(map(str,sorted(adjacent)))).replace("ADJFLOOR",str(adjacent_floor)).replace("SINGLE",str(single_floor))
    obj = Path(temp) / "bounds"
    subprocess.run(["c++", "-O3", "-std=c++17", "-I", str(HERE), "-x", "c++",
                    "-", "-o", str(obj)], input=code, text=True, check=True)
    lower = list(map(int, subprocess.check_output([str(obj)], text=True).split()))
    assert len(lower) == 1 << N
    active = []
    monotone = []
    alpha = [0]*(1<<N)
    neighbors = [sum(e ^ (1 << v) for e in BITS if e & (1<<v)) for v in range(N)]
    for s in range(1 << N):
        if s:
            low = s & -s
            v = low.bit_length()-1
            alpha[s] = max(alpha[s^low],1+alpha[(s^low) & ~neighbors[v]])
        es = [e for e in BITS if s & e == e]
        used = 0
        for e in es:
            used |= e
        active.append(used)
        cover = COUNT[s]-alpha[s]
        monotone.append(len(es) + cover)
    formula = []
    for s in range(1 << N):
        a = active[s]
        best = monotone[a]
        b = 0 if N > 10 else a
        while b:
            core = a ^ b
            best = min(best, 3*COUNT[b] + COUNT[core ^ active[core]] + monotone[core])
            b = (b-1) & a
        formula.append((monotone[a] if N > 10 else max(best, lower[s]+1)) if a else 0)
    return formula, lower, active, monotone


def symmetry():
    maps = {tuple(V.index(g[v]) for v in V) for g in FANO["automorphisms"]()
            if {g[v] for v in V} == set(V)}
    assert all({tuple(sorted((g[a],g[b]))) for a,b in EDGES} == set(EDGES) for g in maps)
    return sorted(maps)


def cases(formula, lower, budget, seconds, monotone_mode=False):
    return reader_jobs(N, EDGES, symmetry(), formula, lower, budget, seconds, monotone_mode,
                       aggregate=N > 10)


def reader_jobs(n, edges, group, formula, lower, budget, seconds, monotone_mode=False, aggregate=False):
    """Generate canonical direct-reader profiles and legal raw first gates."""
    all_vars = (1 << n) - 1
    bits = [(1 << a) | (1 << b) for a, b in edges]
    popcounts = [bin(s).count("1") for s in range(1 << n)]
    pairs = list(combinations(range(n), 2))
    zero = [lower[all_vars ^ (1 << v)] for v in range(n)]
    high = []
    for v in range(n):
        ns = sum(e ^ (1 << v) for e in bits if e & (1 << v))
        core = lower[all_vars ^ (1 << v) ^ ns]
        high.append(core + popcounts[ns] if core else popcounts[ns]-1)
    seen = set()
    def signs(r, cap_zero, cap_high):
        return [z for z in range(r+1) if r+min(2,z) <= cap_zero and r+min(2,r-z) <= cap_high]
    sizes = [[r for r in range(1,min(budget-a,budget-b)+1) if signs(r,budget-a,budget-b)]
             for a,b in zip(zero,high)]
    assert all(not options or max(options)<=4 for options in sizes)
    truth = [any(s & e == e for e in bits) for s in range(1 << n)]
    essential = {(v,w,t):any(truth[s] != truth[s | (1 << v)] for s in range(1 << n)
                             if not s & (1 << v) and ((s >> w) & 1)==t)
                 for v in range(n) for w in range(n) if w != v for t in (0,1)}
    for counts in product(*sizes):
        if counts in seen:
            continue
        seen.update(tuple(counts[g[v]] for v in range(n)) for g in group)
        if sum(counts) > budget+1 or (sum(counts) == budget+1 and formula[all_vars] > budget+1):
            continue
        if any(sum(counts[v] for v in range(n) if not s & (1 << v)) + k > budget
               for s,k in enumerate(lower) if k):
            continue
        allowed = set()
        for a,b in pairs:
            for op in ((0,3) if monotone_mode else range(4)):
                if monotone_mode and op==0 and (a,b) not in edges:
                    continue
                if counts[a] <= essential[a,b,op>>1] or counts[b] <= essential[b,a,op&1]:
                    continue
                if all(any((r-z if bit else z)>0 for z in signs(r,budget-zero[v],budget-high[v]))
                       for v,bit,r in [(a,op&1,counts[a]),(b,op>>1,counts[b])]):
                    allowed.add((op,a,b))
        stabilizer = [g for g in group if all(counts[v]==counts[g[v]] for v in range(n))]
        seeds = set(allowed)
        while seeds:
            seed = min(seeds)
            op,a,b = seed
            for g in stabilizer:
                u,w = g[a],g[b]
                seeds.discard((op,u,w) if u<w else (((op&1)<<1)|(op>>1),w,u))
            data = [budget,seconds,len(edges),sum((c-1) << (2*v) for v,c in enumerate(counts)),*bits]
            for v in range(n):
                data.extend((zero[v],high[v]))
            for a,b in pairs:
                data.extend((a,b,lower[all_vars ^ (1 << a) ^ (1 << b)]))
            if aggregate:
                # Try every legal raw gate first in one canonically sorted search.
                seeds.clear()
                data.append(len(allowed))
                for gate in sorted(allowed):
                    data.extend(gate)
            else:
                data.extend((1,*seed))
            data.append(len(allowed))
            for gate in sorted(allowed):
                data.extend(gate)
            data.extend(formula)
            data.extend(lower)
            data.extend((0,) if aggregate else (1,*seed))
            yield counts, seed, " ".join(map(str,data)) + "\n"


def census():
    configure((1<<14)-1)
    group = FANO["automorphisms"]()
    with tempfile.TemporaryDirectory(prefix="pnp-heawood-census-") as temp:
        _,initial,active,leaves = floors(temp)
        _,strengthened,_,_ = floors(temp,10)
        _,eleven,_,_ = floors(temp,11)
        _,ordinary,_,_ = floors(temp,11,True,20)
    assert not Path(temp).exists()
    small,large,seen = [],[],set()
    for s in range(1,1<<N):
        if s in seen or active[s] != s:
            continue
        seen.update(sum(1<<g[v] for v in V if s & (1<<v)) for g in group)
        upper = leaves[s]-1
        assert initial[s] <= strengthened[s] <= upper
        if COUNT[s]<=10 and initial[s]<upper:
            small.append(s)
        if COUNT[s]>10 and strengthened[s]<upper:
            large.append(s)
    assert small == [1963,1979,2019,2023,2031,3771,3835,4027,4047,4059]
    assert large == [4091,4095,8127,8175,8191,16383]
    assert strengthened[ALL] == 22 and strengthened[ALL^1] == 20
    high_core = ALL ^ (1 | sum(e^1 for e in BITS if e&1))
    assert strengthened[high_core] == 15
    print("Small signed-circuit exclusions requiring search:",*small)
    print("Larger signed-formula exclusions requiring the local proof:",*large)
    assert eleven[4095] == 19 and eleven[ALL] == 22
    assert ordinary[ALL] == 23 and ordinary[ALL^1] == 21
    print("Full signed circuit floor 22; single low pin 20; single high pin 18.")
    print("After the monotone adjacent-deletion exclusion: full monotone floor 23, single low pin 21.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--seconds",type=int,default=10)
    ap.add_argument("--workers",type=int,default=2)
    ap.add_argument("--mask",type=int, default=14974)
    ap.add_argument("--budget",type=int,help="check only this candidate size")
    ap.add_argument("--counts",action="append",help="limit to one exact direct-reader profile")
    ap.add_argument("--monotone",action="store_true",help="restrict every gate to an ordinary AND or OR")
    ap.add_argument("--census",action="store_true",help="verify the list of exceptional induced graphs")
    args = ap.parse_args()
    if args.census:
        return census()
    if not 0 <= args.mask < (1<<14) or args.seconds<1 or args.workers<1:
        ap.error("use a 14-bit vertex mask and positive time and worker limits")
    configure(args.mask)
    if not EDGES:
        print("The induced graph has no edges; constant false uses zero gates.")
        return
    if args.counts and any(len(r)!=N or any(c not in "1234" for c in r) for r in args.counts):
        ap.error("each count vector needs one digit from 1 to 4 per active input")
    scratch = tempfile.TemporaryDirectory(prefix="pnp-heawood-subgraph-")
    with scratch as temp:
        checked_order = 11 if N>11 else 10 if N==11 else 0
        adjacent_floor = 20 if args.monotone and N>12 else 0
        single_floor = 21 if N==14 else 0
        formula, lower, _, leaves = floors(temp,checked_order,args.monotone,adjacent_floor,single_floor)
        upper = leaves[ALL]-1
        budgets = range(lower[ALL],upper) if args.budget is None else [args.budget]
        if args.budget is not None and args.budget < lower[ALL]:
            print(f"Mask {args.mask}: the restriction floor {lower[ALL]} already excludes budget {args.budget}.")
            scratch.cleanup()
            assert not Path(temp).exists()
            return
        assert all(lower[ALL] <= b < upper for b in budgets)
        jobs = (job for budget in budgets for job in cases(formula,lower,budget,args.seconds,args.monotone)
                if not args.counts or "".join(map(str,job[0])) in args.counts)
        kind = "monotone" if args.monotone else "signed"
        print(f"Mask {args.mask}: {kind} circuit floor {lower[ALL]}, upper {upper}, formula floor {formula[ALL]}.",flush=True)
        binary = Path(temp)/"search"
        subprocess.run(["c++","-O3","-std=c++17",f"-DWIDTH={N}","-DSIGNED_MODE=1",
                        f"-DPETERSEN_PAIR_MODE={3 if args.monotone else 2}",str(HERE/"petersen-raw-prefix.cpp"),
                        "-o",str(binary)],check=True)
        control = PROFILE["control"]
        check = subprocess.run([str(binary)],input=control(N,args.seconds,formula,lower,edges=EDGES),
                               text=True,capture_output=True,check=True)
        assert check.stdout.splitlines()[-1].startswith("SAT "), check.stdout
        print(f"{upper}-gate positive control passed all {1<<N} truth rows.",flush=True)
        def run(job):
            counts,seed,data = job
            result = subprocess.run([str(binary)],input=data,text=True,capture_output=True,
                                    check=True,timeout=args.seconds+40)
            verdict, nodes = result.stdout.splitlines()[-1].split()
            return verdict,int(nodes),counts,seed
        results = Counter()
        total = 0
        job_count = 0
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            pending = set()
            exhausted = False
            while pending or not exhausted:
                while not exhausted and len(pending)<2*args.workers:
                    job = next(jobs,None)
                    if job is None:
                        exhausted = True
                    else:
                        pending.add(pool.submit(run,job))
                        job_count += 1
                if pending:
                    done,pending = wait(pending,return_when=FIRST_COMPLETED)
                    for item in done:
                        verdict,nodes,counts,seed = item.result()
                        results[verdict] += 1
                        total += nodes
                        if verdict != "UNSAT":
                            print(verdict,counts,seed,nodes,flush=True)
        if not job_count and args.counts:
            print("No requested counts survived the numerical tests and symmetry representative selection.")
        print(dict(results),"prefixes",total,flush=True)
    assert not Path(temp).exists()
    if results.get("UNSAT",0) != job_count:
        raise SystemExit("Incomplete exclusion.")


if __name__ == "__main__":
    main()
