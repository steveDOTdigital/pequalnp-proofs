"""AND cost of the eleven-vertex graph with arbitrary free ORs."""
import argparse
from itertools import combinations
from pathlib import Path
from runpy import run_path
import subprocess

data = run_path(str(Path(__file__).with_name("eleven-dirty-search.py")))
E,POS,NEG = data["EDGES"],data["POS"],data["NEG"]
N=11


def solve(k, seconds, pin):
    clauses=[]
    nv=0
    def var():
        nonlocal nv
        nv+=1
        return nv
    def meet(a,b):
        v=var()
        clauses.extend(([-v,a],[-v,b],[v,-a,-b]))
        return v
    def join(xs):
        v=var()
        clauses.extend([-a,v] for a in xs)
        clauses.append([-v]+xs)
        return v
    ports=[([var() for _ in range(N+j)],[var() for _ in range(N+j)]) for j in range(k)]
    final=[var() for _ in ports]
    clauses.append(final)
    for a,b in ports:
        clauses.extend([-x,-y] for x,y in zip(a,b))
        for i,y in enumerate(b):
            clauses.append([-y]+a[:i])
    for u in range(N):
        uses=[side[u] for pair in ports for side in pair]
        cap=k-(sum(bool(row & (1<<u)) for row in NEG)-1).bit_length()
        clauses.append(uses)
        clauses.extend([-v for v in group] for group in combinations(uses,cap+1))
    # Before the first true AND on an edge, only raw signals can be true.
    for u,v in E:
        clauses.append([z for a,b in ports for z in (meet(a[u],b[v]),meet(a[v],b[u]))])
    negative_ports=[]
    for row in POS+NEG:
        row_ports=[]
        values=[]
        for pair in ports:
            sides=[]
            for port in pair:
                raw=[x for i,x in enumerate(port[:N]) if row & (1<<i)]
                old=[meet(x,y) for x,y in zip(port[N:],values)]
                sides.append(join(raw+old))
            values.append(meet(*sides))
            row_ports.append(sides)
        root=join([meet(a,b) for a,b in zip(values,final)])
        clauses.append([root if row in POS else -root])
        if row in NEG:
            negative_ports.append(row_ports)
    # Distinct maximal false rows have a positive union. At the first gate
    # differing from the union of their separate evaluations, the operands
    # of one AND have opposite patterns (1,0) and (0,1).
    for x,y in combinations(negative_ports,2):
        split=[]
        for (a,b),(c,d) in zip(x,y):
            for pattern in ((a,-b,-c,d),(-a,b,c,-d)):
                witness=var()
                clauses.extend([-witness,lit] for lit in pattern)
                split.append(witness)
        clauses.append(split)
    if pin:
        owners=(0,1,3,5,7,8,10)
        assert k==len(owners)
        groups={u:[] for u in owners}
        for a,b in E:
            u=a if a in groups else b
            groups[u].append(a if u==b else b)
        for j,(u,(a,b)) in enumerate(zip(owners,ports)):
            left,right={u},set(groups[u])
            if min(left)>min(right):left,right=right,left
            for side,s in [(a,left),(b,right)]:
                for i,x in enumerate(side):clauses.append([x if i in s else -x])
            clauses.append([final[j]])
    cnf=f"p cnf {nv} {len(clauses)}\n"+"".join(" ".join(map(str,c))+" 0\n" for c in clauses)
    exe=Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"bin/cadical"
    out=subprocess.run([str(exe),"-q","--check","--checkproof=2","-t",str(seconds)],input=cnf,
                       capture_output=True,text=True,timeout=seconds+20)
    if out.returncode==20 and "s UNSATISFIABLE" in out.stdout:return "UNSAT"
    if out.returncode==0 and "UNKNOWN" in out.stdout:return "time limit"
    if out.returncode!=10:raise RuntimeError(out.stderr[-240:])
    model={int(v) for line in out.stdout.splitlines() if line.startswith("v ") for v in line.split()[1:]}
    gs=[([i for i,x in enumerate(a) if x in model],[i for i,x in enumerate(b) if x in model]) for a,b in ports]
    ends=[j for j,x in enumerate(final) if x in model]
    for row in range(2048):
        values=[bool(row&(1<<i)) for i in range(N)]
        for a,b in gs:values.append(any(values[i] for i in a) and any(values[i] for i in b))
        assert any(values[N+j] for j in ends)==data["target"](row)
    return "SAT",gs,ends


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("k",type=int)
    ap.add_argument("--seconds",type=int,default=120)
    ap.add_argument("--star",action="store_true")
    opt=ap.parse_args()
    print(solve(opt.k,opt.seconds,opt.star),flush=True)
