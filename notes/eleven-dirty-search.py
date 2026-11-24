"""Bounded synthesis for L-meta-1342, shard 1. Run from lean/ with Python 3."""
import argparse
from itertools import combinations
from pathlib import Path
import subprocess

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
POS = [(1<<a)|(1<<b) for a,b in EDGES]


def target(row):
    return any(row & e == e for e in POS)


NEG = [r for r in range(2048) if not target(r) and
       all(target(r | 1<<i) for i in range(11) if not r & (1<<i))]


def star_control():
    centers = (0,1,3,5,7,8,10)
    groups = {c:[] for c in centers}
    for a,b in EDGES:
        c = a if a in groups else b
        groups[c].append(b if a == c else a)
    # Three unused dirty gates are legal in the stated model and check shard accounting.
    gates = [(False,0,1),(False,1,2),(False,2,3)]
    def add(is_or,a,b):
        gates.append((is_or,min(a,b),max(a,b)))
        return 10+len(gates)
    def join(xs):
        out,*rest=xs
        for x in rest:
            out=add(True,out,x)
        return out
    out=join([add(False,c,join(group)) for c,group in groups.items()])
    assert out==10+len(gates) and len(gates)==25
    return gates


def evaluate(gates,row):
    vs=[bool(row & (1<<i)) for i in range(11)]
    for is_or,a,b in gates:
        vs.append(vs[a] or vs[b] if is_or else vs[a] and vs[b])
    return vs


def verify(gates):
    assert all(evaluate(gates,r)[-1]==target(r) for r in range(2048))
    dirty=sum(not op and any(evaluate(gates,r)[11+j] for r in NEG)
              for j,(op,_,_) in enumerate(gates))
    assert dirty>=3
    return dirty


def solve(budget,seconds,control):
    clauses=[]
    nv=0
    def var():
        nonlocal nv
        nv+=1
        return nv
    def choose(n):
        c=[var() for _ in range(n)]
        clauses.append(c)
        clauses.extend([-a,-b] for a,b in combinations(c,2))
        return c
    rows=POS+NEG
    wires=[[bool(r & (1<<i)) for r in rows] for i in range(11)]
    ops=[]
    labels=[]
    # Every operand selection is shared across rows. Constants and unary gates
    # are omitted in this candidate search; a timeout never exhausts the shard.
    for j in range(budget):
        a,b=choose(len(wires)),choose(len(wires))
        op=var()
        ops.append((op,a,b))
        for i,z in enumerate(a):
            clauses.extend([-z,-w] for w in b[:i])
        ports=[]
        for sels in (a,b):
            port=[var() for _ in rows]
            for sel,col in zip(sels,wires):
                for v,src in zip(port,col):
                    if isinstance(src,bool):
                        clauses.append([-sel,v if src else -v])
                    else:
                        clauses.extend(([-sel,-v,src],[-sel,v,-src]))
            ports.append(port)
        out=[var() for _ in rows]
        for x,y,z in zip(*ports,out):
            clauses.extend(([op,-z,x],[op,-z,y],[op,z,-x,-y],[-op,z,-x],[-op,z,-y],[-op,-z,x,y]))
        d=var()
        clauses.extend(([-d,-op],[-d]+out[len(POS):]))
        labels.append(d)
        wires.append(out)
    # Order the three distinct indices certifying dirtiness.
    picks=[choose(budget) for _ in range(3)]
    for k,pick in enumerate(picks):
        for i,v in enumerate(pick):
            clauses.append([-v,labels[i]])
            if k:
                clauses.extend([-v,-w] for w in picks[k-1][i:])
    clauses.extend([v if k<len(POS) else -v] for k,v in enumerate(wires[-1]))
    if control:
        for (op,a,b),(is_or,i,j) in zip(ops,star_control()):
            clauses.extend(([op if is_or else -op],[a[i]],[b[j]]))
    dimacs=f"p cnf {nv} {len(clauses)}\n"+"".join(" ".join(map(str,c))+" 0\n" for c in clauses)
    exe=Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"bin/cadical"
    p=subprocess.run([str(exe),"-q","--check","--checkproof=2","-t",str(seconds)],
                     input=dimacs,text=True,capture_output=True,timeout=seconds+20)
    if p.returncode==20 and "s UNSATISFIABLE" in p.stdout:return "UNSAT for this model"
    if p.returncode==0 and "UNKNOWN" in p.stdout:return "time limit"
    if p.returncode!=10 or "s SATISFIABLE" not in p.stdout:raise RuntimeError(p.stderr[-240:])
    model={int(v) for l in p.stdout.splitlines() if l.startswith("v ") for v in l.split()[1:]}
    gates=[(op in model,next(i for i,v in enumerate(a) if v in model),next(i for i,v in enumerate(b) if v in model)) for op,a,b in ops]
    return "SAT", verify(gates),gates


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--seconds",type=int,default=120)
    ap.add_argument("--control",action="store_true")
    args=ap.parse_args()
    print(solve(25 if args.control else 21,args.seconds,args.control),flush=True)
