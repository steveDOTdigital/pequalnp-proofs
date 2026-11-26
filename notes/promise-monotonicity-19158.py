"""Finish the finite cases from the JavaScript orbit and formula replay (Python-SAT)."""
from itertools import combinations
import json
from pathlib import Path
import subprocess


def raw_row(i):
    a,b=divmod(i,4)
    return [j==a for j in range(4)] + [j==b for j in range(4)]


def special_constructions():
    def cell(mask,i,j):
        if mask==31710:
            h=[i==k or j==k for k in range(4)]
            return (h[0] and h[1]) or (h[2] and h[3]) or ((h[0] or h[1]) and (h[2] or h[3]))
        if mask==31711:
            h=[i==k or j==k for k in (1,2,3)]
            return (i==0 or j==0) or ((h[0] and h[1]) or (h[2] and (h[0] or h[1])))
        rows = [[0],[1],[2,3]] if mask!=15838 else [[0],[1,2],[3]]
        cols = [[0],[1],[2,3]]
        h=[i in a or j in b for a,b in zip(rows,cols)]
        crown=(h[0] and h[1]) or (h[2] and (h[0] or h[1]))
        return crown or (mask==14302 and i==2 and j==2)
    for mask in (31710,31711,13278,15838,14302):
        assert sum(int(cell(mask,i,j))<<(4*i+j) for i in range(4) for j in range(4))==mask


def possible_support(target,support):
    outputs={}
    for row in range(16):
        pattern=sum(int(v)<<i for i,v in enumerate(raw_row(row))) & support
        wanted=(target>>row)&1
        if outputs.setdefault(pattern,wanted)!=wanted:return False
    return True


def search(target,support,size,nots,backend):
    from pysat.solvers import Solver
    pins=[q for q in range(8) if support>>q&1]
    wires=[[raw_row(i)[q] for i in range(16)] for q in pins]
    cnf,ops=[],[]
    count=0
    def new():
        nonlocal count
        count+=1
        return count
    def choose(n):
        ids=[new() for _ in range(n)]
        cnf.append(ids)
        cnf.extend([[-a,-b] for a,b in combinations(ids,2)])
        return ids
    def read(selectors,values):
        result=new()
        for s,v in zip(selectors,values):
            if type(v) is bool:
                cnf.append([-s,result if v else -result])
            else:
                cnf.extend([[-s,-v,result],[-s,v,-result]])
        return result
    for _ in range(size):
        left,right=choose(len(wires)),choose(len(wires))
        aop,oop,nop=choose(3)
        ops.append(nop)
        for i,sel in enumerate(left):
            cnf.extend([[-sel,-right[j]] for j in range(i)])
            cnf.extend([[-nop,-sel,right[i]],[-sel,-right[i],nop]])
        column=[]
        for row in zip(*wires):
            a,b=read(left,row),read(right,row)
            w=new()
            cnf.extend([[-aop,-a,-b,w],[-aop,a,-w],[-aop,b,-w],
                        [-oop,a,b,-w],[-oop,-a,w],[-oop,-b,w],
                        [-nop,a,w],[-nop,-a,-w]])
            column.append(w)
        wires.append(column)
    cnf.extend([[-v for v in group] for group in combinations(ops,nots+1)])
    cnf.extend([list(group) for group in combinations(ops,size-nots+1)])
    cnf.extend([[w if (target>>i)&1 else -w] for i,w in enumerate(wires[-1])])
    with Solver(name=backend,bootstrap_with=cnf) as solver:
        return solver.solve()


from itertools import combinations
def mincost(rows,cap):
 n=len(rows);q=3;full=(1<<(q*n))-1;target=sum(v<<(3*i) for i,v in enumerate(rows))
 raw=[sum(1<<(3*i+j) for i in range(n) for j in range(q) if z==i or z==n+j) for z in range(n+q)]
 lv=[set([0,*raw])];seen=set(lv[0])
 for cost in range(1,cap+1):
  new={full^v for v in lv[-1]}
  if cost==1:new.add(full)
  for k in range((cost-1)//2+1):
   for a in lv[k]:
    for b in lv[cost-1-k]:new.update((a&b,a|b))
  new-=seen
  if target in new:return cost
  seen|=new;lv.append(new)
 return None
def check_three_columns():
 n=0;bad=[]
 for p in range(5,9):
  for rs in combinations(range(8),p):
   n+=1;M=sum((1 if r==7 else r.bit_count()) for r in rs)+2
   if M>2*p-1:bad.append(rs)
 assert n==93 and len(bad)==6
 for rs in [(1,2,3,5,6),(1,3,5,6,7)]:
  assert mincost(rs,6) is None
 print("Rectangular quotients: 93 row families checked.")


def main():
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--backend",default="cadical195")
    args=ap.parse_args()
    special_constructions()
    check_three_columns()
    upper=Path(__file__).with_name("promise-monotonicity-19158.cjs")
    cases=json.loads(subprocess.check_output(["node",str(upper),"--cases"],text=True))
    count=0
    for case in cases:
        target,bound=case["t"],case["m"]
        for support in range(256):
            r=support.bit_count()
            if r+1>bound-4 or not possible_support(target,support):continue
            for size in range(r+1,bound-3):
                for nots in range(1,size-r+1):
                    if search(target,support,size,nots,args.backend):
                        raise RuntimeError(f"Unresolved candidate {target}: {support=}, {size=}, {nots=}")
                    count+=1
        print("Excluded all remaining counterexample sizes for mask",target,flush=True)
    print("All 65536 four-by-four matrices verified;",count,"completed bounded searches.",flush=True)


if __name__=="__main__":main()
