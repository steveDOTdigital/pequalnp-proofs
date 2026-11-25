"""Check local rectangle profiles for the three-cross-OR plane cases."""
from itertools import product, permutations
from pathlib import Path
from functools import lru_cache
import subprocess
import runpy
import sys

root=Path(__file__).resolve().parent
plane=runpy.run_path(str(root/'plane-shared-or-check.py'))
CNF=runpy.run_path(str(root/'plane-three-line-cores.py'))['Formula']
ADJ=plane['ADJ']
arcs=tuple(permutations(range(4),2))

@lru_cache(None)
def profiles(r):
    if r==4:return [0]
    all_masks=set()
    for rows in product(range(1,1<<r),repeat=4):
        if not any(all((x&bits)!=0 and ((x&bits)&((x&bits)-1))==0 for x in rows) for bits in range(1,1<<r)):continue
        all_masks.add(sum(1<<k for k,(i,j) in enumerate(arcs) if rows[i]&rows[j]==rows[i]))
    return sorted(x for x in all_masks if not any(y!=x and y&x==y for y in all_masks))

def at_most(c,lits,k):
    # Unary prefix counts. A true input advances every attained threshold by one.
    earlier=[]
    for lit in lits:
        latest=[c.var() for _ in range(min(len(earlier)+1,k+1))]
        c.clauses.append([-lit,latest[0]])
        for i,old in enumerate(earlier):
            c.clauses.append([-old,latest[i]])
            if i+1<len(latest):c.clauses.append([-old,-lit,latest[i+1]])
        earlier=latest
    c.clauses.append([-earlier[k]])

def check(helpers,limit,seconds):
    c=CNF()
    rows=[sorted(a) for a in ADJ]
    partners=[set() for a in rows]
    for x,y in helpers:
        partners[x].add(y); partners[y].add(x)
    dom={};extra=[]
    for v,neigh in enumerate(rows):
        assert plane['independent'](set(neigh)|partners[v])
        marks=[c.var() for _ in range(3)];extra+=marks
        choices=[]
        for i,j in arcs:dom[v,neigh[i],neigh[j]]=c.var()
        for r in range(1,5):
            for mask in profiles(r):
                var=c.var();choices.append(var)
                c.clauses.extend([-var,k] for k in marks[:r-1])
                c.clauses.extend([-var,dom[v,neigh[i],neigh[j]]] for idx,(i,j) in enumerate(arcs) if mask&(1<<idx))
        c.clauses.append(choices)
    for p,l in plane['FULL']:
        for w in ADJ[p]-{l}:
            for a in ADJ[l]-{p}:
                compare={a,w}|partners[p]|partners[l]
                if p not in compare and l not in compare and plane['independent'](compare):
                    c.clauses.append([-dom[p,w,l],-dom[l,a,p]])
    at_most(c,extra,limit-26)
    solver=Path(subprocess.check_output(['lean','--print-prefix'],cwd=root.parent/'lean',text=True).strip())/'bin/cadical'
    result=subprocess.run([str(solver),'-q','--check','--checkproof=2','-t',str(seconds)],
        input=c.text(),capture_output=True,text=True)
    return {10:'SAT',20:'UNSAT',0:'incomplete'}.get(result.returncode,'incomplete')

def classify_orbits():
    from collections import Counter
    from concurrent.futures import ThreadPoolExecutor
    from itertools import combinations
    shape=runpy.run_path(str(root/'plane-three-shared-ors.py'))
    group=shape['group']
    shapes=tuple((p,l) for p in range(13) for l in range(13,26))
    seen=set();pending=[];covered=0
    for basis in combinations(shapes,3):
        if basis in seen:continue
        orbit={tuple(sorted((g[p],g[l]) for p,l in basis)) for g in group}
        seen.update(orbit)
        if shape['certify'](basis)>=64:
            covered+=len(orbit)
        else:
            pending.append((basis,len(orbit)))
        plane['matching'].cache_clear()
    assert len(seen)==790244
    print('three cross-shore ORs, direct exclusions',covered,'remaining orbits',len(pending),flush=True)
    outcomes=Counter()
    def run(row):
        basis,count=row
        return basis,count,check(basis,55,18)
    with ThreadPoolExecutor(max_workers=3) as workers:
        for basis,count,verdict in workers.map(run,pending):
            outcomes[verdict]+=count
            print('profile',basis,count,verdict,flush=True)
    assert sum(outcomes.values())+covered==790244
    print('three cross-shore ORs',covered,dict(outcomes),flush=True)

if __name__=='__main__':
    fam=((0,15),(1,14),(2,18))
    print('profiles per raw budget',[(r,len(profiles(r))) for r in range(1,5)],flush=True)
    print('ordinary star control',check(fam,65,12),flush=True)
    if '--all-cross' in sys.argv:classify_orbits()
    else:print(fam,check(fam,55,30),flush=True)
