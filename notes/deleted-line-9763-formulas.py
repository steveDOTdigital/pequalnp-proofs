"""Bound signed formula size for the projective plane with one deleted line.

Run with Python 3.10 or newer. The comparison argument is in
heawood-signed-formulas.md. Ownership means choosing one endpoint per edge.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from runpy import run_path

notes = Path(__file__).resolve().parent
local_masks = run_path(str(notes / "heawood-signed-formulas.py"))["local_masks"]
points = range(13)
pencils = [[12 + (p + d) % 13 for d in (0, 4, 10, 12) if (p+d)%13] for p in points]
neighbors = pencils + [[p for p in points if 13 + line in pencils[p]] for line in range(12)]
assert sum(map(len, neighbors)) == 96


def neighbor_bits(vertex, selected):
    return sum(1 << j for j, w in enumerate(neighbors[vertex]) if selected >> w & 1)


@lru_cache(None)
def local_price(degree, clean, mixed, owner, forced):
    """Minimize positive reads less unowned flags, keeping all best choices."""
    choices = []
    for owned in range(1 << degree):
        if bool(owned) != owner or forced & ~owned:
            continue
        for reads in range(1 + mixed, degree + 1):
            if any(mark & ~owned == 0 for mark in local_masks(reads, clean, degree)):
                choices.append((reads - degree + owned.bit_count(), owned))
                break
    return dict((mask,cost) for cost,mask in choices)


def owner_profiles():
    # Nonowners form an independent set. Bit 4 denotes an owner.
    for pset in range(1 << 13):
        blocked = sum(1 << line for line in range(12)
                      if any(pset >> p & 1 for p in neighbors[13 + line]))
        available = ((1 << 12) - 1) ^ blocked
        lset = available
        while True:
            independent = pset | (lset << 13)
            yield bytes(0 if independent >> v & 1 else 16 + neighbor_bits(v, independent)
                        for v in range(25))
            if not lset:
                break
            lset = (lset - 1) & available


def feasible(domains, limit):
    # One orientation at each end of a flag, with a common leaf budget.
    if any(not d for d in domains):
        return False
    links=[(v,i,w,neighbors[w].index(v)) for v in points for i,w in enumerate(neighbors[v])]
    while True:
        changed=False
        minima=[min(d.values()) for d in domains]
        remaining=limit-sum(minima)
        if remaining<0:
            return False
        for v,d in enumerate(domains):
            kept={m:c for m,c in d.items() if c<=minima[v]+remaining}
            if len(kept)<len(d):domains[v]=kept;changed=True
        for v,i,w,j in links:
            for a,k,b,t in ((v,i,w,j),(w,j,v,i)):
                allowed={1-((m>>t)&1) for m in domains[b]}
                kept={m:c for m,c in domains[a].items() if ((m>>k)&1) in allowed}
                if not kept:return False
                if len(kept)<len(domains[a]):domains[a]=kept;changed=True
        if not changed:break
    open_vars=[v for v,d in enumerate(domains) if len(d)>1]
    if not open_vars:return sum(min(d.values()) for d in domains)<=limit
    v=min(open_vars,key=lambda w:len(domains[w]))
    for m,c in domains[v].items():
        branch=list(domains);branch[v]={m:c}
        if feasible(branch,limit):return True
    return False


def bounds(mixed, profiles):
    prices, choices = [], []
    for v in range(25):
        degree = len(neighbors[v])
        clean = ((1 << degree) - 1) ^ neighbor_bits(v, mixed)
        entries = [local_price(degree, clean, (mixed >> v) & 1, i >= 16,
                               (i & 15) if i >= 16 else 0) for i in range(32)]
        prices.append([min(d.values(),default=100) for d in entries])
        choices.append(entries)
    fixed = 48 + mixed.bit_count()
    from numpy import array, arange
    table = array(prices, dtype='int16')
    costs = fixed + table[arange(25), profiles].sum(axis=1)
    lower = int(costs.min())
    for budget in range(lower,59):
        for row in profiles[costs <= budget]:
            if feasible([choices[v][z] for v,z in enumerate(row)],budget-fixed):
                return lower,budget
    return lower,max(59,lower)

def symmetries():
    # Use the first two parallel classes to coordinatize the affine plane.
    inf = [p for p in points if len(pencils[p]) == 3]
    affine = [p for p in points if p not in inf]
    axes = [sorted(pencils[p]) for p in inf[:2]]
    coord = {p: tuple(next(i for i,l in enumerate(axis) if l in pencils[p])
                     for axis in axes) for p in affine}
    inv = {v:p for p,v in coord.items()}
    assert len(inv)==9
    line_by_points = {frozenset(p for p in v if p in coord):i+13
                      for i,v in enumerate(neighbors[13:])}
    inf_by_lines = {frozenset(pencils[p]):p for p in inf}
    from itertools import product
    group = []
    for a,b,c,d in product(range(3),repeat=4):
        if (a*d-b*c)%3==0: continue
        for u,v in product(range(3),repeat=2):
            m = {p:inv[((a*x+b*y+u)%3,(c*x+d*y+v)%3)] for p,(x,y) in coord.items()}
            for pts,l in line_by_points.items():
                m[l] = line_by_points[frozenset(m[p] for p in pts)]
            for p in inf: m[p]=inf_by_lines[frozenset(m[l] for l in pencils[p])]
            perm = tuple(m[i] for i in range(25))
            assert len(set(perm))==25
            assert all(set(neighbors[m[i]])=={m[k] for k in neighbors[i]} for i in range(25))
            group.append(perm)
    assert len(set(group))==432
    assert {perm[13] for perm in group}==set(range(13,25))
    # Verify the natural quotient labels after deleting one more line.
    import re
    prior=(notes/'PuncturedPlaneCircuit.lean').read_text(encoding='utf8')
    prior=prior.split('def rawTarget',1)[1].split('theorem upper',1)[0]
    flags={(int(a),int(b)) for a,b in re.findall(r'\(x (\d+) && x (\d+)\)',prior)}
    assert len(flags)==44
    assert {(p,l-1) for p in points for l in pencils[p] if l!=13}==flags
    # Every nonempty set of line vertices has strictly more point neighbors.
    for mask in range(1,1<<12):
        incident={p for p in points if any(mask>>(l-13)&1 for l in pencils[p])}
        assert len(incident)>mask.bit_count()
    return group

if __name__ == "__main__":
    import sys, numpy as np
    profiles = np.array([list(p) for p in owner_profiles()], dtype=np.uint8)
    group = symmetries()
    print('owner profiles',len(profiles),'automorphisms',len(group),flush=True)
    for count in range(1+int(sys.argv[1]) if len(sys.argv)>1 else 4):
        seen=set(); hist=Counter(); orbits=0
        for sub in combinations(range(25),count):
            if sub in seen:continue
            orb={tuple(sorted(perm[i] for i in sub)) for perm in group}
            seen.update(orb);orbits+=1
            answer=bounds(sum(1<<i for i in sub),profiles)
            hist[answer]+=len(orb)
        from math import comb
        assert sum(hist.values())==comb(25,count)
        print(count,orbits,sorted(hist.items()),flush=True)
