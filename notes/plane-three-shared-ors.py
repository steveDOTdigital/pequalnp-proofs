"""Check three shared raw OR gates modulo the verified plane collineations."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from math import factorial
import runpy
import sys

geom=runpy.run_path(str(Path(__file__).with_name('plane-shared-or-check.py')))
price=geom['general_price']
group=[tuple(p)+tuple(x+13 for x in l) for p,l in geom['collineations']()]
types={'P':tuple(combinations(range(13),2)), 'L':tuple(combinations(range(13,26),2)),
       'X':tuple(product(range(13),range(13,26)))}

def orbits(pattern,chain=(),stab=None,mult=1):
    if not pattern:
        yield chain,mult
        return
    if stab is None:stab=group
    free=set(types[pattern[0]])-set(chain)
    while free:
        a,b=min(free)
        buckets={}
        for g in stab:
            image=tuple(sorted((g[a],g[b])))
            buckets.setdefault(image,[]).append(g)
        free.difference_update(buckets)
        yield from orbits(pattern[1:],chain+((a,b),),buckets[a,b],mult*len(buckets))

def certify(helpers):
    opts=[tuple(o) for o in product(*[(None,*h) for h in helpers])]
    opts.sort(key=lambda o:sum(v is not None for v in o))
    best=0
    trials=[]
    for orient in opts:
        value,exceptional=price(helpers,orient=orient)
        best=max(best,value)
        if best>=64:return best
        if value>=60:trials.append((value,orient,exceptional))
    for _,orient,candidates in sorted(trials,key=lambda t:-t[0])[:6]:
        for k in (1,2):
            for removed in combinations(sorted(candidates),k):
                value,_=price(helpers,frozenset(removed),orient)
                best=max(best,value)
                if best>=64:return best
    return best

def check(pattern):
    stats=Counter()
    bad=None
    for helpers,mult in orbits(pattern):
        value=certify(helpers)
        stats[value]+=mult
        if value<64 and (bad is None or value<bad[0]):
            bad=(value,helpers)
        geom['matching'].cache_clear()
    denom=1
    for n in Counter(pattern).values():denom*=factorial(n)
    # Different orders may take different valid shortcuts. Count pass versus unresolved.
    ok=sum(c for val,c in stats.items() if val>=64)
    total=sum(stats.values())
    assert total%denom==0
    print(pattern,'distinct',total//denom,'ordered',total,'certified ordered',ok,'minimum',min(stats),'example',bad,flush=True)

if __name__=='__main__':
    for pattern in sys.argv[1:] or ('PPX','PLX','PXX','XXX'):
        check(pattern)
