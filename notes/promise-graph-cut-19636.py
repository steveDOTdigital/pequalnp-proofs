"""Read-once decompositions after cutting the only gate with two consumers."""
from functools import lru_cache
from itertools import combinations
from collections import Counter
import runpy
from pathlib import Path
base=runpy.run_path(str(Path(__file__).with_name("promise-graph-19636.py")))
target=base["MASK"]
full=(1<<25)-1
row_bits=[sum((1<<i) for i,x in enumerate(base["inputs"](r)) if x) for r in range(25)]
raw=[sum(((row_bits[r]>>i)&1)<<r for r in range(25)) for i in range(10)]


def halves(xs):
    for n in range(1,len(xs)//2+1):
        for part in combinations(range(len(xs)),n):
            if 2*n==len(xs) and 0 not in part:continue
            yield tuple(xs[i] for i in part),tuple(x for i,x in enumerate(xs) if i not in part)


def colorings(s,m):
    ht=[r&s for r in row_bits]
    rest=m^s
    adj={a:set() for a in ht}
    for i in range(25):
        for j in range(i):
            if ((row_bits[i]^row_bits[j])&rest)==0 and ((target>>i ^ target>>j)&1):
                adj[ht[i]].add(ht[j]);adj[ht[j]].add(ht[i])
    colour={}
    components=[]
    for x in adj:
        if x in colour:continue
        comp={x};colour[x]=0;stack=[x]
        while stack:
            v=stack.pop()
            for u in adj[v]:
                if u in colour:
                    if colour[u]==colour[v]:return
                else:
                    colour[u]=1-colour[v];comp.add(u);stack.append(u)
        components.append(comp)
    masks=[sum((v in component)<<i for i,v in enumerate(ht)) for component in components]
    possible=[sum(colour[v]<<i for i,v in enumerate(ht))]
    for change in masks:possible += [h^change for h in possible]
    yield from possible


@lru_cache(maxsize=20000)
def tables(xs,k):
    if len(xs)==1:
        return (xs[0],full^xs[0]) if k else (xs[0],)
    vals=set()
    for a,b in halves(xs):
        for i in range(k+1):
            for u in tables(a,i):
                for v in tables(b,k-i):
                    vals.update((u&v,u|v))
    if k:vals.update(full^w for w in tables(xs,k-1))
    return tuple(vals)


@lru_cache(maxsize=100000)
def fits(xs,k,p,n):
    if len(xs)<=3:
        return any(w&p==p and not w&n for w in tables(xs,k))
    if k and fits(xs,k-1,n,p):return True
    for a,b in halves(xs):
        for j in range(k+1):
            for w in tables(a,j):
                if not w&n and fits(b,k-j,p&~w,n):return True
                if w&p==p and fits(b,k-j,p,n&w):return True
    return False


def main():
    stats=Counter()
    for mask in base["supports"]():
        r=mask.bit_count()
        if r not in (7,8):continue
        k=9-r
        s=(mask-1)&mask
        while s:
            xs=tuple(sorted(raw[i] for i in range(10) if s & (1<<i)))
            rest=tuple(raw[i] for i in range(10) if (mask^s)&(1<<i))
            for h in colorings(s,mask):
                stats["labels"]+=1
                for j in range(k+1):
                    if fits(xs,j,h,full^h):
                        stats["prefixes"]+=1
                        suffix=tuple(sorted((*rest,h,h)))
                        if fits(suffix,k-j,target,full^target):
                            print("POSSIBLE",mask,k,s,h,j,flush=True);return
                        break
            s=(s-1)&mask
        stats["supports"]+=1
        print("EXCLUDED",mask,k,flush=True)
    print("Only-one-repeated-wire census",dict(stats),flush=True)


if __name__=="__main__":main()
