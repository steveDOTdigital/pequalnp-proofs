from itertools import combinations,permutations
from functools import lru_cache

V=range(6)
PAIRS=tuple(combinations(V,2))
INDEX={e:i for i,e in enumerate(PAIRS)}
PINS=[1<<i|1<<j for i,j in PAIRS]
NROWS=range(64)

def representatives():
    translations=[tuple(INDEX[tuple(sorted((p[i],p[j])))] for i,j in PAIRS) for p in permutations(V)]
    seen=set()
    for graph in range(1<<15):
        if graph in seen:continue
        edges=[i for i in range(15) if graph>>i&1]
        seen.update(sum(1<<trans[i] for i in edges) for trans in translations)
        yield graph
    assert len(seen)==1<<15

def shore_pairs():
    for a in range(1,64):
        for b in range(a+1,64):
            if a&b:continue
            rectangle=sum(1<<k for k,(i,j) in enumerate(PAIRS)
                          if ((a>>i & b>>j)|(a>>j & b>>i))&1)
            yield a,b,rectangle
SHORES=list(shore_pairs())

def cover(target, pieces):
    # Branch on a remaining item with the fewest maximal covering pieces.
    allm=sorted(set(pieces),key=int.bit_length,reverse=True)
    maximal=[]
    for m in allm:
        if m and not any(m&x==m for x in maximal):maximal.append(m)
    options={1<<k:[m for m in maximal if m>>k&1] for k in range(target.bit_length()) if target>>k&1}
    @lru_cache(None)
    def go(left):
        if not left:return ()
        bit=min((b for b in options if left&b),key=lambda b:len(options[b]))
        return min(((m,)+go(left&~m) for m in options[bit]),key=len)
    return go(target)

def data(graph):
    edges=[PINS[k] for k in range(15) if graph>>k&1]
    neg=[r for r in NROWS if not any((r&e)==e for e in edges)
         and all(r>>i&1 or any(((r|1<<i)&e)==e for e in edges) for i in V)]
    pos=sorted({r|1<<i for r in neg for i in V if not r>>i&1})
    pairs=[(a,b,e) for a,b,e in SHORES if not e&~graph]
    bc=len(cover(graph,[e for a,b,e in pairs]))
    columns={sum(1<<k for k,r in enumerate(pos) if r&a and r&b):(a,b) for a,b,e in pairs}
    c=cover((1<<len(pos))-1,columns)
    flat=[columns[m] for m in c]
    return neg,pos,bc,flat

def optimal_cover(graph):
    pairs={edge:(a,b) for a,b,edge in SHORES if not edge&~graph}
    return [pairs[edge] for edge in cover(graph,pairs)]

if __name__=='__main__':
    import collections
    counts=collections.Counter()
    for gr in representatives():
        neg,pos,bic,flat=data(gr);counts[bic]+=1
        if len(flat)<bic:
            print('WITNESS',gr,'biclique number',bic,'gates',flat,'negative',neg,'positive',pos,flush=True)
    print('graph counts',counts,flush=True)
