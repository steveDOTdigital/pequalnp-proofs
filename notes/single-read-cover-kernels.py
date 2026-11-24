"""Enumerate four-cycle-free incidence graphs after removing isolated inputs and leaf twins.

Isomorphism allows swapping shores. A minimum vertex cover distinguishes the
small search universe; canonical labels forget which cover generated the graph.
"""
from collections import Counter
from itertools import combinations, permutations

def parts(code):
    a, masks = code
    return a, len(masks), {(i,a+j) for j,m in enumerate(masks) for i in range(a) if m&(1<<i)}


def canonical(left,right,edges):
    if not edges:
        return 0,()
    left = sorted({v for v,w in edges})
    right = sorted({w for v,w in edges})
    def oriented(L,R,E):
        rows = {w:{v for v,u in E if u==w} for w in R}
        return min((len(L),tuple(sorted(sum(1<<i for i,v in enumerate(p) if v in rows[w]) for w in R)))
                   for p in permutations(L))
    options=[]
    if len(left)<=len(right):
        options.append(oriented(left,right,edges))
    if len(right)<=len(left):
        options.append(oriented(right,left,{(v,u) for u,v in edges}))
    return min(options)


def neighbors(edges):
    result={}
    for a,b in edges:
        result.setdefault(a,set()).add(b)
        result.setdefault(b,set()).add(a)
    return result


def matching(edges):
    left={v for v,w in edges}
    adj=neighbors(edges)
    mate={}
    def augment(v,seen):
        for w in adj[v]-seen:
            seen.add(w)
            if w not in mate or augment(mate[w],seen):
                mate[w]=v
                return True
        return False
    return sum(augment(v,set()) for v in left)


def components(edges):
    adj=neighbors(edges)
    unseen=set(adj)
    result=[]
    while unseen:
        root=min(unseen)
        group={root}
        stack=[root]
        while stack:
            node=stack.pop()
            fresh=adj[node]-group
            group.update(fresh)
            stack.extend(fresh)
        unseen-=group
        result.append(group)
    return result


def active_core(edges):
    e=set(edges)
    while e:
        deg=neighbors(e)
        leaves={v for v,ns in deg.items() if len(ns)==1}
        if not leaves:
            break
        e={pair for pair in e if leaves.isdisjoint(pair)}
    return e


def catalog(k):
    seen=set()
    for a in range(k//2+1):
        b=k-a
        left_cover=set(range(a))
        right_cover=set(range(a,k))
        cross=[(v,w) for v in left_cover for w in right_cover]
        neighborhoods=[]
        for shore in (left_cover,right_cover):
            for size in range(1,len(shore)+1):
                neighborhoods.extend(map(frozenset,combinations(sorted(shore),size)))
        for internal in range(1<<len(cross)):
            base={pair for j,pair in enumerate(cross) if internal&(1<<j)}
            def rec(j,selected):
                if j<len(neighborhoods):
                    group=neighborhoods[j]
                    yield from rec(j+1,selected)
                    if all(len(group&t)<=1 for t in selected):
                        yield from rec(j+1,[*selected,group])
                    return
                e=set(base)
                for off,S in enumerate(selected,k):
                    if S <= left_cover:
                        e.update((v,off) for v in S)
                    else:
                        e.update((off,w) for w in S)
                adj=neighbors(e)
                if not set(range(k))<=set(adj) or matching(e)!=k:
                    return
                if any(len(x&y)>1 for x,y in combinations(adj.values(),2)):
                    return
                if any(sum(len(adj[v])==1 for v in group)>1 for group in adj.values()):
                    return
                yield canonical(None,None,e)
            seen.update(rec(0,[]))
    return seen


def minimum_cover(edges,k):
    vertices=sorted(neighbors(edges))
    for cover in combinations(vertices,k):
        c=set(cover)
        if all(not c.isdisjoint(e) for e in edges):
            return cover
    raise AssertionError("cover smaller than the construction budget was not found")


def star_program(code):
    a,b,edges=parts(code)
    n=a+b
    cover=minimum_cover(edges,matching(edges))
    gated=[]
    def add(op,i,j):
        assert i!=j and max(i,j)<n+len(gated)
        gated.append((op,i,j))
        return n+len(gated)-1
    def join(inputs):
        i,*others=inputs
        for j in others:
            i=add("or",i,j)
        return i
    stars=[]
    for v in cover:
        owned=sorted((w if v==u else u) for u,w in edges if v in (u,w) and
                     next(c for c in cover if c in (u,w))==v)
        assert owned
        stars.append(add("and",v,join(owned)))
    root=join(stars)
    assert len(gated)==len(edges)+len(cover)-1
    for u,v in edges:
        for invert in (False,True):
            vals=[(False,z in (u,v)) if ((z>=a)!=invert) else (z in (u,v),False) for z in range(n)]
            for op,i,j in gated:
                p,q=vals[i],vals[j]
                vals.append((p[0] or q[0],p[1] or q[1]) if op=="or" else
                            (p[0] and q[0],(p[0] and q[1]) or (p[1] and q[0])))
            assert vals[root][1]
    return len(gated)


def classify(code):
    a,b,edges=parts(code)
    core=active_core(edges)
    if not core:
        return "forest"
    if len(core)==6 and all(len(ns)==2 for ns in neighbors(core).values()):
        if matching(edges)<=3:
            rest=edges-core
            core_points={v for v,_ in core}
            core_lines={w for _,w in core}
            assert all(u in core_points and w not in core_lines for u,w in rest) or all(
                w in core_lines and u not in core_points for u,w in rest)
            return "six-cycle with leaves on one shore"
    return "other cyclic"


def unique_code(edges):
    return canonical(None,None,edges)


def upper(code):
    a,b,edges=parts(code)
    return max(0,len(edges)+matching(edges)-1)


from functools import lru_cache

@lru_cache(None)
def lower(code):
    a,b,edges=parts(code)
    n=a+b
    if not edges:
        return 0
    adj=neighbors(edges)
    if not active_core(edges):
        return upper(code)
    # Removing an isolated star component costs precisely its number of inputs.
    for group in components(edges):
        if len(group)<n and any(len(adj[v])==len(group)-1 for v in group):
            remaining={e for e in edges if group.isdisjoint(e)}
            return len(group)+lower(unique_code(remaining))
    # Nonisolated false twins in a four-cycle-free graph have one common neighbor.
    for v,w in combinations(adj,2):
        if adj[v]==adj[w]:
            left={e for e in edges if w not in e}
            return 1+lower(unique_code(left))
    # Here all inputs are essential, both pins stay nonconstant, and the graph
    # has neither an isolated edge nor any pair of inputs with identical neighborhoods.
    forced = []
    bound=n-1
    for v in adj:
        zero={e for e in edges if v not in e}
        zero_cost=lower(unique_code(zero))
        bound=max(bound,n-len(neighbors(zero))+zero_cost)
        alarms=adj[v]
        one={e for e in zero if alarms.isdisjoint(e)}
        one_cost=(lower(unique_code(one))+len(alarms) if one else len(alarms)-1)
        bound=max(bound,n-len(neighbors(one))-len(alarms)+one_cost)
        forced.append(min(max(zero_cost+x,one_cost+y) for x,y in ((3,3),(4,2),(2,4))))
    bound=max(bound,min(forced))
    assert bound<=upper(code),(code,bound,upper(code))
    return bound



def add_existing_or(n, gates, x):
    """Insert a second OR reading existing raw x, preserving the topological order."""
    for wire in range(n+len(gates)):
        if wire==x:
            continue
        uses=[(j,k) for j,g in enumerate(gates) for k in (1,2) if g[k]==wire]
        if wire==n+len(gates)-1:
            uses.append((len(gates),0))
        for mask in range(1,1<<len(uses)):
            take={r for i,r in enumerate(uses) if mask & (1<<i)}
            mapping=dict(enumerate(range(n)))
            out=[]
            if wire<n:
                alt=n
                out.append((True,wire,x))
            for j,(op,a,b) in enumerate(gates):
                out.append((op,alt if (j,1) in take else mapping[a],
                            alt if (j,2) in take else mapping[b]))
                mapping[n+j]=n+len(out)-1
                if wire==n+j:
                    alt=n+len(out)
                    out.append((True,mapping[wire],x))
            yield tuple(out)

def critical_extensions():
    """Enumerate all 10-gate extensions of the optimal nine-gate C6 with a leaf."""
    from pathlib import Path
    import runpy
    helpers = runpy.run_path(str(Path(__file__).with_name("plane-small-core-bounds.py")))
    cycle = {(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)}
    base = cycle | {(6,3)}
    def columns(n):
        return [sum(((r >> i) & 1) << r for r in range(1<<n)) for i in range(n)]
    def truth(edges, cols):
        result = 0
        for u,v in edges:
            result |= cols[u] & cols[v]
        return result
    seven, eight = columns(7), columns(8)
    nine = {}
    for gates in helpers["cycle_stars"]():
        for extended in helpers["add_private"](6,gates):
            if helpers["evaluate_core"](7,extended,seven)[0] == truth(base,seven):
                nine[helpers["circuit_signature"](7,extended)] = extended
    assert len(nine)==9
    ten = {helpers["evaluate_core"](8,g,eight)[0]
           for gates in nine.values() for g in helpers["add_private"](7,gates)}
    # Enumerate both shores of the new vertex, including all relabelings of its neighbors.
    theta=(4,(3,5,9,14))
    # In a theta the six degree-two vertices are in one orbit. Check every labeling
    # extending this C6-plus-pendant by one such vertex; x=7 is always the new input.
    two_ors={helpers["evaluate_core"](8,h,eight)[0]
             for gates in nine.values() for g in helpers["add_private"](7,gates)
             for h in add_existing_or(8,g,7)}
    theta_targets=0
    ruled = set()
    for left,add_left in [([0,1,2,6],False),([3,4,5],True)]:
        for count in range(1,len(left)+1):
            for group in combinations(left,count):
                extra={(7,v) if add_left else (v,7) for v in group}
                edges=base|extra
                adj=neighbors(edges)
                if matching(edges)!=4 or any(len(x&y)>1 for x,y in combinations(adj.values(),2)):
                    continue
                if unique_code(edges)==theta:
                    assert truth(edges,eight) not in two_ors
                    theta_targets+=1
                if truth(edges,eight) not in ten:
                    ruled.add(unique_code(edges))
    assert theta_targets>0
    return ruled

@lru_cache(None)
def monotone_lower(code):
    a,b,edges=parts(code)
    bound=lower(code)
    if code in extension_bounds:
        bound=max(bound,11)
    if code==(4,(3,5,9,14)):
        bound=max(bound,12)
    if bound < upper(code):
        adj=neighbors(edges)
        groups=components(edges)
        for group in groups:
            if len(group)<a+b and any(len(adj[v])==len(group)-1 for v in group):
                rest={e for e in edges if group.isdisjoint(e)}
                return len(group)+monotone_lower(unique_code(rest))
        for v,w in combinations(adj,2):
            if adj[v]==adj[w]:
                rest={e for e in edges if w not in e}
                return 1+monotone_lower(unique_code(rest))
        forced=[]
        for v,alarms in adj.items():
            zero={e for e in edges if v not in e}
            lo=monotone_lower(unique_code(zero))
            bound=max(bound,a+b-len(neighbors(zero))+lo)
            one={e for e in zero if alarms.isdisjoint(e)}
            hi=(monotone_lower(unique_code(one))+len(alarms) if one else len(alarms)-1)
            if zero:
                # The controlling value of the first raw reader eliminates its successor too.
                bound=max(bound,min(lo,hi)+2,hi+a+b-len(neighbors(one))-len(alarms))
                forced.append(min(max(lo+x,hi+y) for x,y in ((3,3),(4,2),(2,4))))
        # The first binary raw gate cannot funnel two variables in these residual graphs.
        if len(forced)==len(adj):
            bound=max(bound,min(forced))
        shores=[set(range(a)),set(range(a,a+b))]
        # Maximize the count of implicant gates among least circuits before localizing.
        for shore in [g & side for g in groups for side in shores]+shores:
            if len(shore)<2 or len({frozenset(adj[v]) for v in shore}) != len(shore):
                continue
            pinned=[unique_code({edge for edge in edges if v not in edge}) for v in shore]
            bound=max(bound,2+min(monotone_lower(h) for h in pinned))
    assert bound<=upper(code),(code,bound,upper(code))
    return bound

extension_bounds=critical_extensions()

def degree_two_components(code):
    a,b,edges=parts(code)
    adj=neighbors(edges)
    shores=[set(range(a)),set(range(a,a+b))]
    return all(any(all(len(adj[v])<=2 for v in group & side) for side in shores)
               for group in components(edges))


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--five", action="store_true", help="include the larger fifth-cover census")
    args=parser.parse_args()
    for k in range(1,6 if args.five else 5):
        items=catalog(k)
        counts=Counter(classify(code) for code in items)
        for code in items:
            star_program(code)
        short=Counter(upper(code)-lower(code) for code in items)
        print("distance from star upper bound",dict(sorted(short.items())),flush=True)
        print(f"cover {k}: {len(items)} reduced graphs; {dict(counts)}",flush=True)
        refined=Counter(upper(code)-monotone_lower(code) for code in items)
        print("monotone distances",dict(sorted(refined.items())),flush=True)
        rank_two=[code for code in items if degree_two_components(code)]
        assert all(upper(code)==monotone_lower(code) for code in rank_two)
        print("components with a shore of degree at most two",len(rank_two),flush=True)
        if k<=4:
            assert refined=={0:len(items)}
        if k==4:
            print("ten-gate exclusions",sorted(extension_bounds))
