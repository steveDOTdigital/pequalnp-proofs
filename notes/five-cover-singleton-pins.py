"""Enumerate cover-five incidence graphs and bound costs under one- and two-vertex pins."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import runpy

library = runpy.run_path(str(Path(__file__).with_name('single-read-cover-kernels.py')))
parts = library['parts']
neighbors = library['neighbors']
matching = library['matching']
components = library['components']
catalog = library['catalog']


def compressed(edges):
    """Canonicalize row permutations only within tied invariant degree profiles."""
    if not edges:
        return 0, ()
    adj = neighbors(edges)
    def oriented(left, right):
        buckets = {}
        for v in left:
            key = (len(adj[v]), tuple(sorted(len(adj[w]) for w in adj[v])))
            buckets.setdefault(key, []).append(v)
        orders = [permutations(buckets[k]) for k in sorted(buckets)]
        best = None
        for blocks in product(*orders):
            label = {v:i for i,v in enumerate(v for block in blocks for v in block)}
            rows = tuple(sorted(sum(1<<label[v] for v in adj[w]) for w in right))
            if best is None or rows < best:
                best = rows
        return len(left), best
    left, right = set(v for v,w in edges), set(w for v,w in edges)
    options = []
    if len(left) <= len(right):
        options.append(oriented(left, right))
    if len(right) <= len(left):
        options.append(oriented(right, left))
    return min(options)


def tree_like(edges):
    return all(sum(a in group for a,b in edges) <= len(group)
               for group in components(edges))


def pendant_centers(edges, budget):
    adj = neighbors(edges)
    return {p for p in adj if len(adj[p]) >= 3
            and any(len(adj[z]) == 1 for z in adj[p])
            and budget - bound(compressed({e for e in edges if p not in e})) <= 3}


def marks_without(edges, omitted):
    adj = neighbors(edges)
    bare = {v for v in adj if len(adj[v]) >= 2} - omitted
    return matching({(v,w) for v,w in edges if v in bare and w in bare})


@lru_cache(None)
def bound(code):
    a, b, edges = parts(code)
    if not edges:
        return 0
    adj = neighbors(edges)
    n = len(adj)
    upper = len(edges) + matching(edges) - 1
    if matching(edges) <= 4 or tree_like(edges) or library['degree_two_components'](code):
        return upper
    for group in components(edges):
        if len(group) < n:
            tree = {(x,y) for x,y in edges if x in group}
            if len(tree) == len(group)-1:
                return len(tree) + matching(tree) + bound(compressed(edges-tree))
    for v,w in combinations(adj,2):
        if adj[v] == adj[w]:
            return 1 + bound(compressed({e for e in edges if w not in e}))

    def pin(values):
        fixed = set(values)
        high = {v for v in values if values[v]}
        if any(x in high and y in high for x,y in edges):
            return None
        alarms = set().union(*(adj[v] for v in high)) - fixed
        omitted = fixed | alarms
        rest = {e for e in edges if omitted.isdisjoint(e)}
        if not rest:
            return (len(alarms)-1,len(alarms)) if alarms else None
        return bound(compressed(rest))+len(alarms),len(neighbors(rest))+len(alarms)

    # A nonconstant restriction also forgets all inputs outside its support.
    lower = n-1
    singles = {}
    excluded = {}
    for v in adj:
        for bit in (0,1):
            result = pin({v:bit})
            if result:
                singles[v,bit] = result[0]
                excluded[v,bit] = n-result[1]
                lower = max(lower,n-result[1]+result[0])
        if (v,0) in singles and (v,1) in singles:
            lower = max(lower,2+min(singles[v,0],singles[v,1]))
    if lower == upper:
        return upper
    for group in components(edges):
        for side in [set(range(a)),set(range(a,a+b))]:
            s = side & group
            if len(s)>=2 and len({frozenset(adj[v]) for v in s})==len(s):
                lower = max(lower,2+min(singles[v,0] for v in s))
    if lower == upper:
        return upper
    centers = pendant_centers(edges, upper-1)
    lower = max(lower,min(upper,n-1+len(centers)+marks_without(edges,centers)))
    if all(len(adj[v]) >= 2 for v in adj) and len(edges)>n:
        lower = max(lower,n+matching(edges))
    if lower == upper:
        return upper
    double = {}
    for v,w in combinations(sorted(adj),2):
        for h,j in product((0,1),repeat=2):
            result = pin({v:h,w:j})
            if result:
                double[v,w,h,j] = result
                lower = max(lower,n-result[1]+result[0])
    if lower == upper:
        return upper
    def essential(v,w,bit):
        if not bit:
            return bool(adj[v] - {w})
        return w in adj[v] or bool(adj[v]-adj[w]-{w}) and v not in adj[w]
    # Each first gate is on two distinct raw inputs. An AND on a nonedge
    # misses all positive edge rows and can be replaced by false.
    def first_bound(v,w,op):
        required = lower
        rv=1+int(essential(v,w,op))
        rw=1+int(essential(w,v,op))
        for x,r in ((v,rv),(w,rw)):
            if r >= 2:
                zero, one = singles[x,0], singles[x,1]
                mixed = max(zero+3,one+3)
                same = max(zero+2+2*int(op==0),one+2+2*int(op==1))
                required=max(required,min(mixed,same))
            for t in (0,1):
                if (x,t) in singles:
                    other = w if x==v else v
                    other_r = rw if x==v else rv
                    keep_other = essential(other,x,t)
                    payment = excluded[x,t] + r-1
                    payment += int(not keep_other)*(other_r-1)
                    payment += int(t==op and keep_other)
                    required=max(required,singles[x,t]+payment,
                                 singles[x,t]+r+int(t==op))
        for t,u in product((0,1),repeat=2):
            if (v,w,t,u) not in double:
                continue
            # Fixing raw sources removes at least their total number of input
            # occurrences, including the shared first gate, in a nonconstant cofactor.
            cost, support = double[v,w,t,u]
            required=max(required, cost+n-support+rv+rw-2)
        return required
    choices=[first_bound(v,w,op) for v,w in combinations(sorted(adj),2) for op in (0,1)
             if op==1 or w in adj[v]]
    lower=max(lower,min(choices))
    assert lower<=upper,(code,lower,upper)
    return lower


def saturated_core(code, budget, candidates):
    """Check each remaining candidate by counting necessary exits at a core point."""
    left, _, edges = parts(code)
    adj = neighbors(edges)
    points = set(range(left))
    core = {v for v in adj if len(adj[v]) >= 2}
    lines = core - points
    # The core and its incidence relation are the same in all twelve cases.
    core_masks = sorted(sum(1 << p for p in adj[line]) for line in lines)
    assert left == 5 and core_masks == [7,9,10,12,17,18,20,24]
    assert set(candidates) <= lines
    assert budget-len(adj)+1 == 8
    for x in candidates:
        available = core-{x}
        obligations = {e for e in edges if set(e)<=available}
        # The five cold shared marks must be exactly the five point marks.
        covers = {frozenset(chosen) for chosen in combinations(sorted(available),5)
                  if all(not set(chosen).isdisjoint(e) for e in obligations)}
        assert covers == {frozenset(points)}
        assert matching(obligations) == 5
        # Every other core line is unmarked. One distinct exit is required
        # per incident unmarked line, plus a separate birth for the edge to x.
        assert any(len(adj[p] & lines) >= 4 for p in points)


def main():
    # Relabel using the faster degree-profile ordering inside the previous
    # catalog generator. It still tests all permutations within each tied class.
    catalog.__globals__['canonical'] = lambda l,r,e:compressed(e)
    items=sorted(catalog(5))
    assert len(items)==1022
    print('catalog',len(items),flush=True)
    sizes = Counter()
    protected = Counter()
    final_cores = []
    for code in items:
        _, _, edges = parts(code)
        upper = len(edges) + 4
        lb = bound(code)
        sizes[upper-lb]+=1
        if lb == upper:
            protected['exact star']+=1
            continue
        adj = neighbors(edges)
        centers=pendant_centers(edges,upper-1)
        candidates = []
        for v, alarms in adj.items():
            rest={e for e in edges if v not in e and alarms.isdisjoint(e)}
            high=(bound(compressed(rest))+len(alarms)) if rest else len(alarms)-1
            lost = len(adj)-len(alarms)-len(neighbors(rest))
            # Use only centers whose entire closed neighborhood avoids v.
            # Their charges, and the marks in the remaining cover, are cold on v.
            far = {p for p in centers if v!=p and v not in adj[p]}
            cold_charges = len(far)+marks_without(edges,far|{v})
            from_charges = len(adj)-1+3+cold_charges
            if max(high+max(6,lost+3),from_charges)<=upper-1:
                candidates.append(v)
        if not candidates:
            protected['pin or mark bounds'] += 1
        else:
            saturated_core(code,upper-1,candidates)
            protected['saturated core']+=1
            final_cores.append((code,upper,lb,candidates))
    print('distance from star size',dict(sizes),'singleton status',dict(protected),flush=True)
    assert sizes == {0:794,1:222,2:6}
    assert protected == {'exact star':794,'pin or mark bounds':216,'saturated core':12}
    print('saturated core placements:', len(final_cores),
          'remaining singleton candidates checked:', sum(len(e[3]) for e in final_cores))

if __name__ == '__main__':
    main()
