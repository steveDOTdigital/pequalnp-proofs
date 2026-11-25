"""Verify shared raw OR cases against the 52 posted L-meta-650 flags."""
from functools import lru_cache
from itertools import combinations, permutations
from collections import Counter

ROWS = [[0,1,3,9],[0,2,8,12],[1,7,11,12],[0,6,10,11],[5,9,10,12],[4,8,9,11],[3,7,8,10],[2,6,7,9],[1,5,6,8],[0,4,5,7],[3,4,6,12],[2,3,5,11],[1,2,4,10]]
FLAGS = [(p,l) for p,line_indices in enumerate(ROWS) for l in line_indices]
POINTS = range(13)
PAIRS = tuple(combinations(POINTS,2))
LINES = tuple(frozenset(p for p,l in FLAGS if l==w) for w in POINTS)
NEIGH = tuple(frozenset(row) for row in ROWS)
JOIN = {(a,b): next(iter(NEIGH[a] & NEIGH[b])) for a,b in permutations(POINTS,2)}
MEET = {(a,b): next(iter(LINES[a] & LINES[b])) for a,b in permutations(POINTS,2)}
FLAGS_SET = frozenset(FLAGS)
assert all(len(NEIGH[a] & NEIGH[b]) == len(LINES[a] & LINES[b]) == 1 for a,b in PAIRS)

def frames():
    for f in permutations(POINTS,4):
        if all(JOIN[a,b] != JOIN[a,c] for a,b,c in combinations(f,3)):
            yield f

def collineations():
    # A projective frame generates the order-three plane by joins and meets.
    it = frames()
    base = next(it)
    known = [set(base),set()]
    recipe = []
    while len(known[0])+len(known[1]) < 26:
        previous = len(recipe)
        for side,op in enumerate((JOIN,MEET)):
            for a,b in combinations(sorted(known[side]),2):
                c = op[a,b]
                if c not in known[1-side]:
                    known[1-side].add(c)
                    recipe.append((side,a,b,c))
        assert len(recipe)>previous
    group = []
    for image in frames():
        mapping = [dict(zip(base,image)),{}]
        for side,a,b,c in recipe:
            mapping[1-side][c]=(JOIN,MEET)[side][mapping[side][a],mapping[side][b]]
        p,l = mapping
        assert len(set(p.values()))==len(set(l.values()))==13
        assert all((p[a],l[b]) in FLAGS_SET for a,b in FLAGS)
        group.append((tuple(p[i] for i in POINTS),tuple(l[i] for i in POINTS)))
    assert len(set(group))==5616
    return group

def point_orbits(count,group):
    remaining=set(combinations(PAIRS,count))
    while remaining:
        basis=min(remaining)
        orbit={tuple(sorted(tuple(sorted((g[a],g[b]))) for a,b in basis)) for g,_ in group}
        yield basis,len(orbit)
        remaining.difference_update(orbit)

@lru_cache(None)
def matching(removed):
    rows=[tuple(l for l in row if (p,l) not in removed) for p,row in enumerate(ROWS)]
    owner={}
    def augment(p,seen):
        for l in rows[p]:
            if l in seen:continue
            seen.add(l)
            if l not in owner or augment(owner[l],seen):
                owner[l]=p
                return True
        return False
    return sum(augment(p,set()) for p in POINTS)

def pair_bound(points,lines):
    removed=set()
    for a,b in points:
        w=JOIN[a,b]
        removed.update(((a,w),(b,w)))
    for v,w in lines:
        p=MEET[v,w]
        removed.update(((p,v),(p,w)))
    # Exceptional edges can have conflicting partners in the comparison column.
    clashes=set()
    for a,b in points:
        for v,w in lines:
            for on,opposite in (((a,v),(b,w)),((a,w),(b,v))):
                if on in FLAGS_SET and opposite in FLAGS_SET:clashes.update((on,opposite))
    clashes.difference_update(removed)
    bad_points={p for p,l in clashes}
    bad_lines={l for p,l in clashes}
    cut=removed | {(p,l) for p,l in FLAGS if p in bad_points or l in bad_lines}
    penalty=len(bad_points)+len(bad_lines)-len(clashes)+matching(frozenset(cut))
    raw=52-len(removed)+penalty
    return raw+3*(len(points)+len(lines))-1

def cross_bound(helpers):
    # On a nonincident mixed helper, point and line end-stars may both be exceptional.
    # On an incident mixed helper only that single flag can be exceptional.
    exceptional=set()
    for p,l in helpers:
        if (p,l) in FLAGS_SET:
            exceptional.add((p,l))
        else:
            exceptional.update((a,b) for a,b in FLAGS if p==a or l==b)
    bad_points={a for a,b in exceptional}
    bad_lines={b for a,b in exceptional}
    cut=frozenset((a,b) for a,b in FLAGS if a in bad_points or b in bad_lines)
    residual=matching(cut)
    return 52+len(bad_points)+len(bad_lines)-len(exceptional)+residual+3*len(helpers)-1

def restricted_cross(helpers,removed):
    h=FLAGS_SET-removed
    line_partners=[{l for a,l in helpers if a==p} for p in POINTS]
    point_partners=[{p for p,b in helpers if b==l} for l in POINTS]
    exceptional=set()
    for p,l in h:
        x,y=line_partners[p],point_partners[l]
        if not x and not y:continue
        ws=[w for w in NEIGH[p] if w!=l and (p,w) in h]
        qs=[q for q in LINES[l] if q!=p and (q,l) in h]
        if not ws or not qs:continue
        if (l in x or p in y or any((q,w) in FLAGS_SET for q in y for w in x)
            or any((q,w) in FLAGS_SET for q in qs for w in x)
            or any((q,w) in FLAGS_SET for q in y for w in ws)):
            exceptional.add((p,l))
    ps={a for a,b in exceptional}
    ls={b for a,b in exceptional}
    cut=removed | frozenset((a,b) for a,b in FLAGS if a in ps or b in ls)
    return len(h)+len(ps)+len(ls)-len(exceptional)+matching(cut)+3*len(helpers)-1

def mixed(group):
    choices=tuple((p,l) for p in POINTS for l in POINTS)
    for k in (1,2):
        remaining=set(combinations(choices,k))
        outcomes=Counter()
        while remaining:
            basis=min(remaining)
            orbit={tuple(sorted((g[p],j[l]) for p,l in basis)) for g,j in group}
            remaining.difference_update(orbit)
            bound=cross_bound(basis)
            if bound<64:
                projection=sorted({(MEET[w,l],w) for p,l in basis if l not in NEIGH[p] for w in NEIGH[p]})
                for count in range(1,len(projection)+1):
                    for sub in combinations(projection,count):
                        bound=max(bound,restricted_cross(basis,frozenset(sub)))
                        if bound>=64:break
                    if bound>=64:break
            outcomes[bound]+=len(orbit)
            matching.cache_clear()
        print('cross-shore ORs with projection restrictions',k,sorted(outcomes.items()),flush=True)
        if k==1:assert outcomes=={64:117,67:52}

# All vertices use the posted 0..25 labels in this mixed check.
FULL=frozenset((p,l+13) for p,l in FLAGS)
ADJ=tuple(frozenset(w+13 for w in NEIGH[v]) if v<13 else LINES[v-13] for v in range(26))

def independent(vertices):
    return all(ADJ[v].isdisjoint(vertices) for v in vertices)

def general_price(helpers,omit=frozenset(),orient=()):
    partners=[set() for i in range(26)]
    for index,(a,b) in enumerate(helpers):
        paid=orient[index] if orient else None
        if paid!=a:partners[a].add(b)
        if paid!=b:partners[b].add(a)
    keep=frozenset((p,l) for p,l in FULL-omit if independent(partners[p]|{l}) and independent(partners[l]|{p}))
    adjacent=[set() for i in range(26)]
    for p,l in keep:
        adjacent[p].add(l)
        adjacent[l].add(p)
    clashes=set()
    candidates=set()
    for p,l in keep:
        required=partners[p]|partners[l]
        for other_l in adjacent[p]-{l}:
            for other_p in adjacent[l]-{p}:
                witnesses=required|{other_p,other_l}
                if p in witnesses or l in witnesses or not independent(witnesses):
                    clashes.add((p,l))
                    candidates.update(((p,l),(p,other_l),(other_p,l)))
    ps={p for p,l in clashes}
    ls={l for p,l in clashes}
    cut=frozenset((p,l-13) for p,l in FULL if (p,l) not in keep or p in ps or l in ls)
    price=len(keep)+len(ps)+len(ls)-len(clashes)+matching(cut)+3*len(helpers)-1-2*sum(v is not None for v in orient)
    return price,candidates

def mixed_with_point(group):
    remaining={((a,b),(p,l+13)) for a,b in PAIRS for p in POINTS for l in POINTS}
    values=Counter()
    while remaining:
        basis=min(remaining)
        (a,b),(p,l)=basis
        orbit={(tuple(sorted((g[a],g[b]))),(g[p],j[l-13]+13)) for g,j in group}
        remaining.difference_update(orbit)
        bound,candidates=general_price(basis)
        if bound<64:
            for i,(first,second) in enumerate(basis):
                for paid in (first,second):
                    labels=tuple(paid if j==i else None for j in range(len(basis)))
                    bound=max(bound,general_price(basis,orient=labels)[0])
        if bound<64:
            for k in (1,2,3):
                for cut in combinations(sorted(candidates),k):
                    bound=max(bound,general_price(basis,frozenset(cut))[0])
                    if bound>=64:break
                if bound>=64:break
        values[bound]+=len(orbit)
        matching.cache_clear()
    print('one point-pair OR and one cross-shore OR',sorted(values.items()),flush=True)

def main():
    group=collineations()
    for left,right in ((1,1),(2,1),(2,2),(3,1)):
        outcomes=Counter()
        for choice,n in point_orbits(left,group):
            for others in combinations(PAIRS,right):
                outcomes[pair_bound(choice,others)]+=n
            matching.cache_clear()
        print((left,right),sorted(outcomes.items()),flush=True)
    mixed(group)
    mixed_with_point(group)

if __name__=='__main__':main()
