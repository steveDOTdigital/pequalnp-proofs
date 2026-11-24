"""Four raw OR clauses on Singer's order-three plane, with exact heptad covers."""
from itertools import combinations, permutations, product
from collections import Counter
from functools import lru_cache

LINES=tuple(frozenset((l+d)%13 for d in (0,1,3,9)) for l in range(13))
FLAGS=tuple((p,l) for p in range(13) for l,S in enumerate(LINES) if p in S)
QUADS=tuple(frozenset(q) for q in combinations(range(13),4)
            if all(len(set(q)&S)<=2 for S in LINES))
ROWS=tuple(sum(1<<i for i in q)+sum(1<<(13+j) for j,S in enumerate(LINES) if S.isdisjoint(q))
           for q in QUADS)
FULL=(1<<len(ROWS))-1
ABSENT=tuple(sum(1<<j for j,r in enumerate(ROWS) if not r&(1<<v)) for v in range(26))
EID={e:j for j,e in enumerate(FLAGS)}
JOIN={tuple(sorted((a,b))):l for l,S in enumerate(LINES) for a,b in combinations(S,2)}
MEET={tuple(sorted((a,b))):next(iter(LINES[a]&LINES[b])) for a,b in combinations(range(13),2)}

def join(a,b):
    return JOIN[tuple(sorted((a,b)))]

def meet(a,b):
    return MEET[tuple(sorted((a,b)))]

def group():
    base=sorted(QUADS[0]);known=set(base);steps=[]
    while len(known)<13:
        before=len(known)
        pairs=list(combinations(sorted(known),2))
        for (a,b),(c,d) in combinations(pairs,2):
            i,j=join(a,b),join(c,d)
            if i==j:
                continue
            v=meet(i,j)
            if v not in known:
                known.add(v);steps.append((v,a,b,c,d))
        assert len(known)>before
    result=[]
    for q in QUADS:
        for order in permutations(q):
            m=dict(zip(base,order))
            for v,a,b,c,d in steps:
                m[v]=meet(join(m[a],m[b]),join(m[c],m[d]))
            lines=[LINES.index(frozenset(m[p] for p in S)) for S in LINES]
            result.append(tuple(EID[m[p],lines[l]] for p,l in FLAGS))
    assert len(set(result))==5616
    return result

def matching(es):
    flags=[FLAGS[i] for i in es]
    return len({p for p,l in flags})==len(es) and len({l for p,l in flags})==len(es)

def orbits(k,syms):
    remaining={e for e in combinations(range(52),k) if matching(e)}
    found=[]
    while remaining:
        e=min(remaining)
        orbit={tuple(sorted(s[i] for i in e)) for s in syms}
        assert orbit<=remaining
        remaining-=orbit;found.append((e,len(orbit)))
    return found

def matching_covers(es):
    options=[]
    for choice in product((0,1),repeat=len(es)):
        clause=tuple(FLAGS[i][0] if k==0 else 13+FLAGS[i][1] for i,k in zip(es,choice))
        st=FULL
        for w in clause:st &= ABSENT[w]
        options.append((clause,st))
    for k in range(1,len(options)+1):
        for cut in combinations(range(len(options)),k):
            passed=0
            for j in cut:passed|=options[j][1]
            if passed==FULL:
                return tuple(options[j][0] for j in cut)
    raise AssertionError('An incidence and a quadrangle are disjoint as constraints.')


def dual_certificate(es):
    """Pack rows which no single matching-hitting clause can reject together."""
    flags=[FLAGS[i] for i in es]
    clauses=[tuple(p if side==0 else 13+l for (p,l),side in zip(flags,bits))
             for bits in product((0,1),repeat=len(flags))]
    masks={}
    for j,row in enumerate(ROWS):
        options=sum(1<<i for i,cl in enumerate(clauses) if all(not row&(1<<v) for v in cl))
        assert options
        masks.setdefault(options,j)
    pack={0:()}
    for pattern,j in sorted(masks.items()):
        if any(sub!=pattern and (pattern&sub)==sub for sub in masks):
            continue
        for used,witness in tuple(pack.items()):
            if not used&pattern and len(pack.get(used|pattern,()))<=len(witness):
                pack[used|pattern]=witness+(j,)
    result=max(pack.values(),key=len)
    for a,b in combinations(result,2):
        r=ROWS[a]|ROWS[b]
        assert any(r&(1<<p) and r&(1<<(13+l)) for p,l in flags)
    return result


def four_cover(es):
    """Minimum hitting set on the 16 canonical clauses of a four-matching."""
    endpoints=[FLAGS[i] for i in es]
    absences=[]
    for selection in product((0,1),repeat=4):
        rows=FULL
        for (p,l),side in zip(endpoints,selection):
            rows &= ABSENT[p if side==0 else 13+l]
        absences.append(rows)
    options={sum(1<<j for j,rows in enumerate(absences) if rows>>r&1) for r in range(len(ROWS))}
    minimal=tuple(sorted(s for s in options if not any(t!=s and (s&t)==t for t in options)))
    @lru_cache(None)
    def solve(left):
        if not left:return ()
        pivot=min(left,key=lambda s:bin(s).count('1'))
        return min(((j,)+solve(tuple(s for s in left if not s&(1<<j)))
                    for j in range(16) if pivot&(1<<j)),key=len)
    chosen=solve(minimal)
    assert all(any(s&(1<<j) for j in chosen) for s in options)
    return chosen

def one_repeat(edges,n,x):
    rows=[(i,) for i in range(n)]+list(combinations(range(n),2))
    target=sum(1<<j for j,row in enumerate(rows) if row in edges)
    raw=[sum(1<<j for j,row in enumerate(rows) if v in row) for v in list(range(n))+[x]]
    def splits(s):
        low=s&-s
        a=(s-1)&s
        while a:
            if a&low:yield a,s^a
            a=(a-1)&s
    @lru_cache(None)
    def tables(s):
        if not s&(s-1):return {raw[s.bit_length()-1]}
        funcs=set()
        for a,b in splits(s):
            u,v=tables(a),tables(b)
            funcs.update(p&q for p in u for q in v)
            funcs.update(p|q for p in u for q in v)
        return funcs
    for a,b in splits((1<<(n+1))-1):
        u,v=tables(a),tables(b)
        uo=[p for p in u if (p|target)==target];vo=[p for p in v if (p|target)==target]
        if any(p|q==target for p in uo for q in vo):return True
        ua=[p for p in u if (p&target)==target];va=[p for p in v if (p&target)==target]
        if any(p&q==target for p in ua for q in va):return True
    return False

def proxy_control():
    """Replace a point in one line star by three shared pair ORs."""
    p,target=0,0
    others=[l for l,S in enumerate(LINES) if p in S and l!=target]
    transversal=next(S for S in LINES if p not in S)
    partners=[next(iter((LINES[l]&transversal))) for l in others]
    gates=[]
    def gate(op,a,b):
        assert a!=b and max(a,b)<26+len(gates)
        gates.append((op,a,b))
        return 25+len(gates)
    def disjoin(wires):
        a,*rest=wires
        for b in rest:a=gate('or',a,b)
        return a
    helpers=[gate('or',p,b) for b in partners]
    proxy=gate('and',gate('and',helpers[0],helpers[1]),helpers[2])
    stars=[]
    for l,S in enumerate(LINES):
        if l==target:
            pts=[proxy]+sorted(S-{p})
        elif l in others:
            j=others.index(l)
            pts=[helpers[j]]+sorted(S-{p,partners[j]})
        else:pts=sorted(S)
        stars.append(gate('and',13+l,disjoin(pts)))
    out=disjoin(stars)
    ancestors=[set() for _ in range(26)]
    nested=0
    for j,(op,a,b) in enumerate(gates):
        below=ancestors[a]|ancestors[b]
        nested+=len(below) if op=='and' else 0
        ancestors.append(below|({j} if op=='and' else set()))
    def tape(row):
        vals=[bool(row&(1<<v)) for v in range(26)]
        for op,a,b in gates:
            vals.append((vals[a] and vals[b]) if op=='and' else (vals[a] or vals[b]))
        return vals
    neg=[tape(row) for row in ROWS]
    assert all(tape((1<<p)|(1<<(13+l)))[out] for p,l in FLAGS)
    assert all(not vs[out] for vs in neg)
    witnesses={(j,i):next(n for n,vs in enumerate(neg) if vs[26+j]!=vs[i])
               for j,(op,a,b) in enumerate(gates) if op=='and' for i in (a,b)}
    assert (len(gates),nested,len(witnesses))==(66,3,30)
    return gates,witnesses

if __name__=='__main__':
    syms=group()
    for k in (2,3):
        states=orbits(k,syms)
        counts=Counter()
        for e,num in states:
            cover=matching_covers(e)
            certificate=dual_certificate(e)
            assert len(certificate)==len(cover)
            counts[len(cover)]+=num
            print('matching',k,tuple(FLAGS[i] for i in e),'orbit',num,'clauses',len(cover),'point masks',tuple(sum(1<<p for p in QUADS[j]) for j in certificate),flush=True)
        assert counts==({3:468,4:702} if k==2 else {5:6084,6:6084,7:1872,8:936})
        print(k,'matching orbit totals',dict(sorted(counts.items())),flush=True)

    gates,witnesses=proxy_control()
    print('Control:',len(gates),'gates, three AND-ancestor pairs,',len(witnesses),'strict operands')

    counts=Counter()
    for e,num in orbits(4,syms):
        cover=four_cover(e)
        certificate=dual_certificate(e)
        assert len(certificate)==len(cover)
        counts[len(cover)]+=num
        print('matching',4,tuple(FLAGS[i] for i in e),'orbit',num,'clauses',len(cover),
              'point masks',tuple(sum(1<<p for p in QUADS[j]) for j in certificate))
    assert counts=={6:1521,7:9360,8:52416,9:29016,10:19656,11:5616,12:2808,15:234}
    print('4-matching orbit totals',dict(sorted(counts.items())))
    path={(i,i+1) for i in range(5)}
    fork={(0,1),(0,2),(0,3),(1,4),(2,5)}
    assert not any(one_repeat(E,6,x) for E in (path,fork) for x in range(6))
    print('Both six-vertex forest cores exclude a repeated input in all 12 positions.')
