"""Integer-checked rectangle prices for the 468 generic order-three plane tests.

Run with Python 3, NumPy and SciPy. The optimizer only proposes weights.
All lower bounds printed by this program are recomputed in integer arithmetic.
"""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import argparse
import math
import runpy

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

root = Path(__file__).resolve().parent
previous = runpy.run_path(str(root / 'quadrangle-shared-bound.py'))
edges, incident, banks = (previous[k] for k in ('edges', 'es', 'banks'))
perms = previous['perms']
seeds = [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
columns = set()
for (p,l), k, j, dual in product(seeds,(1,3,9),range(13),(False,True)):
    def translate(word):
        return sum(1 << i for i in range(13) if word >> (((-1 if dual else 1)*(k*i+j))%13) & 1)
    if dual:
        p,l=l,p
    columns.add(translate(p) | translate(l)<<13)
columns = sorted(columns)
assert len(columns)==468 and all(not any(c>>a&c>>b&1 for a,b in edges) for c in columns)
edge_index = {e:i for i,e in enumerate(edges)}
column_index = {c:i for i,c in enumerate(columns)}
col_vertices = [[v for v in range(26) if c>>v&1] for c in columns]
tape = [sum(1<<t for t,c in enumerate(columns) if c>>v&1) for v in range(26)]
all_columns = (1<<len(columns))-1
counts = np.full((len(banks),16,16),99,dtype=np.int16)
for f,(k,d,choices) in enumerate(banks):
    for need in range(16):
        for charge in range(16):
            allowed=[bin(a&charge).count('1') for a in choices if need&~a==0]
            if allowed: counts[f,need,charge]=min(allowed)

def orbits(images):
    groups = []
    left = set(range(len(images[0])))
    while left:
        v = min(left)
        group = sorted({im[v] for im in images})
        assert set(group)<=left
        groups.append(group)
        left.difference_update(group)
    return groups

def price(support,allow_extra=False,refine=False,override=None,pair_ref=None):
    vertices = [v for v in range(26) if support>>v&1]
    stabilizer=[g for g in perms if sum(1<<g[v] for v in vertices)==support]
    if override is not None:stabilizer=override[0]
    flags=orbits([[edge_index[g[a],g[b]] for a,b in edges] for g in stabilizer])
    cols=orbits([[column_index[sum(1<<g[v] for v in vs)] for vs in col_vertices] for g in stabilizer])
    hot=set(range(52)) if allow_extra else {i for i,(a,b) in enumerate(edges) if a in vertices or b in vertices}
    warm=sum(1<<t for t,c in enumerate(columns) if c&support)
    if override is not None:hot,warm=override[1:3]
    full=(1<<52)-1
    hotmask=sum(1<<e for e in hot)
    required=(override[3] if override is not None and len(override)>3 else
              [full if warm>>t&1 else full & ~hotmask for t in range(len(columns))])
    col_required=[sum(1<<t for t,r in enumerate(required) if r>>e&1) for e in range(52)]
    eligible=[]
    for i,(p,l) in enumerate(edges):
        good=True
        for j in incident[l]:
            for k in incident[p]:
                if i==j or i==k:continue
                witnesses=tape[edges[j][0]] & tape[edges[k][1]]
                witnesses &= col_required[j] & col_required[k]
                if not witnesses:good=False
        eligible.append(good)
    flags=[f for f in flags if eligible[f[0]]]
    assert all(all(eligible[i] for i in f) for f in flags)
    flagclass={e:j for j,f in enumerate(flags) for e in f}
    sets=[set(range(52))]
    if refine:
        classes=orbits([[edge_index[g[a],g[b]] for a,b in edges] for g in stabilizer])
        choose=range(1,len(classes)) if len(classes)<=7 else [1,len(classes)-1]
        for k in choose:
            for ids in combinations(range(len(classes)),k):sets.append({e for j in ids for e in classes[j]})
    features=[(Q,cols) for Q in sets]
    if pair_ref is not None:
        helpers=pair_ref
        parts={}
        for e,(a,b) in enumerate(edges):
            def relation(S):
                return (bool(S>>a&1),bool(S>>b&1),
                    sum(bool(S>>edges[i][1]&1) for i in incident[a]),
                    sum(bool(S>>edges[i][0]&1) for i in incident[b]))
            key=tuple(sorted(relation(h) for h in helpers))
            parts.setdefault(key,set()).add(e)
        buckets={}
        for t,c in enumerate(columns):
            key=(bin(c&8191).count('1'),tuple(sorted(bin(c&h).count('1') for h in helpers)))
            buckets.setdefault(key,[]).append(t)
        small=list(buckets.values());states=list(parts.values())
        candidates={frozenset(Q) for Q in states}
        candidates.update(frozenset(set(range(52))-Q) for Q in states)
        candidates.update(frozenset(Q|R) for Q,R in combinations(states,2))
        features.extend((Q,small) for Q in sorted(candidates,key=lambda q:tuple(sorted(q))) if Q and len(Q)<52)
    costcols=[sum(bin(sum(1<<e for e in Q)&required[t]).count('1') for t in c) for Q,groups in features for c in groups]
    objective=np.array(costcols+[len(f) for f in flags]+[-1]*26,dtype=np.int64)
    constraints=[]; rhs=[]; local=[]
    for v in range(26):
        neighbors=[b if a==v else a for a,b in (edges[i] for i in incident[v])]
        forced=[]; charges=[]
        for t,c in enumerate(columns):
            charge=0 if c>>v&1 else sum(1<<j for j,e in enumerate(incident[v]) if required[t]>>e&1)
            forced.append(charge & sum(1<<j for j,b in enumerate(neighbors) if c>>b&1))
            charges.append(charge)
        prices=counts[:,forced,charges]
        good=np.flatnonzero(np.max(prices,axis=1)<99)
        summands=[]
        for Q,groups in features:
            mark=sum(1<<i for i,e in enumerate(incident[v]) if e in Q)
            # Compulsory rows remain forced, even when they have zero price.
            local_cost=counts[:,forced,[a&mark for a in charges]][good]
            summands.extend(local_cost[:,cs].sum(axis=1) for cs in groups)
        dom=np.zeros((len(good),len(flags)),dtype=np.int64)
        for ix,f in enumerate(good):
            for j,e in enumerate(incident[v]):
                if banks[f][1]>>j&1 and eligible[e]:dom[ix,flagclass[e]]+=1
        # Repeated families with the same coefficients give the same inequality.
        terms=np.column_stack(summands+[dom]+[np.array([banks[f][0] for f in good])])
        terms=np.unique(terms,axis=0)
        local.append(terms)
        for row in terms:
            constraint=np.zeros(len(objective),dtype=np.int64)
            constraint[:-26]=-row[:-1];constraint[-26+v]=1
            constraints.append(constraint);rhs.append(row[-1])
    result=linprog(objective,A_ub=csr_matrix(np.array(constraints)),b_ub=rhs,
        bounds=[(0,4)]*len(costcols)+[(0,8)]*len(flags)+[(None,None)]*26,method='highs')
    assert result.success,result.message
    scale=100000
    weights=np.rint(np.maximum(0,result.x[:-26])*scale).astype(np.int64)
    # Each local coefficient counts at most four reports per column. A global
    # capacity counts at most 52. Check the worst integer dot products before use.
    bound=len(weights)*int(max(weights,default=0))*len(columns)
    assert 26*(4*scale+4*bound)+52*bound < 2**63
    lower=sum(int(np.min(terms[:,-1]*scale + terms[:,:-1]@weights)) for terms in local)
    lower-=int(objective[:-26]@weights)
    return (lower+scale-1)//scale,lower/scale,len(hot),len(flags),len(cols)


def four_leaf_residuals():
    # The exceptional four-leaf term is a product of two two-variable ORs.
    # Three hot flags form an induced path; only its missing corner can heat
    # a negative column. The extra singleton can be placed at any other vertex.
    seen=set()
    solved=[]
    for a,b in edges:
        for c,other in edges:
            if other!=b or a==c:continue
            for p,d in edges:
                if p!=c or b==d or (a,d) in edge_index:continue
                for s in range(26):
                    key=(a,b,c,d,s)
                    if s in (a,b,c,d) or key in seen:continue
                    seen.update(tuple(g[i] for i in key) for g in perms)
                    stab=[g for g in perms if all(g[i]==i for i in key)]
                    hot=set(incident[s]) | {edge_index[a,b],edge_index[c,b],edge_index[c,d]}
                    warm=tape[s] | (tape[a]&tape[d])
                    ans=price(1<<s,override=(stab,hot,warm))
                    print('four-leaf path and singleton',key,ans,flush=True)
                    solved.append(ans[0])
    assert len(seen)==52*3*3*22
    assert len(solved)==6 and min(solved)>58
    print('four-leaf residual raw bounds',sorted(Counter(solved).items()),flush=True)


def exceptional_residuals(gates):
    # A connected nonstar tree on at most five vertices must contain a
    # four-vertex path. Start with those paths, then extend by one vertex.
    path_masks=set()
    for a,b in edges:
        for c,k in edges:
            if k!=b or c==a:continue
            for j,d in edges:
                if j==c and b!=d and (a,d) not in edge_index:
                    path_masks.add(sum(1<<i for i in (a,b,c,d)))
    assert len(path_masks)==468
    extended=set()
    for base in path_masks:
        for i in range(26):
            if base>>i&1:continue
            mask=base|(1<<i)
            if sum(bool(mask>>a&mask>>b&1) for a,b in edges)==4:extended.add(mask)
    families=[path_masks,extended]
    while len(families)+3<gates:
        larger=set()
        for mask in families[-1]:
            for a,b in edges:
                if bool(mask>>a&1)!=bool(mask>>b&1):larger.add(mask|(1<<a)|(1<<b))
        families.append(larger)
    warm_only={}
    for n,family in enumerate(families,4):
        s=gates+1-n
        if s<1:continue
        seen_shapes=set()
        for mask in sorted(family):
            if mask in seen_shapes:continue
            shape=[i for i in range(26) if mask>>i&1]
            images=[sum(1<<g[i] for i in shape) for g in perms]
            seen_shapes.update(images)
            stab=[g for g,m in zip(perms,images) if m==mask]
            covered=set()
            got=[]
            for S in combinations([i for i in range(26) if i not in shape],s):
                if S in covered:continue
                orbit={tuple(sorted(g[i] for i in S)) for g in stab}
                covered.update(orbit)
                stabilize=[g for g in stab if tuple(sorted(g[i] for i in S))==S]
                hot={j for j,(a,b) in enumerate(edges) if a in S or b in S or (a in shape and b in shape)}
                points=0;lines=0;singles=0
                for v in shape:
                    if v<13:points |= tape[v]
                    else:lines |= tape[v]
                for v in S:singles |= tape[v]
                support=sum(1<<v for v in S)
                # On columns containing any singleton the raw leaves must serve every flag.
                # This bound is independent of the rest of the helper.
                if s>=2 and gates>=6:
                    canonical=min(sum(1<<g[v] for v in S) for g in perms)
                    if canonical not in warm_only:warm_only[canonical]=price(canonical,allow_extra=True)[0]
                    if warm_only[canonical]>62-gates:
                        got.append(warm_only[canonical]);continue
                result=price(support,override=(stabilize,hot,singles | (points&lines)))
                got.append(result[0])
                if result[0]<=62-gates:print('unresolved',gates,'gate shape',shape,S,result,flush=True)
            assert len(covered)==math.comb(26-len(shape),s)
            assert min(got)>62-gates
            print(gates,'gate shape',shape,'support placements',len(got),'raw bounds',sorted(Counter(got).items()),flush=True)
        assert seen_shapes==family


def two_pairs(refine=False):
    pairs=[sum(1<<i for i in p) for p in combinations(range(26),2)]
    seen=set()
    result_counts=Counter()
    for left,right in combinations(sorted(pairs),2):
        if (left,right) in seen:continue
        a=[i for i in range(26) if left>>i&1]; b=[i for i in range(26) if right>>i&1]
        images=[tuple(sorted((sum(1<<g[i] for i in a),sum(1<<g[i] for i in b)))) for g in perms]
        seen.update(images)
        stab=[g for g,key in zip(perms,images) if key==(left,right)]
        hot1=sum(1<<j for j,e in enumerate(edges) if any(i in e for i in a))
        hot2=sum(1<<j for j,e in enumerate(edges) if any(i in e for i in b))
        full=(1<<52)-1
        required=[full & ~(0 if c&left else hot1) & ~(0 if c&right else hot2) for c in columns]
        result=price(0,override=(stab,set(),0,required))
        if refine and result[0]<=58:
            result=price(0,override=(stab,set(),0,required),pair_ref=(left,right))
        result_counts[result[0]]+=1
        if result[0]<=58:print('unresolved raw pairs',a,b,result,flush=True)
    assert len(seen)==math.comb(len(pairs),2)
    if refine:assert min(result_counts)>58
    print('two raw pairs',sum(result_counts.values()),sorted(result_counts.items()),flush=True)


def many_on_four(nested=False,pair_count=3):
    # Enumerate labeled networks on at most four raw inputs up to projectivities.
    reps=[0]
    done=Counter(); minimum=Counter()
    for n in range(1,5):
        reps=previous['orbit_reps'](n,reps)
        if n<3 or (nested and n!=3):continue
        for S in reps:
            vs=[i for i in range(26) if S>>i&1]
            stab=[g for g in perms if sum(1<<g[i] for i in vs)==S]
            pairs=[sum(1<<i for i in p) for p in combinations(vs,2)]
            if nested:choices=[(a,S) for a in pairs]
            else:choices=combinations(pairs,pair_count)
            seen=set()
            for helpers in choices:
                if (not nested and set(v for v in vs if any(h>>v&1 for h in helpers))!=set(vs)):continue
                key=tuple(sorted(helpers))
                if key in seen:continue
                atom=[[i for i in vs if h>>i&1] for h in key]
                images=[tuple(sorted(sum(1<<g[i] for i in a) for a in atom)) for g in stab]
                seen.update(images)
                fix=[g for g,im in zip(stab,images) if im==key]
                masks=[sum(1<<j for j,(p,l) in enumerate(edges) if h>>p&1 or h>>l&1) for h in key]
                required=[]
                for c in columns:
                    r=(1<<52)-1
                    for h,m in zip(key,masks):
                        if not c&h:r &= ~m
                    required.append(r)
                cost=59 if nested else 64-3*pair_count
                ans=price(0,override=(fix,set(),0,required))
                if ans[0]<=cost:ans=price(0,override=(fix,set(),0,required),pair_ref=key)
                minimum[ans[0]]+=1;done[n]+=1
                if ans[0]<=cost:print('unresolved joint',key,ans,flush=True)
            if nested:
                expected={tuple(sorted((h,S))) for h in pairs}
            else:
                expected={tuple(sorted(hs)) for hs in combinations(pairs,pair_count)
                          if all(any(h>>i&1 for h in hs) for i in vs)}
            assert seen==expected
    assert min(minimum)>(59 if nested else 64-3*pair_count)
    print('nested' if nested else f'{pair_count} pairs on four','cases',sorted(done.items()),'raw bounds',sorted(minimum.items()),flush=True)

def raw_disjunctions():
    reps=[0]
    for size in range(1,5):
        reps=previous['orbit_reps'](size,reps)
        if size<2:continue
        results=[]
        for mask in reps:
            result=price(mask)
            if result[0]<=63-size:
                result=price(mask,refine=True)
            assert result[0]>63-size
            results.append(result[0])
        print('raw disjunction size',size,'bounds',sorted(Counter(results).items()),flush=True)


def main():
    cases={
        'raw-disjunctions':raw_disjunctions,
        'four-gate-helper':four_leaf_residuals,
        'five-gate-helper':lambda:exceptional_residuals(5),
        'six-gate-helper':lambda:exceptional_residuals(6),
        'two-pairs':lambda:two_pairs(refine=True),
        'nested-disjunctions':lambda:many_on_four(nested=True),
        'three-pairs':lambda:many_on_four(pair_count=3),
        'four-pairs':lambda:many_on_four(pair_count=4),
        'five-pairs':lambda:many_on_four(pair_count=5),
        'six-pairs':lambda:many_on_four(pair_count=6),
    }
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=list(cases),help='run only the selected proof check')
    choice=parser.parse_args().case
    for name,check in cases.items():
        if choice is None or name==choice:check()


if __name__=='__main__':
    main()
