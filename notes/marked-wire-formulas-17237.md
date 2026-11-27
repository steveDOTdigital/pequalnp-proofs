# L-meta-17237 needs internal sharing at a 45-gate budget

The [posted claim](https://data.pequalnp.com/data/lemma/L-meta-17237.0c0a82c55dd1.json) seeks a monotone 45-gate circuit with an incidence output and a marked wire. Any such witness would need a gate output reused **within the incidence cone**. The proof below excludes all formula-shaped incidence cones, including ones with arbitrary alternating AND and OR. The unrestricted claim is open.

## The incidence formula needs 44 gates

The nonisolated graph has nine points, twelve lines, 36 flags and no four-cycle. Each point has four lines and exactly one of the three marked lines. Each line has three points. If a vertex cover omits a nonempty set S of points, it must contain all their neighbours. Counting 4|S| incidences, and noting that a neighbour has fewer than four points, gives |N(S)|>|S|. The unique minimum vertex cover is therefore the nine points.

Use the [cross-rank formula bound](https://github.com/steveDOTdigital/pequalnp-proofs/blob/e4c9449f5e4b2d6ab80e45fbc7fec77cef963557/notes/FlagCrossRank.lean), or its tree-protocol proof. For a flag (p,l), the usual negative cross selects the other points of l and the other lines through p. For a marked l, add the other two marked lines to this negative test. These additions preserve independence because the three marked lines are disjoint on the retained points. They also preserve the cross incidences used in the bound. Thus with these modified crosses the proof gives 36+|K| leaves, where K is the image of the variables reported by the formula protocol on each flag and its own cross. That image is a vertex cover. This needs at least 45 leaves, hence at least 44 gates in a binary formula.

## A minimum incidence formula cannot have a subtree positive on two marked singletons

If there are exactly 45 leaves, the image K must be the nine points. Fix any line l. On the three positive flags of l and their three negative crosses, the protocol reports l precisely off the diagonal. On the diagonal it reports the point because K contains only points. Off the diagonal the positive point is on in the negative cross, so l is the only possible report. The resulting 3 by 3 matrix is the all-ones matrix minus the identity and has rank three over the rationals. Each leaf labelled l contributes one rank-one rectangle to the protocol, so l has at least three occurrences. Twelve lines then account for at least 36 leaves and the nine essential points for at least nine. At equality every line has exactly three occurrences.

Now suppose a subtree W is positive on the singletons of distinct marked lines a and b. On every positive flag of a, W is true by monotonicity. On every enhanced cross of a, W is also true because b is selected. A tree protocol follows only subtrees that are true on its positive input and false on its negative input. Thus all nine cells of the protocol matrix for a avoid W. The rank-three requirement for a is paid entirely outside W. Inside W one more occurrence of a is necessary, since W is true on a alone and has no constant true term after simplifying the formula. This contradicts the exact three occurrences of a.

## Both possible locations of the marked wire

Trim the incidence cone and simplify constants and copies. If the marked wire lies inside that cone, it is positive on all three marked singletons and is distinct from the incidence output. Fix its whole subtree to true. The resulting incidence formula is still correct on flags, singletons and all ordinary crosses. For any required negative input with points in at most two marked groups, turn on all lines avoiding its selected points. One of the three marked lines must avoid them. The marked subtree was already true on that larger negative input, so the clamped formula is false there and hence false on the original negative input. Ordinary crosses have only two selected points and fit this condition. This substitution removes the marked gate and simplifies its parent, saving at least two gates. The result would have at most 43 gates, contradicting the cross bound.

If the marked wire lies outside the incidence cone, it needs at least one gate of its own. A raw wire cannot accept all three marked singleton tests. The budget therefore forces a minimum 44-gate incidence formula and at most one outside gate. The outside gate has at most two operands. To accept three marked singleton tests, some operand must accept two of them. Such an operand must be an internal incidence wire, since a raw wire accepts at most one. The preceding rank argument excludes it.

This excludes any formula-shaped incidence cone at the assigned budget. It leaves open circuits with internal sharing.

## Extended finite search

On the 46-gate control, I also removed either of the two marked-output gates by redirecting its uses to an earlier wire. For each redirect I allowed arbitrary redefinitions at two remaining positions. The output test for a pair of positions is exact: force those two wires to each of the four Boolean pairs, then compute which branch is required in each row. The search tested 139 redirections, 137,610 pairs of positions, and 157,502,218 second definitions after first-definition filtering. None supplied a valid circuit. SAT runs for a final AND or OR also timed out on 84 rows. Their strengthened structural encoding decoded the known 47-gate AND-output control on all 720 rows.

## Geometry replay

```python
from itertools import combinations
points=tuple(i for i in range(12) if i not in (0,2,8))
lines=tuple(range(12,25))
marked=(13,15,21)
differences={0,1,3,9}
edges={(p,l) for p in points for l in lines if (p+l+2)%13 in differences}
neighbors={p:{l for a,l in edges if a==p} for p in points}
groups={l:{p for p in points if l in neighbors[p]} for l in marked}
assert len(edges)==36
assert all(len(ls)==4 and len(ls.intersection(marked))==1 for ls in neighbors.values())
assert all(len(group)==3 for group in groups.values())
assert all(len(neighbors[p]&neighbors[r])<=1 for p,r in combinations(points,2))
assert all(len(set.union(*(neighbors[p] for p in P)))>k
           for k in range(1,10) for P in combinations(points,k))

active_lines=tuple(sorted({l for p,l in edges}))
assert len(active_lines)==12
assert all(sum(l in neighbors[p] for p in points)==3 for l in active_lines)
independent=lambda pp,ll: not any((p,l) in edges for p in pp for l in ll)
for p,l in edges:
    pp={q for q in points if q!=p and l in neighbors[q]}
    ll=neighbors[p]-{l}
    assert len(pp)==2 and len(ll)==3
    assert independent(pp,ll)
    enhanced=ll|(set(marked)-{l} if l in marked else set())
    assert independent(pp,enhanced)
    assert not p in pp and l not in enhanced
    for q in points:
        if q!=p and l in neighbors[q]:assert q in pp
    for m in active_lines:
        if m!=l and m in neighbors[p]:assert m in enhanced
print('36 ordinary and enhanced crosses verified; all 12 line fibers have size three')
```

## Replay for deleting either marked gate and redefining two gates

```python
from itertools import combinations
points=tuple(i for i in range(12) if i not in (0,2,8))
lines=tuple(range(12,25))
marked=(13,15,21)
differences={0,1,3,9}
edges={(p,l) for p in points for l in lines if (p+l+2)%13 in differences}
neighbors={p:{l for a,l in edges if a==p} for p in points}
groups={l:{p for p in points if l in neighbors[p]} for l in marked}
assert len(edges)==36
assert all(len(ls)==4 and len(ls.intersection(marked))==1 for ls in neighbors.values())
assert all(len(group)==3 for group in groups.values())
assert all(len(neighbors[p]&neighbors[r])<=1 for p,r in combinations(points,2))
assert all(len(set.union(*(neighbors[p] for p in P)))>k
           for k in range(1,10) for P in combinations(points,k))
gates=[]
def gate(op,a,b):
    gates.append((op,min(a,b),max(a,b)))
    return 24+len(gates)
def join(xs):
    v,*tail=xs
    for u in tail:v=gate('or',u,v)
    return v
out=join([gate('and',p,join(sorted(neighbors[p]))) for p in points])
assert len(gates)==44
aux=join(marked)
assert len(gates)==46
def evaluate(a):
    w=[bool(a>>i&1) for i in range(25)]
    for op,x,y in gates:
        w.append((w[x] and w[y]) if op=='and' else (w[x] or w[y]))
    return w[out],w[aux]
for p,l in edges:
    assert evaluate((1<<p)|(1<<l))[0]
for l in marked:
    assert evaluate(1<<l)[1]
n0=n1=0
for k in range(10):
    for ps in combinations(points,k):
        p_mask=sum(1<<p for p in ps)
        excluded=set().union(*(neighbors[p] for p in ps))
        for test_lines in (set(lines),set(lines)-set(marked)):
            selected=test_lines-excluded
            # Isolated points always occur in maximal negative sets.
            value=evaluate(p_mask | 261 | sum(1<<l for l in selected))
            assert not value[0]
            if test_lines!=set(lines):assert not value[1]
        n0+=1
        n1+=sum(bool(set(ps)&g) for g in groups.values())<=1
print('44 gates for incidence, 46 with the marked output; checked all 36 positive pairs, three marked singletons and 512 canonical negatives per output.')
print('There are',n1,'point subsets occupying at most one marker group out of',n0)

# Enumerate new single-gate definitions and then trim gates unused by both outputs.
cases=list(dict.fromkeys(
    [(1<<p)|(1<<l) for p,l in sorted(edges)]+[1<<l for l in marked]+
    [sum(1<<p for p in ps)|261|sum(1<<l for l in ls-set().union(*(neighbors[p] for p in ps)))
     for k in range(10) for ps in combinations(points,k) for ls in (set(lines),set(lines)-set(marked))]
))
inp=[sum(1<<j for j,a in enumerate(cases) if a>>i&1) for i in range(25)]
positive=negative=auxpos=auxneg=0
ma=sum(1<<l for l in marked)
for j,a in enumerate(cases):
    if any(a>>p&1 and a>>l&1 for p,l in edges):positive|=1<<j
    else:
        negative|=1<<j
        if not a&ma:auxneg|=1<<j
    if a in [1<<l for l in marked]:auxpos|=1<<j
def passes(gs,output,marker):
    signals=inp.copy()
    for op,a,b in gs:
        signals.append(signals[a]&signals[b] if op=='and' else signals[a]|signals[b])
    return (signals[output]&positive==positive and not signals[output]&negative
            and signals[marker]&auxpos==auxpos and not signals[marker]&auxneg)
def livecount(gs,output,marker):
    used={w for w in (output,marker) if w>=25}
    for i in reversed(range(len(gs))):
        if 25+i in used:
            used.update(w for w in gs[i][1:] if w>=25)
    return len(used)
assert passes(gates,out,aux) and livecount(gates,out,aux)==46

# Check every single remaining gate against its exact output care conditions.
from time import perf_counter
def requirements(values,main,mark):
    return ((positive & ~values[main]) | (negative & values[main]) |
            (auxpos & ~values[mark]) | (auxneg & values[mark]))
def compute(gs,flip=None,initial=None):
    if flip is None:
        signals=inp.copy()
        start=0
    else:
        signals=initial[:25+flip+1]
        signals[-1]=~signals[-1]
        start=flip+1
    for op,a,b in gs[start:]:
        signals.append(signals[a]&signals[b] if op=='and' else signals[a]|signals[b])
    return signals
def search_redirects(control,output,marker):
    redirects=eligible=considered=0
    for i in range(len(control)):
        wi=25+i
        for replacement in range(wi):
            redirects+=1
            gs=[(op,replacement if a==wi else a,replacement if b==wi else b) for op,a,b in control]
            oo=replacement if output==wi else output
            aa=replacement if marker==wi else marker
            baseline=compute(gs)
            bad=requirements(baseline,oo,aa)
            if not bad:return (gs,oo,aa,(i,replacement,None)),(redirects,eligible,considered)
            for j in range(len(gs)):
                if j==i:continue
                toggled=compute(gs,j,baseline)
                bad_after_flip=requirements(toggled,oo,aa)
                if bad&bad_after_flip:continue
                eligible+=1
                current=baseline[25+j]
                for a,b in combinations(range(25+j),2):
                    if wi in (a,b):continue
                    for op,val in [('and',baseline[a]&baseline[b]),('or',baseline[a]|baseline[b])]:
                        considered+=1
                        changed=val^current
                        if (changed&bad)==bad and not (changed&bad_after_flip):
                            alt=gs[:j]+[(op,a,b)]+gs[j+1:]
                            assert passes(alt,oo,aa) and livecount(alt,oo,aa)<=45
                            return (alt,oo,aa,(i,replacement,j)),(redirects,eligible,considered)
    return None,(redirects,eligible,considered)

live_rows=(1<<len(cases))-1
def forced(gs, first, value, base):
    signals=base[:25+first]+[value]
    for op,a,b in gs[first+1:]:
        signals.append(signals[a]&signals[b] if op=='and' else signals[a]|signals[b])
    return signals
def repair_two(gs, main, mark, omitted, baseline):
    budget=[0,0,0]
    for j in range(len(gs)-1):
        if j==omitted:continue
        stop=25+j
        w00=forced(gs,j,0,baseline)
        w11=forced(gs,j,live_rows,baseline)
        # Group by the truth table of the new gate on the validation rows.
        distinct={}
        for a,b in combinations(range(stop),2):
            if omitted+25 in (a,b):continue
            for op,val in (('and',baseline[a]&baseline[b]),('or',baseline[a]|baseline[b])):
                if val!=baseline[stop]:
                    distinct.setdefault(val,(op,a,b))
        for k in range(j+1,len(gs)):
            if k==omitted:continue
            bad00=requirements(forced(gs,k,0,w00),main,mark)
            bad01=requirements(forced(gs,k,live_rows,w00),main,mark)
            bad10=requirements(forced(gs,k,0,w11),main,mark)
            bad11=requirements(forced(gs,k,live_rows,w11),main,mark)
            must_j1=bad00&bad01
            must_j0=bad10&bad11
            budget[0]+=1
            if must_j0&must_j1:continue
            for val,gate in distinct.items():
                if val&must_j0 or val&must_j1!=must_j1:continue
                must_k1=(val&bad10)|(~val&bad00)
                must_k0=(val&bad11)|(~val&bad01)
                budget[1]+=1
                mix=[(u&~val)|(v&val) for u,v in zip(w00[:25+k],w11[:25+k])]
                for a,b in combinations(range(25+k),2):
                    if 25+omitted in (a,b):continue
                    for op,test in (('and',mix[a]&mix[b]),('or',mix[a]|mix[b])):
                        budget[2]+=1
                        if test&must_k0 or test&must_k1!=must_k1:continue
                        cand=gs.copy();cand[j]=gate;cand[k]=(op,a,b)
                        assert passes(cand,main,mark) and livecount(cand,main,mark)<=45
                        return (cand,main,mark,j,k),budget
    return None,budget
total=[0,0,0]
for removed in (44,45):
    redirects=0
    for replacement in range(25+removed):
        wi=25+removed
        gs=[(op,replacement if a==wi else a,replacement if b==wi else b) for op,a,b in gates]
        main=replacement if out==wi else out
        mark=replacement if aux==wi else aux
        baseline=compute(gs)
        assert requirements(baseline,main,mark)
        candidate,counts=repair_two(gs,main,mark,removed,baseline)
        redirects+=1
        total=[a+b for a,b in zip(total,counts)]
        if candidate:
            print('Witness from redirect',removed,replacement,candidate,flush=True)
            exit()
    print('Searched',redirects,'redirections of gate',removed,'cumulative counts',total,flush=True)
print('No repaired circuit',flush=True)
```
