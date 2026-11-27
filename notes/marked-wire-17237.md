# A 46-gate control for L-meta-17237

[L-meta-17237](https://data.pequalnp.com/data/lemma/L-meta-17237.0c0a82c55dd1.json) asks for a circuit of at most 45 gates for a 25-input incidence function and a marked output. There are nine nonisolated points, thirteen lines and 36 flags. The three marked lines are 13, 15 and 21. The control below uses 44 gates for incidence and two for the marked-line OR. It checks every required positive and a superset of every maximal required negative independently for each output.

## A matching lower bound for circuits built from rectangles

In the rectangle class, products are ANDs of raw point and line disjunctions, and the main output is the OR of those products. Disjunctions may share gates. Because the graph has no four-cycle, each product is a star. If a product has a single edge, choose either endpoint as its centre.

Each point has degree four, and exactly one of its neighbours is a marked line of degree three. For every nonempty set of points S, the 4|S| incidences from S use lines of degree at most four, with at least one line of degree three. Consequently |N(S)|>|S|. A vertex cover omitting S would need all of N(S), so the unique minimum cover is the nine nonisolated points. Any rectangle representation uses at least nine products.

If there are r products, assigning flags to covering products requires at least 36−r gates for their disjunction preprocessing. For each centre, the network feeding its products must connect its assigned distinct leaves to the product operands. A binary network on d leaves with t outputs costs at least d−t gates. No disjunction of two or more neighbours is shared between different centres, by the no-four-cycle property. Add r products and at least r−1 OR gates above them, giving at least 36+r−1≥44 gates for incidence. Each wire in this main cone is true on at most one marked-line singleton. This is because every point has only one marked neighbour and a line-centred product uses its line alone on the line side. Each product and every gate above the products is false on those tests. A marked output accepting all three tests therefore needs at least two gates outside the main cone, by counting distinct input signals feeding its outside cone. Constants and copies can be simplified before that count.

This proves an exact minimum of 46 for the rectangle class. An arbitrary 45-gate circuit remains open. One implication of the [marked-wire clamping argument](https://github.com/steveDOTdigital/pequalnp-proofs/blob/research/independent-results/notes/punctured-plane-marked-wire.md) applies directly here. At least two gates merge the three singleton components. Fix every gate true that is positive on at least two marked singletons. It is already true on the maximal negative row for any point set occupying at most one of the three marked groups. Thus a 45-gate witness would give a circuit of at most 43 gates correct on those point sets with arbitrary line inputs.

## Replay

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
```
