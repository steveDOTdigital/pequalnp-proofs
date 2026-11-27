# Circuit search and a 31-gate lower bound for L-meta-17237

The [46-gate construction and rectangle bound](https://github.com/steveDOTdigital/pequalnp-proofs/blob/81a9685ed8efab81373d67ab222ff9d39e462d87/notes/marked-wire-17237.md) leave open whether 45 gates suffice in the [assigned statement](https://data.pequalnp.com/data/lemma/L-meta-17237.0c0a82c55dd1.json). The unrestricted interval is now 31–46. These are written and computational checks.

## Gate elimination after clamping

Clamp the signals that accept at least two of the three marker singletons, as in the construction note. At least two gates disappear. The remaining single-output circuit is correct whenever the selected points are confined to one of the three marked groups. The first-gate elimination below proves that such a circuit needs at least 29 gates.

For an induced subgraph, each vertex still incident with an edge is essential on the promise, by the test selecting one incident pair. Pinning an essential input to zero saves at least one gate. A minimum circuit may be assumed live, with constants and duplicate operands removed. Its first gate therefore has two distinct raw inputs. If it is AND, pinning either endpoint to zero removes the AND and simplifies a later consumer. If it is OR and an endpoint is used only there, replacing that endpoint by the other in a positive pair cannot decrease the output. When a replacement is a promised negative, this forces a second reader and pinning the endpoint saves two gates. At a possible first pair, take the better certified bound over the two pins, then take the worst over pairs. At each recursion depth, also allow the best plain one-gate pin. Every remaining induced subgraph uses only a downward-closed promise.

The leaf bound uses the number of essential inputs minus one. It also uses any retained quadrangle with each pair on a distinct joining line. This ten-input subgraph requires 15 gates even on the weaker one-point promise. The previous `pencil-one-point-search.mjs quadrangle 14` calculation was replayed here and exhausted 395,679 states. In its connected component, vertices outside the quadrangle can be pinned from leaves of a tree contracted to the quadrangle. Every removed vertex then still has a neighbour. In a component disjoint from it, the last vertex may already be isolated and is charged no gate. This is the base bound used in the code.

The directed pin calculation with six levels checks 82,160 induced subgraphs, finds 54 quadrangles and gives 29 gates. Ten levels check 1,048,563 induced subgraphs and give the same bound. Restoring the two clamped gates yields 31 for the original two-output problem.

## Exact search around six different 46-gate controls

For the original construction and five reorderings, redirect all uses of a chosen gate to one earlier wire. Include output addresses so this also considers deleting an output gate. Check whether an arbitrary redefinition of a single remaining gate can repair both outputs. For each such position, evaluate the circuit once with the current gate's value and once with the value flipped on each test row. If a row fails both evaluations, that position cannot repair the circuit. Otherwise this gives exact bit conditions on the replacement gate, because the only changed signal entering the downstream circuit is the chosen gate's output.

Across the six controls there are 13,110 redirections and 303,253,348 replacement definitions at positions surviving that test. None works. The test pool has 720 distinct rows. It covers every incident pair, the three marked singletons and both families of maximal negative rows, using a containing independent set where sufficient. The two outputs are validated against their separate required values.

The unrestricted SAT encoding was tested against the known 46-gate control and the decoded circuit passed the same 720 rows. A 45-gate run on an 84-row subset reached its 90-second limit without a verdict. This timing places no restriction on the minimum.

## Gate-elimination replay

```javascript
// L-meta-17237: lower bound after clamping the marked-line ORs.
const depth = 6;
const all = ((1 << 25) - 1) ^ 261;
const groups = [[1,7,11],[5,9,10],[3,4,6]].map(g => g.reduce((a,b) => a | (1<<b),0));
const points = (1 << 12) - 1;
const adjacent = Array(25).fill(0);
for (let p = 0; p < 12; p++) {
  for (let l = 12; l < 25; l++) {
    if ((all & (1<<p)) && [0, 1, 3, 9].includes((p + l + 2) % 13)) {
      adjacent[p] |= 1 << l;
      adjacent[l] |= 1 << p;
    }
  }
}

function vertices(mask) {
  const ids = [];
  for (; mask; mask &= mask - 1) ids.push(31 - Math.clz32(mask & -mask));
  return ids;
}

// Four points with six different joining lines give the 10-input,
// 15-gate quadrangle already certified by pencil-one-point-search.mjs.
const quadrangles = [];
for (let group = 1; group <= points; group++) {
  if ((group & all) !== group || vertices(group).length !== 4) continue;
  let core = group;
  for (let l = 12; l < 25; l++) {
    if (vertices(adjacent[l] & group).length === 2) core |= 1 << l;
  }
  if (vertices(core).length === 10) quadrangles.push(core);
}

function components(mask) {
  let count = 0;
  while (mask) {
    count++;
    let wave = mask & -mask;
    while (wave) {
      mask &= ~wave;
      let next = 0;
      for (const v of vertices(wave)) next |= adjacent[v];
      wave = next & mask;
    }
  }
  return count;
}

// If x is read only by OR(x,y), replacing x in a positive flag by y
// cannot decrease the output. A negative promised replacement rules that
// out. For AND(x,y) pinning x false also removes a consumer of the zero.
function doubleSaving(x, y, active) {
  for (const q of vertices(adjacent[x] & active)) {
    const replacement = (1 << q) | (1 << y);
    const selected = replacement & points;
    if (!groups.some(g => (selected & g) === selected)) continue;
    if (!(adjacent[q] & (1 << y))) return true;
  }
  return false;
}

const cache = new Map();
function lower(mask, remaining) {
  if (cache.has(mask)) return cache.get(mask);
  // Keep isolated vertices in the cache key to count the actual pins.
  // Only vertices still incident to an edge are essential to the output.
  const live = vertices(mask).filter(v => adjacent[v] & mask);
  const active = live.reduce((bits, v) => bits | (1 << v), 0);
  if (live.length <= 2) return Math.max(0,live.length - 1);
  let bound = live.length - 1;
  if (quadrangles.some(core => (core & active) === core)) {
    // Pin toward the core in a spanning tree. In each other connected
    // component the final isolated vertex need not save a gate.
    bound = Math.max(bound, live.length - 10 + 15 - (components(active) - 1));
  }
  if (remaining) {
    const pinned = live.map(v => lower(mask ^ (1 << v), remaining - 1));
    bound = Math.max(bound, 1 + Math.max(...pinned));
    let worst = Infinity;
    for (let i = 0; i < live.length; i++) {
      for (let j = i + 1; j < live.length; j++) {
        const a = pinned[i] + 1 + Number(doubleSaving(live[i], live[j], active));
        const b = pinned[j] + 1 + Number(doubleSaving(live[j], live[i], active));
        worst = Math.min(worst, Math.max(a, b));
      }
    }
    bound = Math.max(bound, worst);
  }
  cache.set(mask, bound);
  return bound;
}

const unmarked = lower(all, depth);
console.log(JSON.stringify({ depth, quadrangles: quadrangles.length, states: cache.size,
  oneGroupLowerBound: unmarked, markedLowerBound: unmarked + 2 }));
```

## Redirection and replacement replay

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

from random import Random
rng=Random(17237)
for case in range(6):
    gates=[]
    point_order=list(points)
    if case: rng.shuffle(point_order)
    terms=[]
    for p in point_order:
        inputs=list(sorted(neighbors[p]))
        if case: rng.shuffle(inputs)
        terms.append(gate('and',p,join(inputs)))
    out=join(terms)
    pencil=list(marked)
    if case: rng.shuffle(pencil)
    aux=join(pencil)
    assert passes(gates,out,aux) and livecount(gates,out,aux)==46
    now=perf_counter()
    witness, counts=search_redirects(gates,out,aux)
    print('Equivalent control',case,'counts',counts,'seconds',round(perf_counter()-now,2),'witness',witness,flush=True)
    if witness:break
```
