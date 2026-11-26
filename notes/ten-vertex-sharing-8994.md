# Nineteen gates for formulas on the four deletions in L-meta-8994

Each of the four graphs in [L-meta-8994](https://pequalnp.com/lemma#L-meta-8994) has 14 edges and minimum vertex-cover size six. A 19-gate formula exists for each. The lower bound of 19 holds for all monotone formulas, with arbitrary reuse of raw variables. It also holds for a circuit with a single shared internal output in any of the following cases.

* Its input cone uses at most two gates.
* Its input cone computes a disjunction of any subset of raw inputs.
* It turns on at two distinct singleton assignments.

The extensions below rule out **every** single shared result that turns on at a singleton, every read-once input cone, and every single helper with at most five contributing inputs. A smaller circuit with only one shared internal wire would have to repeat an input inside that cone, reject every singleton, and have at least six endpoints among its positive edge rows.

These claims concern all four deletions separately. A shared output means that at least two operand occurrences read it in the live circuit. The exact desk statement permits arbitrarily many shared outputs, and remains unresolved here.

## What a suffix formula must report

Delete the selected vertex, keeping the original labels on the other ten vertices. Take one row per edge, representing the assignment supported on its endpoints. Take one column per maximal independent set. For a true edge row and a false column, descend a binary formula from its output. At an OR choose a child true on the row, breaking ties consistently using the row alone. At an AND choose a child false on the column, breaking ties using the column alone. Every cell reaches a leaf that is true on the row and false on the column. Each leaf receives a rectangle, since every choice restricts either the rows or the columns.

For a raw leaf labelled by vertex v, its nonempty rectangle can use only edges incident to v. Write its row set as a bit mask on those edges. In every column the edges reporting v are a disjoint union of masks of leaves active in that column. Equal nonempty masks can be merged for this counting test. Using one singleton mask per incident edge allows all patterns and suffices as the maximal-cost option.

Cut a single shared wire H out of the circuit. Its input cone is a formula. Its remaining uses are leaves of another formula whose other leaves are raw. In a column C the suffix can use an H leaf only on an edge e with H(e)=1 and H(C)=0. Declare all such cells optional. For a lower bound one can also declare a superset optional. Each other cell must report one of the endpoints of its row edge that is absent from C.

The calculation below enumerates all endpoint choices independently in each column. For each vertex and each proposed family of row masks, it keeps the choices realizable by disjoint unions, projected to the mandatory cells. It intersects these choice sets over the ten vertices. A column becoming empty excludes that family. Removing an option dominated in every column by one costing no more is exact for this relaxation. Thus infeasibility rules out a suffix with that many raw leaves. A feasible relaxed orientation alone does not establish that a formula exists.

## Counting the gates

With no shared wire, 18 gates would give at most 19 leaves. The search excludes 19 raw leaves for each graph and allows 20. Independently the replay constructs the six stars of a minimum vertex cover and checks their outputs on all 1,024 inputs per deletion. The six star ANDs, eight ORs within stars and five ORs joining them use 19 gates.

If the input cone of H costs t gates and H has at least two uses, an 18-gate circuit leaves at most 17−t raw leaves in the suffix. For a two- or three-variable disjunction the optional cells have an edge touching the support and a column disjoint from it. The raw budgets of 16 and 15 fail for each of the 45 pairs and 120 triples per graph. More generally, if H is true on two singletons a and b, it is true on every column containing a or b. Even declaring **every** cell in every other column optional, the raw budget of 14 fails for all 45 pairs. This rules out every such H with a cone of at least three gates. Disjunctions of four or more distinct variables need at least three gates, since a binary cone depending on k variables contains at least k−1 gates.

For cones of at most two gates, fold constants, copies, repeated variables and absorption first. Pure ANDs of two or three variables either fire only on assignments containing a graph edge, or fire on no edge row. In the latter case substitute false. In the former case replace all suffix uses with false and OR the safe helper into the final output once. Substituting false simplifies at least one suffix gate and pays for this final OR. The result is a formula. These transformations preserve the boundary by monotonicity, which establishes all input rows.

For H = x AND (y OR z), keep only the neighboring variables among y,z. The replacement agrees on edge rows and can only decrease on negative rows. It is now safe, so the same argument applies, including when the replacement is constant. For H = x OR (y AND z), substitute x for H throughout the suffix. If yz is a nonedge this agrees on every positive edge row and can only decrease on negatives. If yz is an edge, append its two-input AND and one final OR to the suffix. This costs the two gates released by removing the input cone. Every input containing yz is positive, and on all other inputs H equals x. What remains is again a formula. This exhausts the two-gate shapes, up to commutativity and associativity.

## Independent replay

Run the following with Python 3.10 or later. The graph test uses the desk’s literal edge list and checks each minimum cover by enumeration. All proof exclusions are finite calculations outside Lean.

```python
from functools import reduce
from itertools import combinations, product
from operator import or_

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
BITS = [1 << i for i in range(11)]


def graph(deleted):
    vertices = sorted(set(range(11)) - {deleted})
    edges = [e for e in EDGES if deleted not in e]
    masks = [BITS[a] | BITS[b] for a, b in edges]
    def positive(row):
        return any(row & mask == mask for mask in masks)
    rows = [r for r in range(2048) if not r & BITS[deleted]]
    columns = [r for r in rows if not positive(r) and
               all(r & BITS[v] or positive(r | BITS[v]) for v in vertices)]
    cover = min((r for r in rows if all(r & mask for mask in masks)),
                key=int.bit_count)
    stars = {v: [] for v in vertices if cover & BITS[v]}
    for a,b in edges:
        owner = a if a in stars else b
        stars[owner].append(b if owner == a else a)
    assert all(stars.values()) and len(stars) == 6 and len(edges) == 14
    assert sum(map(len, stars.values())) + len(stars) - 1 == 19
    assert all(positive(r) == any(r & BITS[v] and any(r & BITS[w] for w in ws)
                                 for v,ws in stars.items()) for r in rows)
    return vertices, edges, columns


def options(vertices, edges, columns, optional):
    # Each column gets its own list of orientations of its mandatory edge rows.
    orientations = []
    for c in columns:
        choices = [[-1] if optional(e,c) else [v for v in e if not c & BITS[v]]
                   for e in edges]
        orientations.append(list(product(*choices)))
    domains = {}
    for v in vertices:
        incident = [i for i,e in enumerate(edges) if v in e]
        degree = len(incident)
        tables = []
        for choices in orientations:
            table = [0] * (1 << degree)
            for index, choice in enumerate(choices):
                pattern = sum(1 << j for j,i in enumerate(incident) if choice[i] == v)
                table[pattern] |= 1 << index
            required = sum(1 << j for j,i in enumerate(incident) if choices[0][i] != -1)
            tables.append((table, required))
        domain = []
        for cost in range(degree + 1):
            bases = combinations(range(1, 1 << degree), cost)
            if cost == degree:
                bases = [tuple(1 << j for j in range(degree))]
            for basis in bases:
                unions = {0}
                for block in basis:
                    unions |= {old | block for old in unions if not old & block}
                allowed = tuple(reduce(or_, (table[p] for p in {u & req for u in unions}), 0)
                                for table,req in tables)
                if not all(allowed):
                    continue
                if any(old_cost <= cost and all(a & ~b == 0 for a,b in zip(allowed,old))
                       for old_cost,old in domain):
                    continue
                domain.append((cost,allowed))
        domains[v] = domain
    return domains, tuple((1 << len(c)) - 1 for c in orientations)


def feasible(domains, rows, remaining):
    if not domains:
        return True
    choices = {}
    for v,domain in domains.items():
        choices[v] = [(cost,tuple(a & b for a,b in zip(rows,allowed)))
                      for cost,allowed in domain if all(a & b for a,b in zip(rows,allowed))]
        if not choices[v]:
            return False
    floors = {v:min(cost for cost,_ in opts) for v,opts in choices.items()}
    spare = remaining - sum(floors.values())
    if spare < 0:
        return False
    v = min(choices, key=lambda x: (sum(c <= floors[x]+spare for c,_ in choices[x]),
                                    -len(domains[x])))
    rest = {x:domain for x,domain in domains.items() if x != v}
    return any(feasible(rest, filtered, remaining - cost) for cost,filtered in choices[v]
               if cost <= floors[v] + spare)


for deletion in range(4):
    vertices, edges, columns = graph(deletion)
    def test(optional, budget):
        domains, rows = options(vertices, edges, columns, optional)
        return feasible(domains, rows, budget)
    domains, rows = options(vertices, edges, columns, lambda edge,column: False)
    assert not feasible(domains, rows, 19) and feasible(domains, rows, 20)
    for size,budget in [(2,16),(3,15)]:
        for support in combinations(vertices,size):
            mask = sum(BITS[x] for x in support)
            assert not test(lambda edge,c: not (c & mask) and any(v in support for v in edge), budget)
    for a,b in combinations(vertices,2):
        mask = BITS[a] | BITS[b]
        assert not test(lambda edge,c: not (c & mask),14)
    print(deletion, len(columns), "passed", flush=True)
```

## A single shared result cannot turn on at even one singleton

Suppose an 18-gate counterexample has a unique shared internal result H. The earlier argument rules out two singleton hits. Let x be its unique singleton hit. Write B for the set of edges avoiding x on which H is true, and T for their endpoints. In the input cone of H alone, set every variable outside {x} ∪ T to zero. This preserves the value on every edge row: the incident edges still contain x, and every edge in B retains both endpoints. Monotonicity can only decrease the result on negative columns. The modified circuit therefore still computes the target. Simplify constants and trim the cone. If H becomes a raw input, or has fewer than two uses after trimming, the formula bound applies.

The modified H depends essentially on x and each vertex of T. On the row of an edge in B, deleting either endpoint leaves a singleton distinct from x and makes H false. Consequently the cone costs at least |T| gates. It also costs at least three by the two-gate result above. Call its cost t. In a column containing x no H leaf can report. The orientation search on just those columns gives a lower bound r on raw suffix leaves, so t ≤ 17−r.

There is a second way to rule out a candidate. Substitute x for H everywhere in the suffix, then OR into the output a star formula computing the edge function of B. On edge rows outside B the substitution preserves H. The new disjunct restores the rows in B. On negative rows the substitution can only decrease the output and the new disjunct is false. This produces a formula, and the added gates total |B| + τ(B) for nonempty B. Thus we can discard T when even the graph induced by T satisfies |E(T)| + τ(G[T]) ≤ t. With B empty, substituting x already suffices.

For each remaining T, first optimistically allow the helper on all edges inside T and all edges incident to x, for every column omitting x. The numbers of candidates before this test were 329, 534, 363 and 604. Only 0, 2, 3 and 9 candidates survived. For each survivor compute the least relaxed raw budget and infer an upper bound on t. In all fourteen cases this upper bound equals |T|. Enumerate every prefix formula up to the resulting cost on {x} ∪ T. A signature stores the values on singletons, edge rows and maximal negative columns. AND and OR act bitwise, and retaining only the cheapest occurrence of a signature preserves all possible minimum-cost signatures. For each surviving signature, test the actual optional cells with the remaining raw budget. None survives.

Thus a circuit smaller than 19 with exactly one shared internal wire must use a helper false on **all ten singletons**. This result permits arbitrarily many readers of that helper. Circuits with multiple shared wires, and some circuits whose sole shared wire is false on every singleton, remain open.

```python
# Extension to the preceding Python replay.
from functools import lru_cache


@lru_cache(None)
def cover_size(edges):
    return min(m.bit_count() for m in range(2048)
               if all(m & (BITS[a] | BITS[b]) for a,b in edges))


def signature_layers(raw, cap):
    layers = [set(raw)]
    seen = set(raw)
    for cost in range(1, cap+1):
        fresh = set()
        for i in range((cost-1)//2+1):
            for left in layers[i]:
                for right in layers[cost-1-i]:
                    fresh.add(left | right)
                    fresh.add(left & right)
        fresh -= seen
        seen.update(fresh)
        layers.append(fresh)
    return layers


for deletion in range(4):
    vertices, edges, columns = graph(deletion)
    jobs = survivors = 0
    for x in vertices:
        def optional_for(support_edges):
            return lambda e,c: not c & BITS[x] and (x in e or e in support_edges)
        fixed = [c for c in columns if c & BITS[x]]
        domains, rows = options(vertices, edges, fixed, lambda e,c: False)
        floor = next(i for i in range(21) if feasible(domains, rows, i))
        for k in range(2, 18-floor):
            for support in combinations([v for v in vertices if v != x], k):
                induced = tuple(e for e in edges if all(v in support for v in e))
                if len({v for e in induced for v in e}) != k:
                    continue
                cost = max(3, k)
                if len(induced) + cover_size(induced) <= cost:
                    continue
                jobs += 1
                domains, rows = options(vertices, edges, columns, optional_for(induced))
                if not feasible(domains, rows, 17-cost):
                    continue
                survivors += 1
                raw_floor = next(i for i in range(18-cost) if feasible(domains, rows, i))
                cap = 17 - raw_floor
                assert cap == k
                tests = [BITS[v] for v in vertices] + [BITS[a] | BITS[b] for a,b in edges] + columns
                signatures = [sum(1 << j for j,m in enumerate(tests) if m & BITS[v])
                              for v in (x,*support)]
                edge_bit = {e:1 << (len(vertices)+j) for j,e in enumerate(edges)}
                col_bit = {c:1 << (len(vertices)+len(edges)+j) for j,c in enumerate(columns)}
                for t,layer in enumerate(signature_layers(signatures, cap)):
                    if t < cost:
                        continue
                    for h in layer:
                        if h & ((1 << len(vertices))-1) != 1 << vertices.index(x):
                            continue
                        hit = tuple(e for e in induced if h & edge_bit[e])
                        if {v for e in hit for v in e} != set(support):
                            continue
                        if len(hit) + cover_size(hit) <= t:
                            continue
                        domains, rows = options(vertices, edges, columns,
                            lambda e,c: bool(h & edge_bit[e]) and not h & col_bit[c])
                        assert not feasible(domains, rows, 17-t)
    assert (jobs,survivors) == [(329,0),(534,2),(363,3),(604,9)][deletion]
    print(deletion, jobs, survivors, "singleton-helper exclusion passed", flush=True)
```

## A helper false on every singleton needs at least six contributing inputs

Let B be the family of edge rows accepted by H, and let T consist of their endpoints. Set other inputs to false **inside H only**. The resulting helper preserves every edge hit and can only improve the circuit on negative inputs. It still depends on both endpoints of every edge in B, as it rejects all singletons. If it becomes safe, the formula argument applies. Otherwise take an independent witness contained in T on which it turns on. Extend that witness to a maximal independent set U of G[T]. Every maximal independent set of the full graph containing U is a column on which H must be true. Each maximal independent set of G[T] is the intersection of T with some maximal independent set of G.

With k = |T|, the input cone costs at least t = max(3,k−1). If k ≤ 5, some edge lies outside B. Substituting false for all h ≥ 2 helper leaves therefore leaves a nonconstant formula, which uses at least h fewer gates because it retains at most the old number of raw leaves. ORing the star formula for B back into the result costs at most |B| + τ(B) gates. This rules out the support whenever |E(T)| + τ(G[T]) ≤ t+2. The cases k ≤ 2 have at most one contributing edge and are already covered by this argument, or by the inactive-helper case.

For 3 ≤ k ≤ 5, the remaining supports and independent witnesses can be checked with the preceding orientation test. Allow the helper on every edge inside T and every column omitting at least one vertex of U. All other edges, and every column containing U, must be handled by raw suffix leaves. Every vertex outside a mandatory column must occur in the suffix: its edge to some vertex in that maximal independent set forces its label. The endpoints of each edge outside T are likewise required, by extending either singleton endpoint to a maximal independent set. Applying these tests leaves 171, 137, 174 and 134 candidate pairs. The orientation test excludes them all at the raw budget 17−t.

```python
for deletion in range(4):
    vertices, edges, columns = graph(deletion)
    candidates = 0
    for k in range(3,6):
        for support in combinations(vertices,k):
            mask = sum(BITS[v] for v in support)
            inside = tuple(e for e in edges if all(v in support for v in e))
            if {v for e in inside for v in e} != set(support):
                continue
            t = max(3,k-1)
            if len(inside) + cover_size(inside) <= t+2:
                continue
            projections = {c & mask for c in columns}
            for witness in projections:
                if witness.bit_count() < 2 or any(witness != w and witness & w == witness
                                                  for w in projections):
                    continue
                forced = {v for e in edges if e not in inside for v in e}
                forced.update(v for v in vertices if any(c & witness == witness and not c & BITS[v]
                                                         for c in columns))
                if len(forced) > 17-t:
                    continue
                candidates += 1
                domains, rows = options(vertices,edges,columns,
                    lambda e,c: e in inside and c & witness != witness)
                assert not feasible(domains,rows,17-t)
    assert candidates == (171,137,174,134)[deletion]
    print(deletion,candidates,"small cold helpers excluded",flush=True)
```

## Read-once input cones

In the remaining single-helper case the cone must also repeat at least one raw variable. To see this, trim the helper to the endpoints of its positive edge rows as above, and suppose each input occurs once in its formula. At an OR root the two subformulas have disjoint variables, and neither turns on at a singleton. Every input contributes to a hit edge within its own child. At an AND root each hit edge has one endpoint in each child, because the two children use disjoint variables and both vanish on the empty input. Each variable in either child is therefore a singleton hit of that child. By monotonicity each child is the disjunction of its variables. Induction expresses H as an OR of complete bipartite graphs on disjoint sets of raw vertices.

Intersect one such bipartite block with the desk graph. Its crossing edges span its support by the trimming above. Split it into the connected components of those crossing edges, replacing it by the OR of their separate bipartite blocks. This preserves all positive edge hits and can only decrease on negatives. A formula that reads k inputs once uses k−1 gates before and after the split. If a block is safe, move it from the helper to a final OR at the output. When another block remains, this releases one OR in the input cone and costs one at the output. A surviving dirty block needs at least two inputs on each shore: a one-vertex shore together with spanning crossing edges gives a safe star. Consequently at most two dirty blocks fit on ten inputs. Their crossing edges are connected, and two blocks have disjoint supports.

The code enumerates these blocks directly, storing their positive rows and the negative columns they accept. If all edge rows are accepted by the helper, replace the suffix uses by true and AND the helper back at the output. This preserves the function: any true target input has H true, while H true together with suffix[true] agrees with the original circuit. Simplifying the constant leaves pays for the final AND (if the suffix becomes constant, the helper itself suffices). For other cases, required raw labels and the orientation test above exclude the resulting one- and two-block signatures. The connected one-block counts before combining blocks were 1,358, 1,587, 1,552 and 1,671. The required-label filter left 1,098, 1,317, 1,253 and 1,431 signatures to test, respectively. This only uses the read-once hypothesis **inside the shared helper**; raw inputs can be reused without restriction elsewhere.

```python
from itertools import chain

def read_once(vs,es,cs):
    graphmask=sum(BITS[v] for v in vs)
    blocks=[]
    for L in range(1,2048):
        if L & ~graphmask or L.bit_count()<2:continue
        rem=graphmask^L
        R=rem
        while R>L:
            if R.bit_count()>=2:
                cross=[e for e in es if ((BITS[e[0]]&L and BITS[e[1]]&R) or
                                         (BITS[e[1]]&L and BITS[e[0]]&R))]
                support=L|R
                active=sum(BITS[v] for v in {w for e in cross for w in e})
                if active==support:
                    seen=L&-L
                    for _ in range(support.bit_count()):
                        for a,b in cross:
                            pair=BITS[a]|BITS[b]
                            if pair&seen:seen|=pair
                    if seen==support:
                        P=sum(1<<j for j,e in enumerate(es) if e in cross)
                        Q=sum(1<<j for j,c in enumerate(cs) if c&L and c&R)
                        if Q:blocks.append((support,P,Q))
            R=(R-1)&rem
    def pairs():
        for i,(s,p,q) in enumerate(blocks):
            for t,b,c in blocks[i+1:]:
                if not s&t:yield s|t,p|b,q|c
    viable=set()
    ebit={e:1<<i for i,e in enumerate(es)}
    cbit={c:1<<i for i,c in enumerate(cs)}
    for s,p,q in chain(blocks,pairs()):
        k=s.bit_count()
        if p==(1<<len(es))-1:continue
        need=0
        for e in es:
            if not p&ebit[e]:need|=BITS[e[0]]|BITS[e[1]]
        for c in cs:
            if q&cbit[c]:need|=graphmask^c
        if need.bit_count()>18-k:continue
        viable.add((k,p,q))
    print('blocks',len(blocks),'cases',len(viable),flush=True)
    for k,p,q in sorted(viable):
        D,R=options(vs,es,cs,lambda e,c:bool(p&ebit[e]) and not(q&cbit[c]))
        assert not feasible(D,R,18-k)
    print('read-once prefix exclusion passed',flush=True)
for d in range(4):
    print('deletion',d,flush=True)
    read_once(*graph(d))

```
