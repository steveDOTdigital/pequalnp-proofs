# Nineteen gates for formulas on the four deletions in L-meta-8994

Each of the four graphs in [L-meta-8994](https://pequalnp.com/lemma#L-meta-8994) has 14 edges and minimum vertex-cover size six. A 19-gate formula exists for each. The lower bound of 19 holds for all monotone formulas, with arbitrary reuse of raw variables. It also holds for a circuit with a single shared internal output in any of the following cases.

* Its input cone uses at most two gates.
* Its input cone computes a disjunction of any subset of raw inputs.
* It turns on at two distinct singleton assignments.

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
