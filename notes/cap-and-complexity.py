"""AND-gate certificates for the capped order-three incidence problem."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import runpy
import subprocess

N = 13
DIFF = {0, 1, 3, 9}
EDGES = [(p, 13+l) for p in range(N) for l in range(N) if (p-l) % N in DIFF]


def mask(vertices):
    return sum(1 << v for v in vertices)


def pop(word):
    return bin(word).count('1')


def capped(vertices, shore):
    return all(sum(((v-i) if shore == 0 else (i-v)) % N in DIFF for v in vertices) <= 2
               for i in range(N))


def boundary():
    caps = []
    for shore in (0, 1):
        assert not any(capped(s, shore) for s in combinations(range(N), 5))
        caps.append([s for n in range(5) for s in combinations(range(N), n) if capped(s, shore)])
    pairs = set()
    for points in caps[0]:
        available = {l for l in range(N) if all((p-l) % N not in DIFF for p in points)}
        pairs.update(mask(points) | (mask(lines) << 13) for lines in caps[1] if set(lines) <= available)
    maximal = sorted(s for s in pairs if all(s | (1 << v) not in pairs
                     for v in range(26) if not s & (1 << v)))
    assert len(caps[0]) == len(caps[1]) == 560 and len(pairs) == 12234
    assert Counter((pop(s & 8191), pop(s >> 13)) for s in maximal) == {(4,3):234, (3,4):234}
    return maximal


MAXIMAL = boundary()


def restricted(pins):
    chosen = mask(pins)
    cols = [s for s in MAXIMAL if chosen & ~s == 0]
    vertices = [v for v in range(26) if v not in pins and any(s & (1 << v) for s in cols)]
    local = {v:i for i,v in enumerate(vertices)}
    positives = [mask((local[p],local[l])) for p,l in EDGES if p in local and l in local]
    negatives = [mask(i for i,v in enumerate(vertices) if s & (1 << v)) for s in cols]
    assert len(set(negatives)) == len(negatives)
    # Every residual negative is graph-maximal. Its complement is recoverable
    # from the raw OR ports, using a true flag at each missing vertex.
    for row in negatives:
        assert all(e & ~row for e in positives)
        for i in range(len(vertices)):
            if not row & (1 << i):
                assert any(e & ~row == (1 << i) for e in positives)
    assert all(any(e & ~(s | t) == 0 for e in positives) for s,t in combinations(negatives,2))
    return vertices, positives, negatives


def check_separations():
    for a,b in combinations(range(26),2):
        if (a,b) in EDGES:
            continue
        for x in range(26):
            if x != a and x != b:
                assert any(s & (1<<a) and s & (1<<b) and not s & (1<<x) for s in MAXIMAL)
    assert all(sum(v in e and w in e for e in EDGES) == 0 for v,w in [(0,14),(13,14)])
    for selected in ((), (0,), (0,14)):
        V, P, cols = restricted(selected)
        signatures = [mask(j for j,row in enumerate(cols) if row & (1 << i)) for i in range(len(V))]
        assert all(a & ~b for i,a in enumerate(signatures) for j,b in enumerate(signatures) if i != j)
        print('Pins', selected, ':', len(V), 'vertices,', len(P), 'flags,', len(cols), 'negative columns.')


def product_options(n, positives, negatives, budget):
    full = (1 << n)-1
    flags = [mask(i for i,e in enumerate(positives) if s & e) for s in range(full+1)]
    cols = [mask(i for i,t in enumerate(negatives) if s & t) for s in range(full+1)]
    choices = {}
    # The two input sets of a normalized AND are disjoint and interchangeable.
    for left in range(1, full):
        available = full ^ left
        right = available
        while right > left:
            covered = flags[left] & flags[right]
            cost = pop(cols[left] & cols[right])
            if covered and cost <= budget:
                choices[covered] = min(cost, choices.get(covered, budget+1))
            right = (right-1) & available
    return choices


def cover_cost(positives, options, gates):
    keep = []
    for flags,cost in sorted(options.items(), key=lambda pair:(pair[1], -pop(pair[0]))):
        if not any(flags & ~more == 0 and price <= cost for more,price in keep):
            keep.append((flags,cost))

    @lru_cache(None)
    def best(left, k):
        if not left:
            return 0
        if k == 0:
            return 1000
        candidates = min(([q for q in keep if q[0] & (1<<i)]
                          for i in range(len(positives)) if left & (1<<i)), key=len)
        return min((cost + best(left & ~flags, k-1) for flags,cost in candidates), default=1000)
    return best((1<<len(positives))-1, gates), len(keep)


def symmetry():
    source = Path(__file__).with_name('quadrangle-four-clauses.py')
    group = runpy.run_path(str(source))['group']()
    incident = [[i for i,e in enumerate(EDGES) if v in e] for v in range(26)]
    maps = [tuple(EDGES[g[es[0]]][int(v >= 13)] for v,es in enumerate(incident)) for g in group]
    dual = tuple(13 + (-v)%13 if v < 13 else (-v)%13 for v in range(26))
    images = maps + [tuple(dual[v] for v in m) for m in maps]
    assert {mask(dual[v] for v in range(26) if s & (1<<v)) for s in MAXIMAL} == set(MAXIMAL)
    for seed, size in [((0,),26), ((0,1),312), ((0,14),234),
                       ((0,14,5),1872), ((0,14,16),1872)]:
        assert len({tuple(m[v] for v in seed) for m in images}) == size


def checks():
    symmetry()
    check_separations()
    for pins, k, budget, expected in [((0,14,5),4,1,(68,29)), ((0,14,16),4,1,(68,29)),
                                      ((0,1),5,5,(87,51))]:
        V, P, Q = restricted(pins)
        options = product_options(len(V), P, Q, budget)
        cost, survivors = cover_cost(P, options, k)
        assert (len(options), survivors) == expected and cost > budget
        print('Pins', pins, ':', k, 'ANDs excluded by', survivors, 'undominated products.')


def seven_gate_exclusion():
    """Necessary raw-port conditions on the 16 surviving vertices."""
    vertices, positive, negative = restricted((0,14))
    k = 7
    source = Path(__file__).with_name('plane-three-line-cores.py')
    f = runpy.run_path(str(source))['Formula']()
    one = f.var()
    f.clauses.append([one])

    def conjunction(xs):
        y = f.var()
        f.clauses.extend([-y,x] for x in xs)
        f.clauses.append([y] + [-x for x in xs])
        return y

    def at_most(inputs, limit):
        if len(inputs) <= limit:
            return
        prev = []
        for x in inputs:
            row = [f.var() for _ in range(min(len(prev)+1, limit))]
            f.clauses.append([-x, row[0]] if row else [-x])
            for j,z in enumerate(prev):
                f.clauses.append([-z,row[j]])
                f.clauses.append([-z,-x] + ([row[j+1]] if j+1 < len(row) else []))
            prev = row

    def descending(a,b):
        # An equal prefix forces the next coordinate to be in descending order.
        eq = one
        for x,y in zip(a,b):
            f.clauses.append([-eq,x,-y])
            z = f.var()
            f.clauses.extend(([-eq,-x,-y,z], [-eq,x,y,z]))
            eq = z

    n = len(vertices)
    ports = [[f.var() for _ in vertices] for _ in range(2*k)]
    for g in range(k):
        descending(ports[2*g],ports[2*g+1])
        if g:
            descending(ports[2*g-2]+ports[2*g-1], ports[2*g]+ports[2*g+1])
        for x in range(n):
            f.clauses.append([-ports[2*g][x],-ports[2*g+1][x]])
    for x in range(n):
        at_most([p[x] for p in ports],2)
    for edge in positive:
        x,y = [i for i in range(n) if edge & (1<<i)]
        f.clauses.append([conjunction([ports[d][x],ports[d^1][y]]) for d in range(2*k)])
    bad = []
    for col in negative:
        absent = [conjunction([-p[i] for i in range(n) if col & (1<<i)]) for p in ports]
        for x in range(n):
            if not col & (1<<x):
                f.clauses.append([conjunction([a,p[x]]) for a,p in zip(absent,ports)])
        bad.extend(conjunction([-absent[2*g],-absent[2*g+1]]) for g in range(k))
    at_most(bad, 2**k-len(negative))
    assert (f.count,len(f.clauses)) == (33417,78441)
    root = Path(__file__).resolve().parent.parent / 'lean'
    exe = Path(subprocess.check_output(['lean','--print-prefix'],cwd=root,text=True).strip()) / 'bin/cadical'
    run = subprocess.run([exe,'-q','--check','--checkproof=2','-t','180'],input=f.text(),
                         capture_output=True,text=True,timeout=205)
    assert run.returncode == 20 and 's UNSATISFIABLE' in run.stdout, (run.returncode,run.stderr)
    print('Double-pin restriction: seven ANDs excluded, 33,417 variables and 78,441 clauses.')


if __name__ == '__main__':
    checks()
    seven_gate_exclusion()
