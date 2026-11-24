"""Rebuild a shared-guard plane circuit after stabilizing its selected signals."""
from itertools import combinations, product


def plane(offsets, n):
    lines = tuple(tuple(sorted((l+d) % n for d in offsets)) for l in range(n))
    assert all(len(set(a)&set(b))==1 for a,b in combinations(lines,2))
    return lines


def controlled_stars(lines):
    n=len(lines)
    gates=[]
    def put(op,a,b):
        assert a!=b and max(a,b)<2*n+len(gates)
        gates.append((op,a,b))
        return 2*n+len(gates)-1
    def join(items):
        a,*rest=items
        for b in rest:a=put('or',a,b)
        return a
    arms=[join(s) for s in lines]
    guard=arms[0]
    stars=[put('and',n,guard)]
    marked={}
    for l in range(1,n):
        joint=put('and',guard,arms[l])
        marked[joint]=guard
        outside=[p for p in lines[l] if p not in lines[0]]
        stars.append(put('and',n+l,put('or',joint,join(outside))))
    out=join(stars)
    return gates,marked,out


def tape(n,gates,row):
    vals=[bool(row&(1<<v)) for v in range(2*n)]
    for op,a,b in gates:
        vals.append((vals[a] or vals[b]) if op=='or' else (vals[a] and vals[b]))
    return vals


def valid(lines,row):
    n=len(lines)
    return not any(row&(1<<(n+j)) and any(row&(1<<p) for p in line)
                   for j,line in enumerate(lines))


def stabilize(signals,eval_signal,valid_row,vertices):
    base=0
    words=[0]+[1<<i for i in range(vertices)]+[(1<<i)|(1<<j) for i,j in combinations(range(vertices),2)]
    while True:
        vals=eval_signal(base)
        hit=None
        for ext in words:
            if ext&base or not valid_row(base|ext):continue
            trial=eval_signal(base|ext)
            if any(not vals[g] and trial[g] for g in signals):
                hit=ext
                break
        if hit is None:return base
        base|=hit


def transformed(n,gates,marked,base,extra):
    """Full, point-only and line-only rows use the same fixed one inputs."""
    pts=(1<<n)-1
    row=base|extra
    at=tape(n,gates,base)
    vals=[tuple(bool(r&(1<<i)) for r in (row,base|(extra&pts),base|(extra&~pts)))
          for i in range(2*n)]
    for j,(op,a,b) in enumerate(gates,2*n):
        u,v=vals[a],vals[b]
        if op=='or':
            vals.append(tuple(x or y for x,y in zip(u,v)))
        elif j in marked:
            guard=marked[j]
            other=b if a==guard else a
            vals.append(vals[other if at[guard] else guard])
        else:
            # In this family, every ordinary AND has its line-only operand first.
            vals.append((v[1] and u[2],v[1] and at[a],at[b] and u[2]))
    return vals


def check(lines,all_sparse=False):
    n=len(lines);q=len(lines[0])-1;gates,marked,out=controlled_stars(lines)
    ev=lambda row:tape(n,gates,row)
    ok=lambda row:valid(lines,row)
    base=stabilize(set(marked.values()),ev,ok,2*n)
    assert base and base&(base-1)==0 and base<(1<<n)
    assert len(set(marked.values()))==1 and len(marked)==n-1
    kept=[i for i in range(2*n) if not base&(1<<i) and ok(base|(1<<i))]
    flags={(p,n+l) for l,s in enumerate(lines) for p in s}
    count=0
    for k in range(3):
        for chosen in combinations(kept,k):
            extra=sum(1<<i for i in chosen)
            truth=chosen in flags
            assert ev(base|extra)[out]==truth
            assert transformed(n,gates,marked,base,extra)[out][0]==truth
            count+=truth
    assert count==n*(q+1)-(q+1)**2
    if all_sparse:
        for k in range(q+1):
            for ls in combinations(range(n),k):
                selected=sum(1<<(n+l) for l in ls)
                for points in range(1<<n):
                    row=points|selected
                    assert ev(row)[out] != ok(row)
    print(f'order {q}: {len(gates)} gates, {len(marked)} marked, one guard, {count} surviving flags')



def line_program(n, gates, out, cuts, permit_collisions=False):
    """Build a shared circuit on n point inputs. Its n outputs select a line.

    With cuts=None it computes one-line proof witnesses. Otherwise every AND
    with two line-dependent children must be listed as an exact cut.
    """
    zero, one = -1, -2
    program = []

    def build(op, a, b):
        if a == b: return a
        unit, absorb = (zero, one) if op == 'or' else (one, zero)
        if absorb in (a, b): return absorb
        if a == unit: return b
        if b == unit: return a
        program.append((op, a, b))
        return n + len(program) - 1

    nodes = 2*n + len(gates)
    baseline = list(range(n)) + [zero]*n
    depends = [False]*n + [True]*n
    edges = [[] for _ in range(nodes)]
    selected = [] if cuts is None else sorted(cuts)
    for w, (op, a, b) in enumerate(gates, 2*n):
        baseline.append(build(op, baseline[a], baseline[b]))
        depends.append(depends[a] or depends[b])
        if w in selected:
            continue
        elif op == 'or':
            edges[w] = [(a, one), (b, one)]
        elif cuts is None or permit_collisions:
            edges[w] = [(a, baseline[b]), (b, baseline[a])]
        else:
            assert not (depends[a] and depends[b])
            if depends[a] or depends[b]:
                u, v = (a, b) if depends[a] else (b, a)
                edges[w] = [(u, baseline[v])]

    def sweep(target):
        context = [zero]*nodes
        context[target] = one
        for w in range(target, 2*n-1, -1):
            for u, factor in edges[w]:
                add = build('and', context[w], factor)
                context[u] = build('or', context[u], add)
        return context

    if cuts is None:
        return program, sweep(out)[n:2*n]

    targets = [v for w in selected for v in gates[w-2*n][1:]] + [out]
    contexts = {t: sweep(t) for t in sorted(set(targets))}
    outputs = []
    for line in range(n):
        cut_values = {}

        def query(t):
            coeff = contexts[t]
            value = build('or', baseline[t], coeff[n+line])
            for w, cut in cut_values.items():
                value = build('or', value, build('and', coeff[w], cut))
            return value

        for w in selected:
            _, a, b = gates[w-2*n]
            cut_values[w] = build('and', query(a), query(b))
        outputs.append(query(out))
    return program, outputs


def check_line_program(lines):
    n = len(lines)
    # Dualize the stars so every marked gate now combines two line predicates.
    gates, marked, out = controlled_stars(lines)
    swap = lambda v: (v+n) % (2*n) if v < 2*n else v
    gates = [(op, swap(a), swap(b)) for op,a,b in gates]
    linear, witness = line_program(n, gates, out, None)
    exact, outputs = line_program(n, gates, out, set(marked))
    one_cut, repaired = line_program(n, gates, out, {min(marked)}, permit_collisions=True)
    k = len(marked)
    assert len(linear) <= 4*len(gates)+1-2*n
    assert len(exact) <= (2*k+2)*len(gates)+(2*k*k+3*k+1)*n

    def run(program, heads, row):
        values = [bool(row & (1<<p)) for p in range(n)]
        read = lambda v: (v == -2) if v < 0 else values[v]
        for op,a,b in program:
            values.append((read(a) or read(b)) if op == 'or' else (read(a) and read(b)))
        return tuple(read(v) for v in heads)

    caught = restored = 0
    for row in range(1<<n):
        a, b = run(linear, witness, row), run(exact, outputs, row)
        c = run(one_cut, repaired, row)
        for l in range(n):
            truth = any(l in lines[p] for p in range(n) if row & (1<<p))
            assert b[l] == truth and (not a[l] or truth)
            assert not c[l] or truth
            if row and row & (row-1) == 0:
                caught += a[l]
                restored += c[l]
    assert caught == sum(map(len,lines))-(n-1) and restored == caught+1
    print(f'order {len(lines[0])-1}: {caught} one-line witnesses; '
          f'{restored} after one cut; all {n*(1<<n)} point-set/line outputs exact with all cuts')


if __name__=='__main__':
    # A guard originally false on every negative pair becomes forceable after another pin.
    revisit=lambda row:[row==7,bool(row&1)]
    assert stabilize([0,1],revisit,lambda _:True,3)==7
    check(plane((0,1,3),7),all_sparse=True)
    check(plane((0,1,3,9),13))
    check_line_program(plane((0,1,3),7))
