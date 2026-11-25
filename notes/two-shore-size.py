"""Check the four-gate schedules for K(2,3) and each two-by-three graph construction."""
from itertools import combinations

def raw_bits(n):
    return [sum(((row >> i) & 1) << row for row in range(1 << n)) for i in range(n)]

def tight_schedules(n, target):
    values = raw_bits(n)
    count = 0
    winning = []
    def visit(frontier, gates):
        nonlocal count
        if len(frontier) == 1:
            count += 1
            if values[frontier[0]] == target:
                winning.append(tuple(gates))
            return
        for u,v in combinations(frontier,2):
            rest = [w for w in frontier if w != u and w != v]
            w = len(values)
            for op,value in (("and",values[u]&values[v]),("or",values[u]|values[v])):
                values.append(value)
                visit(rest+[w],gates+[(op,u,v)])
                values.pop()
    visit(list(range(n)),[])
    return count,winning

def construct(columns):
    # Split line vertices by the subset of the two points they meet.
    values = raw_bits(2+len(columns))
    gates = []
    def gate(op,u,v):
        if u is None or v is None:
            return None if op=="and" else (u if v is None else v)
        gates.append((op,u,v))
        values.append(values[u]&values[v] if op=="and" else values[u]|values[v])
        return len(values)-1
    def join(block):
        out = None
        for v in block:
            out = gate("or",out,v)
        return out
    a,b,c = (join([j+2 for j,g in enumerate(columns) if g==k]) for k in (1,2,3))
    if c is not None and a is None and b is None:
        out = gate("and",gate("or",0,1),c)
    else:
        out = gate("or",gate("and",0,gate("or",a,c)),gate("and",1,gate("or",b,c)))
    n = sum(k!=0 for k in columns)+sum(any(k & side for k in columns) for side in (1,2))
    target = 0
    for j,k in enumerate(columns):
        for i in (0,1):
            if k & (1<<i):
                target |= values[i]&values[2+j]
    assert out is not None and values[out] == target
    extra = (3 in columns) and any(k in (1,2) for k in columns)
    assert len(gates)==n-1+int(extra)
    return target

def graph_classes(n):
    """Classify all isolate-free graphs by their open-neighborhood quotient."""
    from itertools import combinations
    raw = raw_bits(n)
    pairs = list(combinations(range(n),2))
    result = {}
    for code in range(1,1<<len(pairs)):
        neighbors = [set() for _ in range(n)]
        table = 0
        for k,(u,v) in enumerate(pairs):
            if code>>k&1:
                neighbors[u].add(v)
                neighbors[v].add(u)
                table |= raw[u]&raw[v]
        if not all(neighbors):
            continue
        classes = {}
        for v,adj in enumerate(neighbors):
            classes.setdefault(frozenset(adj),[]).append(v)
        groups = list(classes.values())
        quotient = [{j for j,g in enumerate(groups) if g[0] in neighbors[c[0]]} for c in groups]
        todo = set(range(len(groups)))
        extra = 0
        while todo:
            start = next(iter(todo))
            comp = {start}
            for _ in groups:
                comp |= {j for i in comp for j in quotient[i]}
            todo -= comp
            degrees = sorted(len(quotient[i]) for i in comp)
            if degrees == [1,1]:
                continue
            if degrees in ([1,1,2,2],[1,1,2,2,2]):
                extra += 1
            else:
                extra = 2
                break
        result[table] = min(2,extra)
    return result

def one_extra_tables(n):
    """Generate live circuits with one duplicated wire, allowing an internal one."""
    from functools import lru_cache
    initial = tuple(sorted(raw_bits(n)))
    outputs = set()
    @lru_cache(None)
    def visit(frontier, split):
        if len(frontier)==1:
            if split:
                outputs.add(frontier[0])
            return
        # Multiset entries stand for remaining uses. Both copies of a reused
        # wire have the same table. Distinct wires with equal tables also work.
        for i,j in combinations(range(len(frontier)),2):
            a,b = frontier[i],frontier[j]
            rest = frontier[:i]+frontier[i+1:j]+frontier[j+1:]
            for v in {a&b,a|b}:
                visit(tuple(sorted(rest+(v,))),split)
                if not split:
                    visit(tuple(sorted(rest+(v,v))),True)
    for value in initial:
        visit(tuple(sorted(initial+(value,))),True)
    visit(initial,False)
    return outputs

def verify_quotients():
    for n in range(2,6):
        classes = graph_classes(n)
        small = one_extra_tables(n)
        # Circuits at n-1 gates may be included by duplicating a trivial wire;
        # check both classes against explicit read-once synthesis as well.
        from functools import lru_cache
        @lru_cache(None)
        def read_once(S):
            if S&(S-1)==0:
                return {raw_bits(n)[S.bit_length()-1]}
            result = set()
            A = (S-1)&S
            while A:
                B = S^A
                if A<B:
                    for f in read_once(A):
                        for g in read_once(B):
                            result.update((f&g,f|g))
                A = (A-1)&S
            return result
        tight = read_once((1<<n)-1)
        for f,klass in classes.items():
            assert (f in tight)==(klass==0)
            assert (f in small or f in tight)==(klass<=1)
        counts = [sum(v==k for v in classes.values()) for k in range(3)]
        print(f"{n} vertices: {len(classes)} isolate-free graphs; size classes {counts}.")

if __name__=="__main__":
    from itertools import product
    for cols in product(range(4), repeat=3):
        if any(cols):
            construct(cols)
    total,winning = tight_schedules(5, construct((3,3,3)))
    assert total==2880 and len(winning)==9
    for gates in winning:
        assert [g[0] for g in gates] == ["or","or","or","and"]
        assert ("or",0,1) in gates
    print("All 63 nonempty labelled two-by-three graphs meet the stated size.")
    print("K(2,3): 9 of 2880 commutative topological schedules attain four gates.")
    verify_quotients()
