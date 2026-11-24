"""Verify graph lower bounds by restrictions and sample gate-ownership exchanges.

Graphs are tuples of neighbor masks and have no loops or parallel edges.
Run with an integer argument to change the census maximum (default 10).
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
import sys


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def count(mask):
    return bin(mask).count('1')


@lru_cache(None)
def canonical(graph):
    if not graph:
        return ()
    def refine(cells):
        while True:
            groups = []
            for cell in cells:
                buckets = {}
                for v in cell:
                    tag = tuple(sum(bool(graph[v] & (1 << j)) for j in t) for t in cells)
                    buckets.setdefault(tag, []).append(v)
                groups.extend(tuple(buckets[t]) for t in sorted(buckets))
            if len(groups) == len(cells):
                return groups
            cells = groups
    def visit(cells):
        cells = refine(cells)
        choices = [(len(cell), i) for i, cell in enumerate(cells) if len(cell)>1]
        if not choices:
            order = [c[0] for c in cells]
            return tuple(sum(1 << j for j,w in enumerate(order) if graph[v] & (1<<w))
                         for v in order)
        _, i = min(choices)
        cell = cells[i]
        found = {}
        for v in cell:
            # Equal open neighborhoods permit swapping these two vertices.
            if graph[v] not in found:
                rest = tuple(w for w in cell if w != v)
                found[graph[v]] = visit(cells[:i]+[(v,), rest]+cells[i+1:])
        return min(found.values())
    return visit([tuple(range(len(graph)))])


def induced(graph, keep):
    order = [v for v in bits(keep) if graph[v] & keep]
    return canonical(tuple(sum(1<<j for j,w in enumerate(order) if graph[v] & (1<<w))
                           for v in order))


def grow(graph):
    n = len(graph)
    far = []
    for v, near in enumerate(graph):
        bad = near
        for w in bits(near):
            bad |= graph[w]
        far.append(bad)
    for s in range(1<<n):
        if any(s & far[v] & ~(1<<v) for v in bits(s)):
            continue
        yield canonical(tuple(mask | (((s>>v)&1)<<n) for v,mask in enumerate(graph))+(s,))


@lru_cache(None)
def cover(graph):
    n = len(graph)
    for k in range(n+1):
        for chosen in combinations(range(n), k):
            off = ((1<<n)-1) ^ sum(1<<v for v in chosen)
            if all(not graph[v] & off for v in bits(off)):
                return k


def forest(graph):
    left = (1<<len(graph))-1
    while left:
        v = next((v for v in bits(left) if count(graph[v]&left)<=1), None)
        if v is None: return False
        left ^= 1<<v
    return True


def protected(graph, eligible):
    # Greatest subset in which the AND and OR obstructions hold at every input.
    while eligible:
        keep = sum(1<<v for v in bits(eligible) if graph[v] & eligible and
                   any(not graph[w] & ~eligible for w in bits(graph[v])))
        if keep == eligible: return True
        eligible = keep
    return False


def upper(graph):
    return max(0, sum(map(count,graph))//2+cover(graph)-1)



def theta233():
    edges = [(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
    return canonical(tuple(sum(1<<b for e in edges for a,b in (e,e[::-1]) if a==v)
                           for v in range(7)))


def can_enter(graph, profiles):
    """Necessary order conditions for a least lift-fixed circuit."""
    n = len(graph)
    entered = 0
    for v,w in combinations(range(n),2):
        for op in (0,1):  # 0=OR; 1=AND
            def can_pair(x,y):
                for d,a in profiles[x]:
                    if (a if op else d-a)==0:
                        continue
                    if d>1 or (op and graph[x]==1<<y) or (not op and not graph[x]&~graph[y]):
                        return True
                return False
            if can_pair(v,w) and can_pair(w,v):
                entered |= (1<<v)|(1<<w)
    if not entered: return False

    def transversal(x, pool):
        # One distance-two representative per neighbor, all mutually independent.
        targets = tuple(bits(graph[x]))
        def choose(i, allowed):
            if i==len(targets): return True
            for z in bits(graph[targets[i]] & allowed):
                if choose(i+1, allowed & ~(1<<z) & ~graph[z]): return True
            return False
        return choose(0, pool & ~graph[x] & ~(1<<x))

    while True:
        add = 0
        for x in range(n):
            if entered & (1<<x): continue
            along_and = (1,1) in profiles[x] and not graph[x] & ~entered
            along_or = (1,0) in profiles[x] and transversal(x, entered)
            if along_and or along_or or any(d>=2 for d,_ in profiles[x]):
                add |= 1<<x
        if not add: return entered==(1<<n)-1
        entered |= add


def possible_size(graph, restrictions, s):
    profiles = []
    for lo,hi in restrictions:
        cap = min(s-lo,s-hi)
        options = [(d,a) for d in range(1,cap+1) for a in range(d+1)
                   if d+min(a,2)<=s-lo and d+min(d-a,2)<=s-hi]
        if not options: return False
        profiles.append(options)
    return can_enter(graph,profiles)


@lru_cache(None)
def input_bounds_eight():
    # Three exact-size UNSAT instances are reproduced by --solve-eight.
    result = {g:11 for g in ((128,64,32,144,72,196,50,41),
                              (128,64,160,80,40,20,138,69),
                              (128,64,160,144,72,68,50,13))}
    def relabel(edges):
        return canonical(tuple(sum(1<<b for e in edges for a,b in (e,e[::-1]) if a==v)
                               for v in range(8)))
    bipartite = [(i,4+j) for j,m in enumerate((3,5,9,14)) for i in range(4) if m&(1<<i)]
    result[relabel(bipartite)] = 12
    petersen = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
    result[relabel([(a-(a>6),b-(b>6)) for a,b in petersen if 6 not in (a,b)])] = 13
    assert len(result)==5 and all(upper(g)==cost for g,cost in result.items())
    return result


@lru_cache(None)
def lower(graph):
    if len(graph)==8 and graph in input_bounds_eight():
        return input_bounds_eight()[graph]
    return elementary(graph)


@lru_cache(None)
def elementary(graph):
    if forest(graph): return upper(graph)
    if len(graph)==7 and graph==theta233(): return 11
    n = len(graph)
    all_nodes = (1<<n)-1
    target = upper(graph)
    # Duplicate leaves give a one-gate lower bound with one of them deleted.
    for a,b in combinations(range(n),2):
        if graph[a]==graph[b]:
            return 1+lower(induced(graph, all_nodes ^ (1<<b)))
    for v in range(n):
        for w in bits(graph[v]):
            if graph[v]==1<<w and graph[w]==1<<v:
                return 2+lower(induced(graph,all_nodes^(1<<v)^(1<<w)))
    bound = n-1
    costs = []
    restrictions = []
    for v, near in enumerate(graph):
        outside = all_nodes^(1<<v)
        low = induced(graph, outside)
        high = induced(graph, outside & ~near)
        lo = lower(low)
        hi = lower(high)+count(near)-(not high)
        bound = max(bound, lo+n-len(low), hi+n-len(high)-count(near), min(lo,hi)+2)
        restrictions.append((lo,hi))
        costs.append(min(max(lo+a,hi+b) for a,b in ((3,3),(4,2),(2,4))))
    # At least one input of the first binary raw gate is read twice.
    bound = max(bound, min(costs))
    for t in range(target,bound,-1):
        eligible = sum(1<<v for v in range(n) if costs[v]>=t and count(graph[v])>=2)
        if protected(graph, eligible):
            bound=t
            break
    while bound<target and not possible_size(graph,restrictions,bound):
        bound+=1
    assert bound<=target, (graph,bound,target)
    return bound


def census(limit):
    layer = {()}
    for n in range(1,limit+1):
        layer = {g for h in layer for g in grow(h)}
        active = sorted(g for g in layer if all(g))
        gap = Counter(upper(g)-lower(g) for g in active)
        cycles = [g for g in active if not forest(g)]
        print(f'{n} active vertices: {len(active)} graphs, {len(cycles)} cyclic, '
              f'upper minus verified lower {dict(sorted(gap.items()))}', flush=True)




def bipartite(graph):
    colors={}
    for root in range(len(graph)):
        if root in colors: continue
        colors[root]=0
        stack=[root]
        while stack:
            v=stack.pop()
            for w in bits(graph[v]):
                if w not in colors:
                    colors[w]=1-colors[v]
                    stack.append(w)
                elif colors[w]==colors[v]:
                    return False
    return True


def cover_kernels(k):
    """Enumerate girth-five graphs via a distinguished minimum vertex cover."""
    pairs=list(combinations(range(k),2))
    seen=set()
    inside_types=set()
    for pattern in range(1<<len(pairs)):
        edges=[e for j,e in enumerate(pairs) if pattern&(1<<j)]
        inside=tuple(sum(1<<b for e in edges for a,b in (e,e[::-1]) if a==v) for v in range(k))
        if any(inside[a]&inside[b] for a,b in edges): continue
        if any(count(inside[a]&inside[b])>1 for a,b in pairs):continue
        code=canonical(inside)
        if code in inside_types: continue
        inside_types.add(code)
        rows=[s for s in range(1,1<<k) if all(
            not (inside[a]&(1<<b) or inside[a]&inside[b]) for a,b in combinations(bits(s),2))]
        def visit(j,selected):
            if j<len(rows):
                visit(j+1,selected)
                if all(count(rows[j]&t)<=1 for t in selected):
                    visit(j+1,selected+[rows[j]])
                return
            a=tuple(inside[v] | sum(1<<(k+i) for i,t in enumerate(selected) if t&(1<<v))
                    for v in range(k))+tuple(selected)
            if not all(a) or len(set(a))!=len(a):return
            g=canonical(a)
            if g in seen:return
            def smaller(mask,budget):
                active=next(((v,graph_neighbors & mask) for v,graph_neighbors in enumerate(g)
                             if mask&(1<<v) and graph_neighbors&mask),None)
                if active is None:return True
                if not budget:return False
                v,ns=active; w=next(bits(ns))
                return smaller(mask^(1<<v),budget-1) or smaller(mask^(1<<w),budget-1)
            if not smaller((1<<len(g))-1,k-1):seen.add(g)
        visit(0,[])
    return seen


def eight_solvers(seconds):
    """Reproduce the three ten-gate exclusions using the project's prior encoder."""
    from concurrent.futures import ThreadPoolExecutor
    from pathlib import Path
    import runpy, subprocess
    notes = Path(__file__).resolve().parent
    lib = runpy.run_path(str(notes/'check-petersen-monotone.py'))
    root = notes.parent/'lean'
    prefix = Path(subprocess.check_output(['lean','--print-prefix'],cwd=root,text=True).strip())
    graphs = {()}
    for _ in range(8):
        graphs = {g for h in graphs for g in grow(h)}
    remaining = sorted(g for g in graphs if all(g) and elementary(g)<upper(g) and upper(g)==11)

    def solve(graph):
        n = len(graph)
        size = elementary(graph)
        assert size+1==upper(graph)
        full=(1<<n)-1
        edges = [(i,j) for i in range(n) for j in bits(graph[i]) if i<j]
        positive = [(1<<i)|(1<<j) for i,j in edges]
        table = tuple(any(row & pair == pair for pair in positive) for row in range(1<<n))
        negative = [row for row in range(1<<n) if not table[row] and
                    all(table[row|(1<<i)] for i in bits(full^row))]
        cnf, gates = lib['encode'](n,size,table,positive,negative)
        # Add the stronger proved pin bounds from this census. They apply to
        # every minimum circuit, regardless of whether its OR gates are lifted.
        for v,near in enumerate(graph):
            zero, one = induced(graph,full^(1<<v)), induced(graph,full & ~near & ~(1<<v))
            caps = (size-lower(zero), size-(lower(one)+count(near)-(not one)))
            reads = []
            for a,b,_ in gates:
                r = cnf.variable()
                cnf.clauses.extend(([-a[v],r],[-b[v],r],[-r,a[v],b[v]]))
                reads.append(r)
            for subset in combinations(range(size),min(caps)+1):
                cnf.clauses.append([-reads[j] for j in subset])
            for d in range(1,min(caps)+1):
                for subset in combinations(range(size),d):
                    for value,cap in enumerate(caps):
                        need = cap-d+1
                        if 1<=need<=min(2,d):
                            for constrained in combinations(subset,need):
                                cnf.clauses.append([-reads[j] for j in subset]+
                                    [(-gates[j][2] if value else gates[j][2]) for j in constrained])
        data=f'p cnf {cnf.variables} {len(cnf.clauses)}\n'+''.join(
            ' '.join(map(str,clause))+' 0\n' for clause in cnf.clauses)
        res=subprocess.run([str(prefix/'bin/cadical'),'-q','--check','--checkproof=2',
                            '-t',str(seconds)],input=data,text=True,capture_output=True,timeout=seconds+15)
        if res.returncode==20:
            assert 's UNSATISFIABLE' in res.stdout
            return graph,size,'UNSAT'
        if res.returncode==0:
            return graph,size,'timeout'
        if res.returncode==10:
            assignment={int(x) for line in res.stdout.splitlines() if line.startswith('v ')
                        for x in line.split()[1:] if int(x)>0}
            def select(port): return next(i for i,b in enumerate(port) if b in assignment)
            program=[(op in assignment,select(a),select(b)) for a,b,op in gates]
            for row,expected in enumerate(table):
                wires=[bool(row&(1<<v)) for v in range(n)]
                for is_or,a,b in program:
                    wires.append((wires[a] or wires[b]) if is_or else (wires[a] and wires[b]))
                assert wires[-1]==expected
            return graph,size,program
        raise RuntimeError((res.returncode,res.stderr))

    with ThreadPoolExecutor(max_workers=2) as pool:
        from concurrent.futures import as_completed
        jobs=[pool.submit(solve,g) for g in remaining]
        for job in as_completed(jobs):
            print('eight-vertex check',job.result(),flush=True)



def ownership_tests():
    n=4
    raw=[sum(1<<row for row in range(1<<n) if row & (1<<v)) for v in range(n)]
    graphs={}
    pairs=list(combinations(range(n),2))
    for mask in range(1,1<<len(pairs)):
        use=[p for j,p in enumerate(pairs) if mask & (1<<j)]
        # On four vertices every graph of girth at least five is a forest.
        adj=tuple(sum(1<<b for e in use for a,b in (e,e[::-1]) if a==v) for v in range(n))
        if not forest(adj): continue
        F=0
        for a,b in use: F|=raw[a]&raw[b]
        graphs[F]=use

    stats=Counter()
    def evaluate(gates, forced=None):
        values=raw.copy()
        inside=[set() for _ in raw]
        for j,(op,a,b) in enumerate(gates):
            vals=(values[a]&values[b]) if op=='and' else (values[a]|values[b])
            values.append(vals if not forced or forced[0]!=j else forced[1])
            inside.append(inside[a] | inside[b] | ({a-n} if a>=n else set()) |
                          ({b-n} if b>=n else set()))
        return values, inside

    def owners(gates,vals,inside,edges):
        all_flags=sum(1<<((1<<u)|(1<<v)) for u,v in edges)
        result=[]
        for j,(op,_,_) in enumerate(gates):
            mask=vals[n+j]&all_flags if op=='and' else 0
            for k in inside[n+j]:
                if gates[k][0]=='and': mask &= ~vals[n+k]
            result.append(mask)
        return result

    def audit(gates):
        vals,inside=evaluate(gates)
        F=vals[-1]
        if F not in graphs or len(inside[-1])+1!=len(gates): return
        edges=graphs[F]
        before=owners(gates,vals,inside,edges)
        all_flags=sum(1<<((1<<u)|(1<<v)) for u,v in edges)
        stats['live correct']+=1
        for j,(op,_,_) in enumerate(gates):
            if op!='and' or before[j]:continue
            zero=evaluate(gates,(j,0))[0][-1]
            lost=all_flags & ~zero
            if not lost: continue
            stats['pivotal ownerless']+=1
            def verify(new,kind):
                after,cones=evaluate(new)
                assert after[-1]==F
                owned=owners(new,after,cones,edges)
                assert all(not (old & ~new) for old,new in zip(before,owned))
                assert new[j][0]!='and' or owned[j]
                stats[kind]+=1
            if count(lost)==1:
                row=next(bits(lost))
                a,b=bits(row)
                new=gates.copy();new[j]=('and',a,b)
                verify(new,'single-edge repairs')
            force=evaluate(gates,(j,(1<<(1<<n))-1))[0][-1]
            forbidden=force & ~F
            eligible=[i for i in inside[n+j] if gates[i][0]=='and' and not vals[n+i]&forbidden]
            for ia,a in enumerate(eligible):
                for b in eligible[ia:]:
                    if not lost & ~(vals[n+a]|vals[n+b]):
                        new=gates.copy();new[j]=('or',n+a,n+b)
                        verify(new,'ancestor repairs')

    def enumerate_live(gates, previous, limit):
        if gates: audit(gates)
        if len(gates)==limit: return
        for b in range(1,n+len(gates)):
            for a in range(b):
                if (b,a)<previous: continue
                for op in ('and','or'):
                    enumerate_live(gates+[(op,a,b)],(b,a),limit)
    enumerate_live([],(-1,-1),4)
    # Neither operand of the last gate can replace it. Two safe ancestral
    # signals do suffice, although the unsafe alternatives on each side differ.
    audit([('and',0,1),('and',2,3),('or',4,5),('and',0,2),('and',1,3),
           ('or',6,7),('or',6,8),('and',9,10)])
    # A private seven-gate expression for a two-edge matching has no admissible
    # ancestral AND on the output's sensitive negative rows.
    obstruction=[('or',0,2),('or',0,3),('and',4,5),
                 ('or',1,2),('or',1,3),('and',7,8),('and',6,9)]
    audit(obstruction)
    vals,cones=evaluate(obstruction)
    target=(raw[0]&raw[1])|(raw[2]&raw[3])
    assert vals[-1]==target and all(vals[n+j] & ~target for j in (2,5))
    assert not owners(obstruction,vals,cones,graphs[target])[-1]
    print('ownership checks',dict(stats))


if __name__ == '__main__':
    if sys.argv[1:2]==['--covers']:
        for k in range(1,1+(int(sys.argv[2]) if len(sys.argv)>2 else 4)):
            group=cover_kernels(k)
            odd=[g for g in group if not bipartite(g)]
            dist=Counter(upper(g)-lower(g) for g in odd)
            print('cover',k,'reduced',len(group),'nonbipartite',len(odd),'nonbipartite gaps',dict(sorted(dist.items())),flush=True)
    elif sys.argv[1:2]==['--owners']:
        ownership_tests()
    elif sys.argv[1:2]==['--solve-eight']:
        eight_solvers(int(sys.argv[2]) if len(sys.argv)>2 else 90)
    else:
        census(int(sys.argv[1]) if len(sys.argv)>1 else 10)
