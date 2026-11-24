"""Factor singleton-true ANDs in binary monotone circuits. All wire IDs are topological."""
from collections import Counter
from dataclasses import dataclass
from itertools import combinations, product
from functools import lru_cache


@dataclass(frozen=True)
class Circuit:
    n: int
    gates: tuple
    output: int


@lru_cache(None)
def raw_tables(n):
    return tuple(sum(1 << mask for mask in range(1<<n) if mask & (1<<i)) for i in range(n))


def tables(c):
    values=list(raw_tables(c.n))
    for op,a,b in c.gates:
        assert op in ("and","or") and 0<=a<len(values) and 0<=b<len(values)
        values.append(values[a]&values[b] if op=="and" else values[a]|values[b])
    return values


def readers(c):
    uses=Counter({c.output:1})
    for _,a,b in c.gates:
        uses.update((a,b))
    return uses


def dirty(c,values):
    singles=sum(1 << (1<<i) for i in range(c.n))
    return [(c.n+j,values[c.n+j]&singles) for j,(op,a,b) in enumerate(c.gates)
            if op=="and" and values[c.n+j]&singles]


def shared(c,values,rows):
    return {values[w]&rows for w,k in readers(c).items() if w>=c.n and k>1}


def rebuild(c,rule=None):
    """Copy the live cone once, replacing one gate by a local reconstruction if requested."""
    mapping={i:i for i in range(c.n)}
    out=[]
    def gate(op,a,b):
        out.append((op,a,b))
        return c.n+len(out)-1
    def visit(w):
        if w in mapping:
            return mapping[w]
        op,a,b=c.gates[w-c.n]
        if rule is not None and w==rule[0]:
            result=rule[1](visit,gate)
        else:
            result=gate(op,visit(a),visit(b))
        mapping[w]=result
        return result
    root=visit(c.output)
    return Circuit(c.n,tuple(out),root)


def any_wire(ws,visit,gate):
    first,*tail=ws
    result=visit(first)
    for w in tail:
        result=gate("or",result,visit(w))
    return result


def private_frontier(c,uses,w):
    if w>=c.n and uses[w]==1:
        op,a,b=c.gates[w-c.n]
        if op=="or":
            return private_frontier(c,uses,a)+private_frontier(c,uses,b)
    return [w]


def solve(c,rows=None):
    c=rebuild(c)
    if rows is None:
        rows=(1 << (1<<c.n))-1
    singles=sum(1 << (1<<i) for i in range(c.n))
    assert rows & singles == singles
    steps=0
    while True:
        values=tables(c)
        bad=dirty(c,values)
        if not bad:
            return c,steps,None
        h,hit=bad[0]
        x=hit & -hit
        _,left,right=c.gates[h-c.n]
        uses=readers(c)
        blockers=[]
        for a,b in ((left,right),(right,left)):
            leaves=private_frontier(c,uses,a)
            rest=[w for w in leaves if values[w]&rows&~values[b]]
            pull=[w for w in leaves if not values[w]&rows&~values[b]]
            fails=[w for w in rest if values[w]&x]
            if fails:
                w=fails[0]
                assert w>=c.n and uses[w]>1 and c.gates[w-c.n][0]=="or"
                blockers.append(w)
                continue
            assert pull
            def replace(visit,gate):
                if not rest:
                    return visit(a)
                u=any_wire(pull,visit,gate)
                inner=gate("and",any_wire(rest,visit,gate),visit(b))
                return gate("or",u,inner)
            nxt=rebuild(c,(h,replace))
            after=tables(nxt)
            assert len(nxt.gates)<=len(c.gates)
            assert (values[c.output]^after[nxt.output]) & rows == 0
            assert shared(nxt,after,rows)<=shared(c,values,rows)
            assert sum(bin(t).count("1") for _,t in dirty(nxt,after)) < sum(bin(t).count("1") for _,t in bad)
            c=nxt
            steps+=1
            break
        else:
            u,v=blockers
            t=values[u]&rows&~values[v]
            z=values[v]&rows&~values[u]
            assert u!=v and t and z
            return c,steps,(u,v,x,t & -t,z & -z)


def primary_rows(n,edges):
    e=[(1<<u)|(1<<v) for u,v in edges]
    univ=(1<<n)-1
    def pos(mask):
        return any(mask&pair==pair for pair in e)
    negatives=[mask for mask in range(univ+1) if not pos(mask) and
               all(pos(mask|(1<<v)) for v in range(n) if not mask&(1<<v))]
    return sum(1<<row for row in set(e+negatives+[1<<i for i in range(n)]))


def truth(n,edges):
    vs=raw_tables(n)
    value=0
    for a,b in edges:
        value|=vs[a]&vs[b]
    return value


def census(n=3,depth=4):
    """All scheduled binary programs with distinct earlier operands, last-gate output."""
    counts=Counter()
    def generate(gates):
        if gates:
            c=Circuit(n,gates,n+len(gates)-1)
            live=rebuild(c)
            values=tables(live)
            before=dirty(live,values)
            out,steps,obstruction=solve(live)
            assert tables(out)[out.output]==values[live.output]
            if before:
                counts["dirty"]+=1
            if steps:
                counts["changed"]+=1
            if obstruction:
                counts["blocked"]+=1
            counts["programs"]+=1
        if len(gates)==depth:
            return
        for a,b in combinations(range(n+len(gates)),2):
            for op in ("and","or"):
                generate(gates+((op,a,b),))
    generate(())
    return dict(counts)


def pin_zero(c,deleted):
    """Use constants only during folding. Retain the live nonconstant residual."""
    ws={i:(None if i==deleted else i) for i in range(c.n)}
    gates=[]
    for j,(op,a,b) in enumerate(c.gates):
        a,b=ws[a],ws[b]
        if a is None or b is None:
            result=None if op=="and" else (b if a is None else a)
        elif a==b:
            result=a
        else:
            result=c.n+len(gates)
            gates.append((op,a,b))
        ws[c.n+j]=result
    if ws[c.output] is None:
        return None
    return rebuild(Circuit(c.n,tuple(gates),ws[c.output]))


def cheapest_alarm(c,x,edges):
    """Find the smallest OR of available wires that recognizes a neighbor on independent inputs."""
    neighbors={b if x==a else a for a,b in edges if x in (a,b)}
    available=[i for i in range(c.n) if i!=x and i not in neighbors]
    residual=[(a,b) for a,b in edges if x not in (a,b)]
    independent=[sum(1<<i for j,i in enumerate(available) if mask & (1<<j))
                 for mask in range(1<<len(available))]
    independent=[r for r in independent if all(r & ((1<<a)|(1<<b)) != ((1<<a)|(1<<b))
                                             for a,b in residual)]
    negatives=[r for r in independent if not any(r!=s and r&s==r for s in independent)]
    negative_table=sum(1 << r for r in negatives)
    values=tables(c)
    goal=sum(1<<v for v in neighbors)
    covers={0:()}
    for wire,table in enumerate(values):
        if wire==x or table & negative_table:
            continue
        mask=sum(1<<v for v in neighbors if table & (1<<(1<<v)))
        if not mask:
            continue
        for hit,old in list(covers.items()):
            union=mask|hit
            if union not in covers or len(old)+1<len(covers[union]):
                covers[union]=old+(wire,)
    return covers[goal]


def restore(c,x,edges):
    values=tables(c)
    assert values[c.output]==truth(c.n,edges)
    after=pin_zero(c,x)
    if after is None:
        # A nonempty star has one AND atop its neighbor OR. No final OR is needed.
        after=Circuit(c.n,(),0)
        old=None
    else:
        old=after.output
    alarm=cheapest_alarm(after,x,edges)
    gates=list(after.gates)
    def gate(op,a,b):
        gates.append((op,a,b))
        return c.n+len(gates)-1
    if not alarm:
        assert old is not None
        out=old
    else:
        w=any_wire(alarm,lambda w:w,gate)
        out=gate("and",x,w)
        if old is not None:
            out=gate("or",old,out)
    new=Circuit(c.n,tuple(gates),out)
    nval=tables(new)
    assert nval[new.output]==values[c.output]
    assert all(mask & (1<<(1<<x))==0 for _,mask in dirty(new,nval))
    before=sum(bin(t).count("1") for _,t in dirty(c,values))
    lost=sum(bool(t & (1<<(1<<x))) for _,t in dirty(c,values))
    assert sum(bin(t).count("1") for _,t in dirty(new,nval))<=before-lost
    return new,alarm



def boundary_rows(n,edges):
    edge_rows=[(1<<u)|(1<<v) for u,v in edges]
    ok=[r for r in range(1<<n) if not any((r & e)==e for e in edge_rows)]
    maximal=[r for r in ok if all(r & (1<<i) or (r|(1<<i)) not in ok for i in range(n))]
    return sum(1<<r for r in edge_rows),sum(1<<r for r in maximal)


def stable_rewrite(c,h,replace):
    """Keep the old relative order of all ANDs when regrouping private OR trees."""
    gates=[]
    mapping={i:i for i in range(c.n)}
    def gate(op,a,b):
        gates.append((op,a,b))
        return c.n+len(gates)-1
    for j,(op,a,b) in enumerate(c.gates):
        wire=c.n+j
        mapping[wire]=replace(mapping.__getitem__,gate) if wire==h else gate(op,mapping[a],mapping[b])
    root=mapping[c.output]
    live={root}
    for j in reversed(range(len(gates))):
        if c.n+j in live:
            live.update(gates[j][1:])
    ren={i:i for i in range(c.n)}
    kept=[]
    for j,(op,a,b) in enumerate(gates):
        if c.n+j in live:
            ren[c.n+j]=c.n+len(kept)
            kept.append((op,ren[a],ren[b]))
    return Circuit(c.n,tuple(kept),ren[root])


def lex_measure(c,values):
    singles=sum(1<<(1<<i) for i in range(c.n))
    ranks=tuple(bin(values[c.n+j]&singles).count("1") for j,g in enumerate(c.gates) if g[0]=="and")
    return len(ranks),ranks


def negative_rewrite(c,edges,sensitive=True):
    """Factor in forward AND order. Only maximal negative rows constrain an increase."""
    c=rebuild(c)
    _,negative=boundary_rows(c.n,edges)
    full=(1<<(1<<c.n))-1
    steps=0
    while True:
        vals=tables(c)
        assert vals[c.output]==truth(c.n,edges)
        ds=dirty(c,vals)
        if not ds:
            return c,steps,None
        h,hit=ds[0]
        x=hit & -hit
        rows=negative
        if sensitive:
            hi=list(raw_tables(c.n))
            for j,(op,a,b) in enumerate(c.gates):
                val=hi[a]&hi[b] if op=="and" else hi[a]|hi[b]
                hi.append(full if c.n+j==h else val)
            rows &= hi[c.output]
        uses=readers(c)
        _,a,b=c.gates[h-c.n]
        blockers=[]
        for left,right in [(a,b),(b,a)]:
            leaves=private_frontier(c,uses,left)
            safe=[w for w in leaves if not vals[w]&rows&~vals[right]]
            rest=[w for w in leaves if vals[w]&rows&~vals[right]]
            blocked=[w for w in rest if vals[w]&x]
            if blocked:
                w=blocked[0]
                assert w>=c.n and uses[w]>1 and c.gates[w-c.n][0]=="or"
                blockers.append(w)
                continue
            assert safe
            def replace(visit,gate):
                if not rest:
                    return visit(left)
                inner=gate("and",any_wire(rest,visit,gate),visit(right))
                return gate("or",any_wire(safe,visit,gate),inner)
            new=stable_rewrite(c,h,replace)
            newvals=tables(new)
            assert len(new.gates)<=len(c.gates)
            assert lex_measure(new,newvals)<lex_measure(c,vals)
            if not sensitive:
                assert shared(new,newvals,rows)<=shared(c,vals,rows)
            c=new
            steps+=1
            break
        else:
            u,v=blockers
            first=vals[u]&rows&~vals[v]
            second=vals[v]&rows&~vals[u]
            assert first and second and not first&second
            return c,steps,(x,u,v,first & -first,second & -second)


def splice(c,h,edges):
    """Choose an OR of independent wires. A later wire outside h's fanout is eligible."""
    values=tables(c)
    assert values[c.output]==truth(c.n,edges)
    positives,negatives=boundary_rows(c.n,edges)
    singles=sum(1<<(1<<i) for i in range(c.n))
    target=positives&values[h]
    forbidden=(negatives|singles)&~values[h]
    depends={h}
    for j,(_,a,b) in enumerate(c.gates):
        if a in depends or b in depends:
            depends.add(c.n+j)
    fits={0:()}
    for w,t in enumerate(values):
        if w in depends or t&forbidden:
            continue
        for old,path in list(fits.items()):
            covered=old|(target&t)
            if covered not in fits or len(path)+1<len(fits[covered]):
                fits[covered]=path+(w,)
    if not target or target not in fits:
        return None
    chosen=fits[target]
    new=rebuild(c,(h,lambda visit,gate:any_wire(chosen,visit,gate)))
    new_vals=tables(new)
    assert new_vals[new.output]==values[c.output]
    assert sum(bin(t).count("1") for _,t in dirty(new,new_vals))<sum(bin(t).count("1") for _,t in dirty(c,values))
    return new,chosen


def included_wire_control():
    c=Circuit(4,(("or",0,1),("or",0,2),("and",4,5),("and",1,2),
                 ("or",3,7),("and",6,8),("or",4,5),("and",9,10)),11)
    new,wires=splice(c,6,[(0,3),(1,2)])
    assert 7 in wires and not dirty(new,tables(new)) and len(new.gates)<=len(c.gates)
    return len(c.gates),len(new.gates),wires

def graph_controls():
    # Matching x-e and a-b. The local target h=x OR (a AND b) contributes to both edges.
    # Forcing h to zero destroys both. Its two OR operands have other live readers.
    edges=[(0,3),(1,2)]
    c=Circuit(4,(("or",0,1),("or",0,2),("and",4,5),("and",1,2),
                 ("or",3,7),("and",6,8),("or",4,5),("and",9,10)),11)
    vals=tables(c)
    assert vals[c.output]==truth(4,edges)
    for rows in [None,primary_rows(4,edges)]:
        _,steps,block=solve(c,rows)
        assert steps==0 and block
    new,wires=restore(c,0,edges)
    assert len(wires)==1 and len(new.gates)<=len(c.gates)
    assert not dirty(new,tables(new))
    # The same matching supplies an algebraic sharp local lower bound.
    # No free wire or singleton-clean one-gate expression covers x and a-b without a or b alone.
    raw=raw_tables(3)
    pool=(*raw,raw[0]|raw[1],raw[0]|raw[2])
    accepted=(1<<1)|(1<<6)
    forbidden=(1<<2)|(1<<4)
    def fits(v):
        return v&accepted==accepted and v&forbidden==0
    assert not any(fits(v) for v in pool)
    assert not any(fits(a|b) or (not (a&b)&(1<<1) and fits(a&b)) for a,b in product(pool,repeat=2))
    return len(c.gates),len(new.gates),wires

def controls():
    # Two non-equivalent shared gates with a common singleton.
    gates=(("or",0,1),("or",0,2),("and",3,4),("and",5,1),
           ("and",3,2),("and",4,1),("or",6,7),("or",8,9))
    c=Circuit(3,gates,10)
    out,steps,block=solve(c)
    assert block and steps==0
    # A genuinely used private OR with a clean AND leaf, plus shared signals below it.
    c=Circuit(5,(("or",0,1),("or",0,2),("and",3,4),("or",0,7),
                ("and",8,5),("or",9,6),("and",10,3)),11)
    out,steps,block=solve(c)
    assert steps and block is None
    return len(c.gates),len(out.gates)


def force_table(c,h,value):
    ws=list(raw_tables(c.n))
    full=(1<<(1<<c.n))-1
    for j,(op,a,b) in enumerate(c.gates):
        v=ws[a]&ws[b] if op=="and" else ws[a]|ws[b]
        ws.append((full if value else 0) if c.n+j==h else v)
    return ws


def one_gate_repair(c,h,edges):
    """Search the exact decisive rows for an independent wire or one clean AND/OR."""
    values=tables(c)
    yes,no=boundary_rows(c.n,edges)
    need=yes&~force_table(c,h,False)[c.output]
    forbidden=no&force_table(c,h,True)[c.output]
    singles=sum(1<<(1<<i) for i in range(c.n))
    depends={h}
    for j,(_,a,b) in enumerate(c.gates):
        if a in depends or b in depends:
            depends.add(c.n+j)
    ws=[w for w in range(len(values)) if w not in depends]
    options=[(None,w,w) for w in ws]+[(op,a,b) for a,b in combinations(ws,2) for op in ("or","and")]
    for op,a,b in options:
        val=values[a] if op is None else (values[a]|values[b] if op=="or" else values[a]&values[b])
        if need&~val or val&forbidden or val&singles&~values[h] or (op=="and" and val&singles):
            continue
        def replacement(visit,gate):
            return visit(a) if op is None else gate(op,visit(a),visit(b))
        new=rebuild(c,(h,replacement))
        ns=tables(new)
        assert ns[new.output]==values[c.output]
        assert len(new.gates)<=len(c.gates)
        assert sum(bin(t).count("1") for _,t in dirty(new,ns))<sum(bin(t).count("1") for _,t in dirty(c,values))
        return new,(op,a,b)
    return None


def bypass(c,edges):
    """Remove one gate whenever a single operand suffices on its sensitive boundary rows."""
    vals=tables(c)
    yes,no=boundary_rows(c.n,edges)
    for j,(op,a,b) in enumerate(c.gates):
        h=c.n+j
        if op=="and":
            sensitive=no&force_table(c,h,True)[c.output]
        else:
            sensitive=yes&~force_table(c,h,False)[c.output]
        for w in (a,b):
            if (vals[h]^vals[w])&sensitive:
                continue
            new=rebuild(c,(h,lambda visit,gate:visit(w)))
            assert len(new.gates)<len(c.gates)
            assert truth(c.n,edges)==tables(new)[new.output]
            return new
    return None


def simplify_then_factor(c,edges):
    while True:
        c,_,stuck=negative_rewrite(c,edges)
        if stuck is None:
            return c
        simpler=bypass(c,edges)
        if simpler is None:
            return None
        c=simpler


def fork_census(depth=4):
    """All suffixes through four gates after A=x+a, B=x+b, h=A AND B on four inputs."""
    n=4
    pairs=list(combinations(range(n),2))
    families={}
    for mask in range(1,1<<len(pairs)):
        edges=tuple(e for j,e in enumerate(pairs) if mask & (1<<j))
        if len(edges)>3:
            continue  # Every bipartite four-cycle-free graph on four vertices is a forest.
        if not any(all(((side>>a)^(side>>b))&1 for a,b in edges) for side in range(16)):
            continue
        families[truth(4,edges)]=edges
    raw=raw_tables(n)
    U,V=raw[0]|raw[1],raw[0]|raw[2]
    vs=[*raw,U,V,U&V]
    off=[*raw,U,V,0]
    marks=[0,0,0,0,0,0,4]
    gates=[("or",0,1),("or",0,2),("and",4,5)]
    counts=Counter()
    unique=set()
    candidates={m:list(combinations(range(m),2)) for m in range(7,7+depth)}
    def rec(left):
        m=len(vs)
        for a,b in candidates[m]:
            flag=marks[a]|marks[b]|int(a==4 or b==4)|(2*int(a==5 or b==5))
            for op in ("or","and"):
                val=vs[a]|vs[b] if op=="or" else vs[a]&vs[b]
                low=off[a]|off[b] if op=="or" else off[a]&off[b]
                if flag==7 and low!=val and val in families:
                    counts["schedules"]+=1
                    c=rebuild(Circuit(n,tuple(gates)+((op,a,b),),m))
                    if c not in unique:
                        unique.add(c)
                        edges=families[val]
                        u,_,stuck=negative_rewrite(c,edges)
                        if stuck:
                            counts["blocked by sensitive negative rows"]+=1
                            h=dirty(u,tables(u))[0][0]
                            alt=splice(u,h,edges)
                            one=one_gate_repair(u,h,edges)
                            if one:
                                counts["covered by a sensitive one-gate repair"]+=1
                            if alt and len(alt[0].gates)<=len(u.gates):
                                counts["covered by old-wire OR"]+=1
                            x=stuck[0].bit_length()-1
                            v=x.bit_length()-1
                            restored,_=restore(u,v,edges)
                            if len(restored.gates)<=len(u.gates):
                                counts["covered by vertex pin"]+=1
                            choices=[a for a in [one[0] if one else None,alt[0] if alt else None,restored] if a is not None and len(a.gates)<=len(u.gates)]
                            if any(negative_rewrite(a,edges)[2] is None for a in choices):
                                counts["completely cleaned by a repair then factoring"]+=1
                            if simplify_then_factor(u,edges) is not None:
                                counts["completely cleaned by bypass and factoring"]+=1
                        else:
                            counts["cleaned by factoring"]+=1
                if left>1:
                    gates.append((op,a,b));vs.append(val);off.append(low);marks.append(flag)
                    rec(left-1)
                    gates.pop();vs.pop();off.pop();marks.pop()
    rec(depth)
    counts["distinct live schedules after compaction"]=len(unique)
    return dict(counts)


if __name__=="__main__":
    print("single-gate rewrites on every small circuit",census(),flush=True)
    print("factoring control before and after",controls(),flush=True)
    print("matching repair before, after and alarm",graph_controls(),flush=True)
    print("matching splice before, after and reused wires",included_wire_control(),flush=True)
    print("fixed fork, upto four suffix gates",fork_census(),flush=True)
