"""Exact synthesis on the six intersection points of four lines in general position.

Free inputs are ORs of complementary pairs of points. In the full plane these
are the only nontrivial point ORs a completed line can leave on this core.
"""
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
import argparse
import runpy
import subprocess

root=Path(__file__).resolve().parent
common=runpy.run_path(str(root/'plane-three-line-cores.py'))
Formula=common['Formula']
pairs=list(combinations(range(4),2))
points=list(range(4,10))
flags=[(v,4+i) for i,edge in enumerate(pairs) for v in edge]
or_masks=tuple((1<<i)|(1<<(13-i)) for i in (4,5,6))
full=1023
truth=tuple(any(x>>u & x>>v & 1 for u,v in flags) for x in range(1024))

def bits(mask):
    while mask:
        one=mask & -mask
        yield one.bit_length()-1
        mask-=one

def subsets(mask):
    sub=mask
    while True:
        yield sub
        if not sub:break
        sub=(sub-1)&mask

def pop(mask):return bin(mask).count('1')

@lru_cache(None)
def profile(hi,lo,helpers):
    if truth[hi] or not truth[full^lo]:return None
    var=full & ~(hi|lo)
    alarms=sum(1<<v for v in bits(var) if truth[hi|(1<<v)])
    edges=tuple((a,b) for a,b in flags if ((1<<a)|(1<<b)) & (hi|lo|alarms)==0)
    used=alarms
    for a,b in edges:used|=(1<<a)|(1<<b)
    # Pin irrelevant raw inputs low before computing a lower bound.
    free=tuple(mask for j,mask in enumerate(or_masks) if helpers>>j&1 and mask&used==mask)
    must=0
    for v in bits(used):
        extra=next((m^(1<<v) for m in free if m>>v&1),0)
        # Saturate the one possible extra reader (the free OR). A change of
        # the target then proves the individual raw source must be read.
        if any(not truth[hi|extra|s] and truth[hi|extra|s|(1<<v)]
               for s in subsets(used & ~(extra|(1<<v)))):
            must|=1<<v
    return used,alarms,edges,free,must

def graph_cost(alarms,edges):
    vertices=0
    for a,b in edges:vertices|=(1<<a)|(1<<b)
    cover=min(pop(s) for s in subsets(vertices) if all((s>>a|s>>b)&1 for a,b in edges))
    # The point shore has degree at most two. Isolated alarm bits cost one
    # each over a nonempty graph; a disjunction alone costs one less.
    return len(edges)+cover+pop(alarms)-1

@lru_cache(None)
def bound(hi,lo,helpers):
    shape=profile(hi,lo,helpers)
    if shape is None:return 0
    used,alarms,edges,free,must=shape
    livehelpers=sum(1<<or_masks.index(m) for m in free)
    if not livehelpers:return graph_cost(alarms,edges)
    if livehelpers!=helpers or (used | hi | lo)!=full:
        return bound(hi,full & ~(hi|used),livehelpers)
    # Consider a circuit actually using all the available helpers, or one
    # omitting at least one. The raw changing-row certificates apply to both.
    best=max(1,pop(must)+len(free)-1)
    for v in bits(used):
        one=1<<v
        child=[]
        for high in (False,True):
            h,l=(hi|one,lo) if high else (hi,lo|one)
            value=bound(h,l,helpers)
            if profile(h,l,helpers) is None:
                child.append(None)
                continue
            lost=int(bool(must&one))+sum(bool(m&one) for m in free if high)
            best=max(best,value+lost)
            child.append(value)
        if (must&one) and None not in child:
            best=max(best,min(child)+2)
    omit=min(bound(hi,lo,helpers^(1<<j)) for j in bits(helpers))
    return min(best,omit)

def read_cap(f,variables,k):
    if k<0:
        f.clauses.append([])
        return
    if k>=len(variables):return
    if len(variables)<=9 or k<=1:
        f.clauses.extend([-x for x in ss] for ss in combinations(variables,k+1))
        return
    # A forward unary counter, sufficient for an upper bound.
    old=[]
    for x in variables:
        new=[f.var() for _ in range(min(k+1,len(old)+1))]
        f.clauses.append([-x,new[0]])
        for i,y in enumerate(old):
            f.clauses.append([-y,new[i]])
            if i+1<len(new):f.clauses.append([-y,-x,new[i+1]])
        old=new
    f.clauses.append([-old[k]])

def solve(mask,size,seconds):
    raw=[1<<i for i in range(10)]+[or_masks[j] for j in bits(mask)]
    width=len(raw)
    f=Formula()
    one=f.var();f.clauses.append([one])
    gates=[];reads=[]
    for j in range(size):
        op=f.var()
        a,b=f.selectors(width+j),f.selectors(width+j)
        r=[]
        for i in range(width+j):
            f.clauses.extend([-a[i],-t] for t in b[:i+1])
            z=f.var();r.append(z)
            f.clauses.extend(([-a[i],z],[-b[i],z],[-z,a[i],b[i]]))
        if gates:
            _,pa,pb=gates[-1]
            for i,previous in enumerate(pb):
                f.clauses.extend([-previous,-t] for t in b[:i])
            for i,previous in enumerate(pa):
                for k,prevb in enumerate(pb):
                    f.clauses.extend([-previous,-prevb,-b[k],-t] for t in a[:i])
        gates.append((op,a,b));reads.append(r)
    for i in range(width+size-1):
        f.clauses.append([r[i] for r in reads if i<len(r)])
    sym=[]
    for perm in permutations(range(4)):
        im=list(perm)+[4+pairs.index(tuple(sorted((perm[a],perm[b])))) for a,b in pairs]
        mapped=[sum(1<<im[k] for k in bits(z)) for z in raw]
        if set(raw)==set(mapped):sym.append([raw.index(z) for z in mapped])
    op,a,b=gates[0]
    for v,w in combinations(range(width),2):
        if any(tuple(sorted((im[v],im[w]),reverse=True))<(w,v) for im in sym):
            f.clauses.append([-a[v],-b[w]])
    values={}
    def row(x):
        if x not in values:
            ws=[one if m&x else -one for m in raw];ports=[]
            for op,a,b in gates:
                av,bv=f.port(a,ws),f.port(b,ws)
                val=f.gate(op,av,bv)
                ws.append(val);ports.append((av,bv,val))
            f.clauses.append([ws[-1] if truth[x] else -ws[-1]])
            values[x]=ports
        return values[x]
    yes=[(1<<a)|(1<<b) for a,b in flags]
    no=[x for x in range(1024) if not truth[x] and all(truth[x|1<<v] for v in bits(full^x))]
    for x in yes+no:row(x)
    # A direct raw reader paired with any other raw/helper has to preserve
    # every row distinction when no second reader of the raw input exists.
    for v in range(10):
        vr=1<<v
        for w,m in enumerate(raw):
            if w==v:continue
            seen=[False,False]
            for x in range(1024):
                if x&vr or truth[x]==truth[x|vr]:continue
                if any(bool(z&x)!=bool(z&(x|vr)) for k,z in enumerate(raw) if k!=v):continue
                seen[int(bool(x&m))]=True
            for j,(op,a,b) in enumerate(gates):
                other=[r[v] for k,r in enumerate(reads) if k!=j]
                for control,bad in enumerate(seen):
                    if bad:f.clauses.append([-reads[j][v],-reads[j][w],-op if control else op]+other)
    # Necessary cofactor budgets count every gate with both operands still
    # varying. A gate with a constant operand folds for free.
    checked=0
    for total in (1,2,3,4):
        for loc in combinations(range(10),total):
            pinned=sum(1<<v for v in loc)
            for hi in subsets(pinned):
                lo=pinned^hi
                lower=bound(hi,lo,mask)
                if lower<max(3,size-6):continue
                low,high=row(hi),row(full^lo)
                removed=[]
                for (a,b,_),(c,d,_) in zip(low,high):
                    kept=f.var()
                    f.clauses.extend(([-kept,-a],[-kept,-b],[-kept,c],[-kept,d],[kept,a,b,-c,-d]))
                    removed.append(-kept)
                read_cap(f,removed,size-lower)
                checked+=1
    print('Start',mask,size,'lower',bound(0,0,mask),'rows',len(values),'cubes',checked,
          'variables',f.count,'clauses',len(f.clauses),flush=True)
    solver=Path(subprocess.check_output(['lean','--print-prefix'],cwd=root.parent/'lean',text=True).strip())/'bin/cadical'
    try:
        res=subprocess.run([str(solver),'-q','--check','--checkproof=2','-t',str(seconds)],
                           input=f.text(),text=True,capture_output=True,timeout=seconds+18)
    except subprocess.TimeoutExpired:
        print('Wall-time limit',flush=True);return
    if res.returncode==20:
        assert 's UNSATISFIABLE' in res.stdout
        print('UNSAT',mask,size,flush=True);return
    if res.returncode!=10:
        print('No decision',res.returncode,flush=True);return
    model={int(x) for line in res.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
    net=[(op in model,next(i for i,z in enumerate(a) if z in model),
                       next(i for i,z in enumerate(b) if z in model)) for op,a,b in gates]
    for x,t in enumerate(truth):
        wires=[bool(m&x) for m in raw]
        for o,a,b in net:wires.append((wires[a] or wires[b]) if o else (wires[a] and wires[b]))
        assert wires[-1]==t
    print('SAT verified',mask,size,net,flush=True)

def geometry_controls():
    from collections import Counter
    lines=[{p for p in range(13) if (l-p)%13 in (0,1,3,9)} for l in range(13)]
    counts=Counter()
    for number in (4,5):
        for active in combinations(range(13),number):
            degree=[sum(p in lines[l] for l in active) for p in range(13)]
            multiple=tuple(sorted((d for d in degree if d>=3),reverse=True))
            if number==5 and multiple!=(4,):continue
            core={p for p,d in enumerate(degree) if d>=2}
            extra={tuple(sorted(core&line)) for i,line in enumerate(lines)
                   if i not in active and len(core&line)>1}
            counts[number,multiple]+=1
            if number==4 and not multiple:
                assert len(core)==6 and degree.count(1)==4 and len(extra)==3
                for a,b in extra:
                    assert all(not ({a,b}<=lines[l]) for l in active)
                assert set().union(*map(set,extra))==core
            elif number==4 and multiple==(3,):
                assert len(core)==4 and degree.count(1)==7 and not extra
                assert sorted(len(lines[l]&core) for l in active)==[2,2,2,3]
            elif number==4:
                assert multiple==(4,) and len(core)==1 and degree.count(1)==12
            else:
                assert len(core)==5 and degree.count(1)==8 and not extra
                assert sorted(len(lines[l]&core) for l in active)==[2,2,2,2,4]
    assert counts=={(4,()):234,(4,(3,)):468,(4,(4,)):13,(5,(4,)):117}
    # Four three-edge paths between two hubs. Cover by the left bipartite
    # shore: hub 0 and the four internal right-hand vertices, numbered 6..9.
    gates=[]
    def join(op,a,b):
        gates.append((op,a,b))
        return 9+len(gates)
    neighbor=join('or',join('or',2,3),join('or',4,5))
    stars=[join('and',0,neighbor)]
    for i in range(4):
        stars.append(join('and',6+i,join('or',2+i,1)))
    out=stars[0]
    for star in stars[1:]:out=join('or',out,star)
    assert len(gates)==16
    for x in range(1024):
        ws=[bool(x>>i&1) for i in range(10)]
        hit=any((ws[0] and ws[2+i]) or (ws[2+i] and ws[6+i]) or
                (ws[6+i] and ws[1]) for i in range(4))
        for op,a,b in gates:ws.append((ws[a] or ws[b]) if op=='or' else (ws[a] and ws[b]))
        assert ws[out]==hit
    print('Four and five line configurations',dict(counts),'theta upper control',len(gates),'gates, 1024 rows.')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--geometry',action='store_true')
    parser.add_argument('--helpers',type=int,default=3,choices=(0,1,2,3))
    parser.add_argument('--gates',type=int)
    parser.add_argument('--seconds',type=int,default=40)
    args=parser.parse_args()
    mask=(1<<args.helpers)-1
    if args.geometry:geometry_controls()
    elif args.gates is None:
        print('Core lower bound',bound(0,0,mask),flush=True)
    else:solve(mask,args.gates,args.seconds)
