"""Check cyclic terminal graphs after pendant-tree elimination.

The small-circuit backend admits complemented operands and complemented output
for free. All bounds it proves also apply to ordinary binary AND/OR/NOT lists.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import argparse
import runpy
import subprocess

root = Path(__file__).resolve().parent
old = runpy.run_path(str(root / 'edge-owner-exchange.py'))
canonical, cover, induced, forest = (old[k] for k in ('canonical','cover','induced','forest'))
bits, pop, upper = old['bits'], old['count'], old['upper']
signed = runpy.run_path(str(root / 'petersen-signed-induced.py'))
certified = {}

def make(n,edges):
    masks = [0]*n
    for v,w in edges:
        masks[v] |= 1<<w
        masks[w] |= 1<<v
    return canonical(tuple(masks))

def peelable(g):
    for l,ns in enumerate(g):
        if pop(ns) != 1: continue
        p = next(bits(ns))
        if pop(g[p]) <= 2 or any(z != l and g[z] == ns for z in bits(g[p])):
            return True
    return False

def kernels(k):
    """Every outside vertex is identified by its nonempty subset of the cover."""
    seen, inside_seen = set(),set()
    cpairs=list(combinations(range(k),2))
    for pattern in range(1<<len(cpairs)):
        inside=make(k,[p for j,p in enumerate(cpairs) if pattern>>j&1])
        if inside in inside_seen:continue
        inside_seen.add(inside)
        if any(pop(inside[x]&inside[y])>1 for x,y in cpairs):continue
        choices=[s for s in range(1,1<<k) if all(not inside[x]&inside[y] for x,y in combinations(bits(s),2))]
        def visit(j, rows):
            if j < len(choices):
                visit(j+1, rows)
                s=choices[j]
                if all(pop(s&t)<=1 for t in rows):
                    visit(j+1, rows+[s])
                return
            g=tuple(inside[x] | sum(1<<(k+i) for i,r in enumerate(rows) if r>>x&1)
                    for x in range(k)) + tuple(rows)
            if not all(g) or peelable(g):return
            g=canonical(g)
            if g in seen or cover(g)!=k:return
            assert all(pop(g[x]&g[y])<=1 for x,y in combinations(range(len(g)),2))
            seen.add(g)
        visit(0,[])
    return seen

def unary_value(g,v,value):
    full=(1<<len(g))-1
    if not value: return lower(induced(g,full^(1<<v)))
    smaller=induced(g, full & ~(g[v] | (1<<v)))
    return lower(smaller)+pop(g[v])-(not smaller)

def survives(g,v,w,pin):
    # After fixing w, does v still affect the cofactor?
    if not pin:return bool(g[v] & ~(1<<w))
    if g[w]>>v&1:return True
    return bool(g[v] & ~(g[w] | (1<<w)))

@lru_cache(maxsize=None)
def lower(g):
    if g in certified:return certified[g]
    if not g:return 0
    if forest(g):return upper(g)
    n=len(g)
    co=[[unary_value(g,v,b) for b in (0,1)] for v in range(n)]
    # Consider the first signed AND in a smallest circuit. Its controlling
    # input values are a and b. Essentiality on the partner's controlling
    # slice forces an additional reader. See petersen-gate-elimination.py.
    by_pair=[]
    for v,w in combinations(range(n),2):
        for a,b in product((0,1),repeat=2):
            bv,bw=survives(g,v,w,b),survives(g,w,v,a)
            by_pair.append(max(co[v][t]+1+(a==t)+bv for t in (0,1)))
            by_pair[-1]=max(by_pair[-1],*(co[w][t]+1+(b==t)+bw for t in (0,1)))
    result=max(n-1,min(by_pair))
    assert result<=upper(g),(g,result,upper(g))
    return result

def check_sat(g,size,seconds):
    n=len(g)
    table=tuple(any(g[v]&r for v in bits(r)) for r in range(1<<n))
    cnf,gates,flip=signed['encode'](table,size,list(range(n)))
    prefix=Path(subprocess.check_output(['lean','--print-prefix'],cwd=root.parent/'lean',text=True).strip())
    data=f'p cnf {cnf.variables} {len(cnf.clauses)}\n'+''.join(
        ' '.join(map(str,c))+' 0\n' for c in cnf.clauses)
    result=subprocess.run([str(prefix/'bin/cadical'),'-q','--check','--checkproof=2','-t',str(seconds)],
                          input=data,text=True,capture_output=True,timeout=seconds+15)
    if result.returncode==20:
        assert 's UNSATISFIABLE' in result.stdout
        return True
    if result.returncode==10:
        model={int(x) for line in result.stdout.splitlines() if line.startswith('v ')
               for x in line.split()[1:] if int(x)>0}
        gates=[(next(i for i,z in enumerate(a) if z in model),next(i for i,z in enumerate(b) if z in model),
                p in model,q in model) for a,b,p,q in gates]
        for r,expected in enumerate(table):
            wires=[bool(r>>i&1) for i in range(n)]
            for a,b,p,q in gates:wires.append((wires[a]^p) and (wires[b]^q))
            assert (wires[-1]^(flip in model))==expected
        print('Signed witness',g,gates,flip in model,flush=True)
    else:
        assert result.returncode==0, result.stderr
        print('Solver time limit',g,size,flush=True)
    return False

def monotone_costs(g):
    full=(1<<len(g))-1
    result=[]
    for v,near in enumerate(g):
        off=induced(g,full^(1<<v))
        on=induced(g,full & ~(near | (1<<v)))
        result.append((mono_lower(off), mono_lower(on)+pop(near)-(not on)))
    return result

def profiles(s,costs):
    return [[(d,a) for d in range(1,min(s-lo,s-hi)+1) for a in range(d+1)
             if d+min(a,2)<=s-lo and d+min(d-a,2)<=s-hi] for lo,hi in costs]

def raw_pair_possible(g,opts):
    for v,w in combinations(range(len(g)),2):
        for is_and in (False,True):
            def allowed(x,y):
                # A solely read x must be inessential when y controls the first gate.
                return any((a if is_and else d-a)>0 and
                           (d>1 or not survives(g,x,y,not is_and)) for d,a in opts[x])
            if allowed(v,w) and allowed(w,v):return True
    return False

mono_cert={}
verified_cover=0
@lru_cache(maxsize=None)
def mono_lower(g):
    if not g:return 0
    if g in mono_cert:return mono_cert[g]
    if verified_cover and cover(g)<=verified_cover:return upper(g)
    if forest(g):return upper(g)
    costs=monotone_costs(g)
    bound=max(lower(g),max(min(lo,hi)+2 for lo,hi in costs))
    for v,(lo,hi) in enumerate(costs):
        keep=(1<<len(g))-1
        off=induced(g, keep^(1<<v))
        on=induced(g, keep & ~(g[v] | (1<<v)))
        bound=max(bound,lo+len(g)-len(off),hi+len(g)-len(on)-pop(g[v]))
    target=upper(g)
    while bound<target:
        opts=profiles(bound,costs)
        if all(opts) and raw_pair_possible(g,opts):break
        bound+=1
    assert bound<=target
    return bound

def mono_sat(g,s,seconds):
    n=len(g)
    table=tuple(any(g[v]&r for v in bits(r)) for r in range(1<<n))
    yes=[(1<<v)|(1<<w) for v in range(n) for w in bits(g[v]) if v<w]
    no=[r for r,value in enumerate(table) if not value and
        all(table[r|(1<<v)] for v in range(n) if not r>>v&1)]
    cnf,gates=signed['shared']['encode'](n,s,table,yes,no)
    for v,(lo,hi) in enumerate(monotone_costs(g)):
        reads=[]
        for left,right,_ in gates:
            r=cnf.variable()
            cnf.clauses.extend(([-left[v],r],[-right[v],r],[-r,left[v],right[v]]))
            reads.append(r)
        for subset in combinations(range(s),min(s-lo,s-hi)+1):
            cnf.clauses.append([-reads[j] for j in subset])
        for d in range(1,min(s-lo,s-hi)+1):
            for subset in combinations(range(s),d):
                for pin,cap in ((0,s-lo),(1,s-hi)):
                    need=cap-d+1
                    if 1<=need<=min(2,d):
                        for forced in combinations(subset,need):
                            cnf.clauses.append([-reads[j] for j in subset]+[
                                -gates[j][2] if pin else gates[j][2] for j in forced])
    solver=Path(subprocess.check_output(['lean','--print-prefix'],cwd=root.parent/'lean',text=True).strip())/'bin/cadical'
    data=f'p cnf {cnf.variables} {len(cnf.clauses)}\n'+''.join(
        ' '.join(map(str,c))+' 0\n' for c in cnf.clauses)
    res=subprocess.run([str(solver),'-q','--check','--checkproof=2','-t',str(seconds)],
                       input=data,text=True,capture_output=True,timeout=seconds+15)
    if res.returncode==20:
        assert 's UNSATISFIABLE' in res.stdout
        return True
    if res.returncode==10:
        model={int(x) for l in res.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x)>0}
        program=[(next(i for i,z in enumerate(a) if z in model),next(i for i,z in enumerate(b) if z in model),
                  op in model) for a,b,op in gates]
        for r,value in enumerate(table):
            wires=[bool(r>>v&1) for v in range(n)]
            for a,b,is_or in program:wires.append((wires[a] or wires[b]) if is_or else (wires[a] and wires[b]))
            assert wires[-1]==value
        print('Monotone witness',g,program,flush=True)
    else:assert res.returncode==0,res.stderr
    return False

def run_mono(kmax,seconds):
    global verified_cover
    for k in range(1,kmax+1):
        cases=sorted(kernels(k),key=lambda g:(len(g),upper(g),g))
        done=0
        for g in cases:
            lo,hi=mono_lower(g),upper(g)
            if seconds:
                while lo<hi and mono_sat(g,lo,seconds):
                    print('Monotone exclusion',g,lo,flush=True)
                    lo+=1
            if lo==hi:done+=1
            else:print('Open monotone bound',g,lo,hi,flush=True)
            if lo>mono_lower(g):
                mono_cert[g]=lo
                mono_lower.cache_clear()
        if done==len(cases) and verified_cover==k-1:
            verified_cover=k
            mono_lower.cache_clear()
        print('Monotone cover',k,'terminal graphs',len(cases),'sharp bounds',done,flush=True)

def run(kmax,seconds):
    for k in range(1,kmax+1):
        cases=sorted(kernels(k),key=lambda g:(len(g),upper(g),g))
        solved=0
        for g in cases:
            lo,hi=lower(g),upper(g)
            if seconds:
                while lo<hi and check_sat(g,lo,seconds):
                    print('Checked exclusion',g,lo,flush=True)
                    lo+=1
            if lo==hi:
                solved+=1
                if lo>lower(g):
                    certified[g]=lo
                    lower.cache_clear()
            else:print('Open signed bound',g,lo,hi,flush=True)
        print('Cover',k,'terminal graphs',len(cases),'sharp bounds',solved,flush=True)

def triangle_controls():
    for k in range(4):
        g=make(3+k,[(0,1),(0,2),(1,2)]+[(i,3+i) for i in range(k)])
        lo=lower(g)
        for s in range(lo,upper(g)):
            assert check_sat(g,s,45),(k,s)
        print('Triangle with',k,'pendants: signed size',upper(g),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cover',type=int,default=3)
    parser.add_argument('--seconds',type=int,default=0)
    parser.add_argument('--mono',action='store_true')
    parser.add_argument('--triangle',action='store_true')
    parser.add_argument('--four-summary',action='store_true')
    args=parser.parse_args()
    if args.triangle:
        triangle_controls()
    elif args.four_summary:
        run_mono(3,30)
        assert verified_cover==3
        print('Cover four unresolved deficits',sorted(Counter(upper(g)-mono_lower(g) for g in kernels(4)).items()))
    else:
        (run_mono if args.mono else run)(args.cover,args.seconds)
