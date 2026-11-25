"""Exact monotone checks for cycles with distinct pendant leaves.

Each candidate is a globally minimum circuit. Pinning inputs gives a smaller
graph and free OR literals. Its proved size constrains the number of surviving
live binary gates. Run from any directory with the proof repository available.
"""
from itertools import combinations
from pathlib import Path
import argparse
import runpy
import subprocess

root=Path(__file__).resolve().parent
base=runpy.run_path(str(root/'cyclic-core-peeling.py'))
bits,pop,canonical=base['bits'],base['pop'],base['canonical']
upper,induced=base['upper'],base['induced']
solver=Path(subprocess.check_output(['lean','--print-prefix'],cwd=root.parent/'lean',text=True).strip())/'bin/cadical'

def ring(n,mask):
    g=[0]*(n+pop(mask))
    def edge(a,b):
        g[a]|=1<<b
        g[b]|=1<<a
    for i in range(n):edge(i,(i+1)%n)
    for j,i in enumerate(bits(mask)):edge(i,n+j)
    return tuple(g)

def table(g):
    return tuple(any(g[i]&r for i in bits(r)) for r in range(1<<len(g)))

class Search:
    def __init__(self,g,size,n,mask):
        self.g=g
        self.n=len(g)
        self.size=size
        self.full=(1<<self.n)-1
        self.truth=table(g)
        yes=[(1<<v)|(1<<w) for v in range(self.n) for w in bits(g[v]) if v<w]
        no=[r for r,t in enumerate(self.truth) if not t and
            all(self.truth[r|(1<<v)] for v in bits(self.full^r))]
        self.cnf,self.gates=base['signed']['shared']['encode'](self.n,size,self.truth,yes,no)
        self.one=self.cnf.variable()
        self.cnf.clauses.append([self.one])
        self.rows={}
        self.pin_count=0
        self.actual_reads=[]
        for j in range(size):
            a,b,op=self.gates[j]
            row=[]
            for i in range(self.n+j):
                r=self.cnf.variable()
                self.cnf.clauses.extend(([-a[i],r],[-b[i],r],[-r,a[i],b[i]]))
                row.append(r)
            self.actual_reads.append(row)
        self.normalize_first(n,mask)
        self.raw_profiles()
    def normalize_first(self,n,mask):
        leaves={i:n+j for j,i in enumerate(bits(mask))}
        autos=[]
        for d in (-1,1):
            for k in range(n):
                g=[(d*i+k)%n for i in range(n)]
                if {g[i] for i in leaves}!=set(leaves):continue
                im=g+[leaves[g[i]] for i in leaves]
                assert all({im[w] for w in bits(self.g[v])}==set(bits(self.g[im[v]])) for v in range(self.n))
                autos.append(im)
        a,b,_=self.gates[0]
        for v,w in combinations(range(self.n),2):
            if any(tuple(sorted((im[v],im[w]),reverse=True))<(w,v) for im in autos):
                self.cnf.clauses.append([-a[v],-b[w]])
    def raw_profiles(self):
        for v,near in enumerate(self.g):
            small=self.full^(1<<v)
            low=base['mono_lower'](induced(self.g,small))
            rest=induced(self.g,small & ~near)
            high=base['mono_lower'](rest)+pop(near)-(not rest)
            reads=[row[v] for row in self.actual_reads]
            max_reads=min(self.size-low,self.size-high)
            for chosen in combinations(reads,max_reads+1):
                self.cnf.clauses.append([-r for r in chosen])
            for d in range(1,max_reads+1):
                for chosen in combinations(range(self.size),d):
                    for pin,cap in ((0,self.size-low),(1,self.size-high)):
                        want=cap-d+1
                        if not 1<=want<=min(d,2):continue
                        for controls in combinations(chosen,want):
                            self.cnf.clauses.append([-reads[j] for j in chosen]+[
                                -self.gates[j][2] if pin else self.gates[j][2] for j in controls])
            # A private neighbor lets a safe sibling be moved to the output.
            if any(self.g[w]==1<<v for w in bits(near)):
                for j,(_,_,is_or) in enumerate(self.gates):
                    self.cnf.clauses.append([-reads[j],-is_or]+[r for k,r in enumerate(reads) if k!=j])
    def both(self,a,b):
        if a==self.one:return b
        if b==self.one or a==b:return a
        if a==-self.one or b==-self.one or a==-b:return -self.one
        return self.cnf.conjunction(a,b)
    def evaluate(self,r):
        if r in self.rows:return self.rows[r]
        wires=[self.one if r>>v&1 else -self.one for v in range(self.n)]
        ports=[]
        for a,b,op in self.gates:
            av=self.cnf.select(a,wires)
            bv=self.cnf.select(b,wires)
            y=self.cnf.variable()
            self.cnf.clauses.extend(([op,-y,av],[op,-y,bv],[op,y,-av,-bv],
                                     [-op,y,-av],[-op,y,-bv],[-op,-y,av,bv]))
            wires.append(y)
            ports.append((av,bv,y))
        self.cnf.clauses.append([wires[-1] if self.truth[r] else -wires[-1]])
        self.rows[r]=ports
        return ports
    def at_most(self,variables,k):
        # A forward cardinality counter is enough to forbid k+1 selections.
        if k<0:self.cnf.clauses.append([]);return
        if k>=len(variables):return
        before=[self.one]+[-self.one]*(k+1)
        for x in variables:
            after=[self.one]+[self.cnf.variable() for j in range(k+1)]
            for j in range(1,k+2):
                self.cnf.clauses.extend(([-before[j],after[j]],[-before[j-1],-x,after[j]]))
            before=after
        self.cnf.clauses.append([-before[-1]])
    def pin(self,high,low):
        assert not high&low
        if self.truth[high]:return
        alarms=0
        for v in bits(high):alarms|=self.g[v]
        alarms &= self.full & ~(high|low)
        pool=self.full & ~(high|low|alarms)
        active=sum(1<<v for v in bits(pool) if self.g[v]&pool)
        core=induced(self.g,active)
        bound=base['mono_lower'](core)+pop(alarms)-(not core)
        if bound<=0 or self.size-bound>6:return
        top=high|active|alarms
        if (high,top) in self.tested:return
        self.tested.add((high,top));self.pin_count+=1
        lo,hi=self.evaluate(high),self.evaluate(top)
        keep=[self.both(self.both(-a,c),self.both(-b,d)) for (a,b,_),(c,d,_) in zip(lo,hi)]
        var=[self.both(-a[2],b[2]) for a,b in zip(lo,hi)]
        # Dead intermediate gates cost nothing in the restricted circuit.
        live=[-self.one]*self.size
        for j in reversed(range(self.size)):
            if j==self.size-1:live[j]=self.one
            else:
                uses=[self.both(live[k],self.actual_reads[k][self.n+j]) for k in range(j+1,self.size)]
                y=self.cnf.variable()
                self.cnf.clauses.append([-y]+uses)
                self.cnf.clauses.extend([[-t,y] for t in uses])
                live[j]=self.both(y,var[j])
        kept=[self.both(a,b) for a,b in zip(keep,live)]
        self.at_most([-k for k in kept],self.size-bound)
    def solve(self,seconds):
        self.tested=set()
        for v in range(self.n):
            self.pin(0,1<<v)
            self.pin(1<<v,0)
        for a,b in combinations(range(self.n),2):
            x,y=1<<a,1<<b
            for hi,lo in [(0,x|y),(x,y),(y,x),(x|y,0)]:
                self.pin(hi,lo)
        data=f'p cnf {self.cnf.variables} {len(self.cnf.clauses)}\n'+''.join(
            ' '.join(map(str,c))+' 0\n' for c in self.cnf.clauses)
        try:
            r=subprocess.run([str(solver),'-q','--check','--checkproof=2','-t',str(seconds)],
                             input=data,text=True,capture_output=True,timeout=seconds+20)
        except subprocess.TimeoutExpired:
            print('Solver wall-time limit. Keeping the last proved bound.',flush=True)
            return False
        if r.returncode==20:
            assert 's UNSATISFIABLE' in r.stdout
            return True
        if r.returncode==10:
            model={int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:] if int(x)>0}
            gates=[(next(i for i,z in enumerate(a) if z in model),next(i for i,z in enumerate(b) if z in model),
                    op in model) for a,b,op in self.gates]
            for row,value in enumerate(self.truth):
                ws=[bool(row>>i&1) for i in range(self.n)]
                for a,b,is_or in gates:ws.append((ws[a] or ws[b]) if is_or else (ws[a] and ws[b]))
                assert ws[-1]==value
            print('Monotone witness',gates,flush=True)
        else:assert r.returncode==0,r.stderr
        return False

def check(n,seconds):
    seen=set()
    solved=0
    for mask in sorted(range(1<<n),key=lambda x:(pop(x),x)):
        if mask in seen:continue
        seen.update(sum((mask>>((d*i+k)%n)&1)<<i for i in range(n)) for d in (-1,1) for k in range(n))
        g=ring(n,mask);key=canonical(g)
        lo,hi=base['mono_lower'](key),upper(key)
        while lo<hi:
            test=Search(g,lo,n,mask)
            if not test.solve(seconds):break
            print('Monotone exclusion',n,mask,lo,'restriction cubes',test.pin_count,flush=True)
            lo+=1
        if lo>base['mono_lower'](key):
            base['mono_cert'][key]=lo
            base['mono_lower'].cache_clear()
        solved+=int(lo==hi)
        print('Cycle',n,'pendants',mask,'lower',lo,'upper',hi,flush=True)
    print('Cycle length',n,'resolved',solved,flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cycle',type=int)
    parser.add_argument('--seconds',type=int,default=30)
    args=parser.parse_args()
    assert args.cycle>=3 and args.cycle!=4
    check(args.cycle,args.seconds)
