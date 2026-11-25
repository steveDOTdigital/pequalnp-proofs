"""Exact synthesis on the maximal independent sets and their one-vertex extensions."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse,collections,runpy,subprocess

g=runpy.run_path(str(Path(__file__).with_name('six-vertex-and-count.py')))

class Formula:
    def __init__(self):
        self.clauses=[];self.n=0
    def var(self):
        self.n+=1
        return self.n
    def conjunction(self,a,b):
        z=self.var()
        self.clauses.extend(([-z,a],[-z,b],[z,-a,-b]))
        return z
    def disjunction(self,terms):
        z=self.var()
        self.clauses.append([-z,*terms])
        self.clauses.extend([z,-term] for term in terms)
        return z
    def dimacs(self):
        return 'p cnf {} {}\n'.format(self.n,len(self.clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in self.clauses)

def build(neg,pos,k):
    f=Formula();sides=[];values=[]
    rows=neg+pos
    for j in range(k):
        left=[f.var() for _ in range(6+j)];right=[f.var() for _ in range(6+j)]
        sides.append((left,right))
        vals=[]
        for ri,row in enumerate(rows):
            def side(sel):
                terms=[sel[v] for v in range(6) if row>>v&1]
                terms.extend(f.conjunction(sel[6+t],values[t][ri]) for t in range(j))
                return f.disjunction(terms)
            vals.append(f.conjunction(side(left),side(right)))
        values.append(vals)
    outputs=[f.var() for _ in range(k)]
    for ri,row in enumerate(rows):
        if ri<len(neg):
            for j in range(k):f.clauses.append([-outputs[j],-values[j][ri]])
        else:
            f.clauses.append([f.conjunction(outputs[j],values[j][ri]) for j in range(k)])
    return f,sides,outputs

def decode(row,sides,outputs):
    values=[bool(row>>i&1) for i in range(6)]
    for left,right in sides:
        values.append(any(values[i] for i in left) and any(values[i] for i in right))
    return any(values[6+j] for j in outputs)

def solve(gr,solver,seconds):
    neg,pos,bic,flat=g['data'](gr)
    # Positive controls fix every selector of an optimal ordinary cover.
    # This simultaneously tests the CNF and the decoder for each graph.
    witness=g['optimal_cover'](gr)
    assert len(witness)==bic and len(flat)==bic
    decoded=[([i for i in range(6) if a>>i&1],[i for i in range(6) if b>>i&1]) for a,b in witness]
    assert all(decode(row,decoded,range(bic)) == any((edges & row)==edges
               for j,edges in enumerate(g['PINS']) if gr>>j&1) for row in range(64))
    test,choices,outs=build(neg,pos,bic)
    for (selectors_l,selectors_r),(a,b) in zip(choices,witness):
        for selectors,raw in ((selectors_l,a),(selectors_r,b)):
            test.clauses.extend([signal if (raw>>i)&1 else -signal] for i,signal in enumerate(selectors))
    test.clauses.extend([signal] for signal in outs)
    control=subprocess.run([solver,'-q','--check'],input=test.dimacs(),text=True,capture_output=True,timeout=seconds+15)
    assert control.returncode==10,(gr,control.returncode,control.stderr[:300])
    if bic==0:
        assert gr==0 and not pos
        return 'EMPTY'
    f,select,outputs=build(neg,pos,bic-1)
    run=subprocess.run([solver,'-q','--check','--checkproof=2','-t',str(seconds)],
                       input=f.dimacs(),text=True,capture_output=True,timeout=seconds+15)
    if run.returncode==20:
        print(gr,bic,'UNSAT',flush=True)
        return 'UNSAT'
    if run.returncode==10:
        yes={int(x) for line in run.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
        sides=[([i for i,x in enumerate(a) if x in yes],[i for i,x in enumerate(b) if x in yes]) for a,b in select]
        out=[j for j,x in enumerate(outputs) if x in yes]
        assert all(not decode(r,sides,out) for r in neg)
        assert all(decode(r,sides,out) for r in pos)
        print(gr,bic,'WITNESS',sides,out,flush=True)
        return 'WITNESS'
    if run.returncode not in (0,124):
        raise RuntimeError((gr,run.returncode,run.stderr[:300]))
    print(gr,bic,'UNKNOWN',flush=True)
    return 'UNKNOWN'

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=20);a=p.parse_args()
    lean=Path(__file__).resolve().parent.parent/'lean'
    exe=Path(subprocess.check_output(['lean','--print-prefix'],cwd=lean,text=True).strip())/'bin/cadical'
    graphs=list(g['representatives']());graphs.sort(key=lambda gr:-g['data'](gr)[2])
    with ThreadPoolExecutor(max_workers=3) as pool:
        verdicts=list(pool.map(lambda gr:solve(gr,str(exe),a.seconds),graphs))
    result=collections.Counter(verdicts)
    print('verdicts',result,'verified positive controls',len(graphs))
    assert len(graphs)==156 and result=={'UNSAT':155,'EMPTY':1}
