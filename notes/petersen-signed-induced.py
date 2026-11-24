"""Exact signed binary circuit checks for induced Petersen subgraphs.

The gate model is AND with an independent complement on each operand and on the
final output. Both signs of every intermediate wire are available for free.
"""
import argparse
from itertools import combinations
from pathlib import Path
import runpy
import subprocess

shared = runpy.run_path(str(Path(__file__).with_name("check-petersen-monotone.py")))
model = shared["elimination"]


def xor(cnf, a, b):
    out = cnf.variable()
    cnf.clauses.extend(([-a,-b,-out],[a,b,-out],[a,-b,out],[-a,b,out]))
    return out


def encode(table, count, labels, first_or=False, theta_cuts=False, known=False, seed=None):
    # Previously checked zero cofactors, indexed by the original raw label.
    facts = {}
    if known and labels == [1,2,3,5,6,7,8]:
        facts = {v:(7 if v in (2,8) else 8) for v in labels}
    if known and labels == [0,1,2,3,4,5,7,8]:
        facts = {v:(9 if v in (0,2,3,5) else 10) for v in labels}
    if known and labels == [1,2,3,4,5,7,8]:
        facts = {4:8}

    n = len(labels)
    cnf = shared["Clauses"]()
    gates = []
    for j in range(count):
        a = cnf.one(n+j)
        b = cnf.one(n+j)
        gates.append((a,b,cnf.variable(),cnf.variable()))
        for i,v in enumerate(a):
            cnf.clauses.extend([-v,-w] for w in b[:i+1])

    # Topologically order by the greater operand, then by the smaller operand.
    for (a,b,_,_),(c,d,_,_) in zip(gates[1:] if seed else gates,gates[2:] if seed else gates[1:]):
        for i,v in enumerate(b):
            cnf.clauses.extend([-v,-w] for w in d[:i])
            for j,u in enumerate(a):
                cnf.clauses.extend([-v,-d[i],-u,-w] for w in c[:j])

    for v in range(n+count-1):
        cnf.clauses.append([port[v] for a,b,_,_ in gates for port in (a,b) if v<len(port)])

    # A signed gate combining h(X,Y) and X can be replaced by a signed
    # gate of X,Y or a literal. Normalize these direct dependencies away.
    for j,(a,b,_,_) in enumerate(gates):
        for c,d,_,_ in gates[j+1:]:
            for i in range(n+j):
                for old in (a[i],b[i]):
                    cnf.clauses.extend(([-old,-c[n+j],-d[i]],[-old,-d[n+j],-c[i]]))

    forced_single = []
    for v in range(n):
        slices = [model["restrict"](table,v,t) for t in (0,1)]
        if not all(len(set(f))==2 for f in slices):
            continue
        caps = [count-model["lower"](f) for f in slices]
        if labels[v] in facts:
            caps[0] = min(caps[0],count-facts[labels[v]])
        if theta_cuts:
            assert labels == [1,2,3,5,6,7,8]
            caps[0] = count - (7 if labels[v] in (2,8) else 8)
        readers,forces = [],[[],[]]
        for a,b,neg_a,neg_b in gates:
            r=cnf.variable()
            readers.append(r)
            cnf.clauses.extend(([-a[v],r],[-b[v],r],[-r,a[v],b[v]]))
            # Setting v=t forces an AND whenever the signed literal is false.
            for t,f in enumerate(forces):
                z=cnf.variable()
                f.append(z)
                na=neg_a if t else -neg_a
                nb=neg_b if t else -neg_b
                cnf.clauses.extend(([-a[v],-na,z],[-b[v],-nb,z],[-z,r],
                                    [-z,-a[v],na],[-z,-b[v],nb]))
        cap=min(caps)
        if cap == 1:
            forced_single.append(v)
        if cap<0:
            cnf.clauses.append([])
            continue
        for subset in combinations(range(count),cap+1):
            cnf.clauses.append([-readers[j] for j in subset])
        for nread in range(1,min(cap,count)+1):
            for subset in combinations(range(count),nread):
                absent=[-readers[j] for j in subset]
                for t,limit in enumerate(caps):
                    required=limit-nread+1
                    if 1<=required<=min(2,nread):
                        for chosen in combinations(subset,required):
                            cnf.clauses.append(absent+[-forces[t][j] for j in chosen])

    if theta_cuts:
        # Every first gate is the signed NOR of the two poles once the
        # independently excluded smaller cofactors are applied.
        a,b,p,q = gates[0]
        cnf.clauses.extend(([a[labels.index(2)]],[b[labels.index(8)]],[p],[q]))
    if first_or:
        # Constrain the presence of the OR, not its index: a canonical
        # topological order may put a different ready gate first.
        l,r=sorted((labels.index(2),labels.index(8)))
        candidates=[]
        for a,b,neg_a,neg_b in gates:
            hit=cnf.variable()
            candidates.append(hit)
            cnf.clauses.extend([-hit,v] for v in [a[l],b[r],neg_a,neg_b])
        cnf.clauses.append(candidates)

    if seed:
        x,y,sa,sb = map(int,seed.split(","))
        l,r = labels.index(x),labels.index(y)
        assert l<r
        a,b,p,q = gates[0]
        cnf.clauses.extend(([a[l]],[b[r]],[p if sa else -p],[q if sb else -q]))

    # Any gate with two raw operands can be placed first. Check its four
    # slices using the controlling value on each of its signed input wires.
    for left,right in combinations(range(n),2):
        for lv in (0,1):
            for rv in (0,1):
                budget = 0
                for v,w,sv,sw in ((left,right,lv,rv),(right,left,rv,lv)):
                    section=model["restrict"](table,w,sw)
                    j=v-int(w<v)
                    bypass=int(model["restrict"](section,j,0)!=model["restrict"](section,j,1))
                    for t in (0,1):
                        sub=model["lower"](model["restrict"](table,v,t))
                        if not t: sub=max(sub,facts.get(labels[v],0))
                        budget=max(budget,sub+1+int(sv==t)+bypass)
                if budget>count:
                    for a,b,p,q in gates:
                        cnf.clauses.append([-a[left],-b[right],-p if lv else p,-q if rv else q])

    neg_output=cnf.variable()
    for row, expected in enumerate(table):
        wires=[cnf.variable() for _ in range(n)]
        cnf.clauses.extend([w if row>>i&1 else -w] for i,w in enumerate(wires))
        for a,b,neg_a,neg_b in gates:
            l=xor(cnf,cnf.select(a,wires),neg_a)
            r=xor(cnf,cnf.select(b,wires),neg_b)
            for v in forced_single:
                if table[row]!=table[row ^ (1<<v)]:
                    cnf.clauses.extend(([-a[v],r],[-b[v],l]))
            wires.append(cnf.conjunction(l,r))
        # The complemented output and the last gate value XOR to the target.
        last=wires[-1]
        if expected: cnf.clauses.extend(([neg_output,last],[-neg_output,-last]))
        else: cnf.clauses.extend(([-neg_output,last],[neg_output,-last]))
    return cnf,gates,neg_output


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("labels",help="Original vertex labels in increasing order")
    parser.add_argument("gates",type=int)
    parser.add_argument("--poles",action="store_true")
    parser.add_argument("--theta-cuts",action="store_true")
    parser.add_argument("--known-cofactors",action="store_true")
    parser.add_argument("--seed")
    parser.add_argument("--seconds",type=int,default=120)
    args=parser.parse_args()
    labels=[int(x) for x in args.labels]
    assert labels==sorted(set(labels))
    table,_,_=shared["graph_data"](labels)
    assert model["checks"]["support"](table,len(labels))==tuple(range(len(labels)))
    cnf,gates,final=encode(table,args.gates,labels,args.poles,args.theta_cuts,args.known_cofactors,args.seed)
    data=f"p cnf {cnf.variables} {len(cnf.clauses)}\n"+"".join(" ".join(map(str,c))+" 0\n" for c in cnf.clauses)
    lean=Path(__file__).resolve().parents[1]/"lean"
    prefix=Path(subprocess.check_output(["lean","--print-prefix"],cwd=lean,text=True).strip())
    print(labels,args.gates,cnf.variables,len(cnf.clauses),flush=True)
    out=subprocess.run([str(prefix/"bin/cadical"),"-q","--check","--checkproof=2","-t",str(args.seconds)],
                       input=data,text=True,capture_output=True,timeout=args.seconds+25)
    if out.returncode==20:
        assert "s UNSATISFIABLE" in out.stdout
        print("UNSAT",flush=True)
    elif out.returncode==10:
        true={int(x) for l in out.stdout.splitlines() if l.startswith("v ") for x in l.split()[1:] if int(x)>0}
        def pick(port):
            return next(j for j,p in enumerate(port) if p in true)
        circ=[(pick(a),pick(b),p in true,q in true) for a,b,p,q in gates]
        for row,value in enumerate(table):
            wires=[bool(row>>i&1) for i in range(len(labels))]
            for a,b,p,q in circ:
                wires.append((wires[a]^p) and (wires[b]^q))
            assert (wires[-1]^(final in true))==value
        print("SAT",circ,"output complemented",final in true,flush=True)
    elif out.returncode==0:print("TIMEOUT",flush=True)
    else:raise RuntimeError(out.stderr[-1500:])


if __name__=="__main__":
    main()
