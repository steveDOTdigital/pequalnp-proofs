"""Enumerate normalized minimum circuits for Petersen graph restrictions."""
from itertools import combinations
from pathlib import Path
import argparse
import runpy
import subprocess
import tempfile

here=Path(__file__).resolve().parent
graph=runpy.run_path(str(here/"petersen-deletion-check.py"))
edges=graph["edges"]
data=graph["shared"]["graph_data"]
elimination=graph["elimination"]
restrict=elimination["restrict"]

# Each improved bound has a separate check in the proof, in increasing size.
# Deleting the pendant vertex of the other eight-vertex graph leaves the theta.
reference=[([2,3,5,6,7,8],8),([1,2,5,6,7,8],8),([1,3,5,6,7,8],7),
           ([1,2,3,5,6,7,8],11),([1,2,3,4,5,7,8],9),
           ([0,1,2,3,4,5,7,8],13),([1,2,3,4,5,6,7,8],12)]


def signed_bound(vertices):
    active=sorted({i for edge in edges(vertices) for i in edge})
    result=elimination["lower"](data(active)[0])
    for labels,lb in reference:
        if len(labels)==len(active) and next(graph["bijections"](labels,active),None):
            result=max(result,lb)
    return result


def monotone_bound(vertices):
    # All cofactors occurring here have at most seven active vertices, or
    # are the two eight-vertex deletions solved before the nine-vertex run.
    e=edges(vertices)
    cover=next(k for k in range(len(vertices)+1) if any(
        all(a in c or b in c for a,b in e) for c in combinations(vertices,k)))
    return max(0,len(e)+cover-1)


def bounds(labels, signed):
    lower=signed_bound if signed else monotone_bound
    facts={}
    for v in labels:
        nb={b if a==v else a for a,b in edges(labels) if v in (a,b)}
        facts[v,0]=lower([x for x in labels if x!=v])
        rest=[x for x in labels if x!=v and x not in nb]
        cost=lower(rest)
        facts[v,1]=cost+len(nb) if cost else len(nb)-1
        if signed:
            table=data(labels)[0]
            for t in range(2):
                facts[v,t]=max(facts[v,t],elimination["lower"](restrict(table,labels.index(v),t)))
    return facts


def eligible(labels, signed, cost, table, facts, orbit=True):
    maps=list(graph["bijections"](labels,labels)) if orbit else []
    out=set()
    for i,j in combinations(range(len(labels)),2):
        a,b=labels[i],labels[j]
        if orbit and any(tuple(sorted((m[a],m[b]),reverse=True)) < (b,a) for m in maps): continue
        for op in range(4 if signed else 2):
            if not signed and op==0 and (a,b) not in edges(labels): continue
            p,q=(op & 1,op >> 1) if signed else (op,op)
            required=0
            for x,y,u,w in ((i,j,p,q),(j,i,q,p)):
                slice_y=restrict(table,y,w)
                bypass=restrict(slice_y,x-int(y<x),0)!=restrict(slice_y,x-int(y<x),1)
                for t in (0,1):
                    required=max(required,facts[labels[x],t]+1+int(bypass)+int(t==u))
            if required<=cost:out.add((op,i,j))
    return sorted(out)


def run(labels, costs, seconds, signed, first=None):
    n=len(labels)
    assert n in (6,7,8,9) and labels==sorted(set(labels))
    e=edges(labels)
    table=data(labels)[0]
    assert all(restrict(table,i,0)!=restrict(table,i,1) for i in range(n))
    facts=bounds(labels,signed)
    with tempfile.TemporaryDirectory(prefix="pnp-raw-prefix-") as tmp:
        exe=Path(tmp)/"search"
        subprocess.run(["clang++","-std=c++17","-O3","-DWIDTH="+str(n),"-DSIGNED_MODE="+str(int(signed)),
                        str(here/"petersen-raw-prefix.cpp"),"-o",str(exe)],check=True)
        for budget in costs:
            allowed=eligible(labels,signed,budget,table,facts)
            inp=[budget,seconds,len(e),*[(1<<labels.index(a))|(1<<labels.index(b)) for a,b in e],
                 *[facts[v,t] for v in labels for t in range(2)]]
            if signed and n==9:
                pairs=[]
                for a,b in combinations(labels,2):
                    lb=signed_bound([v for v in labels if v not in (a,b)])
                    if lb>=11: pairs.append((labels.index(a),labels.index(b),lb))
                assert len(pairs)==9
                for pair in pairs: inp.extend(pair)
            inp.append(len(allowed))
            for gate in allowed: inp.extend(gate)
            raw_pairs=eligible(labels,signed,budget,table,facts,orbit=False)
            inp.append(len(raw_pairs))
            for gate in raw_pairs: inp.extend(gate)
            if first is None:
                inp.append(0)
            else:
                assert first in allowed, "the seed must be a surviving orbit representative"
                inp.extend((1,*first))
            print("".join(map(str,labels)),budget,"signed" if signed else "monotone",
                  "first gates",len(allowed),"fixed",first,flush=True)
            res=subprocess.run([str(exe)],input=" ".join(map(str,inp))+"\n",capture_output=True,
                               text=True,timeout=seconds+35,check=True)
            print(res.stdout.strip(),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("labels");parser.add_argument("budgets")
    parser.add_argument("--seconds",type=int,default=120)
    parser.add_argument("--signed",action="store_true")
    parser.add_argument("--first",help="Operator and two local indices, comma separated")
    a=parser.parse_args()
    run(list(map(int,a.labels)),list(map(int,a.budgets.split(","))),a.seconds,a.signed,tuple(map(int,a.first.split(","))) if a.first else None)
