"""Small exact separator cases for the project's quadrangle promise.

The displayed core variables are the retained points followed by the three
unfinished lines. Every negative is a projection of a full quadrangle input.
"""
import argparse
from itertools import combinations, product
from pathlib import Path
import runpy
import subprocess

Formula = runpy.run_path(str(Path(__file__).with_name("plane-three-line-cores.py")))["Formula"]
LINES = [{(i+d) % 13 for d in (0,1,3,9)} for i in range(13)]
QUADS = [(set(q), {j for j,line in enumerate(LINES) if line.isdisjoint(q)})
         for q in combinations(range(13),4) if all(len(set(q)&line) <= 2 for line in LINES)]


def project(arms, points):
    negatives = {sum(1 << i for i,v in enumerate(points) if v in q) |
                 sum(1 << (len(points)+i) for i,v in enumerate(arms) if v in misses)
                 for q,misses in QUADS}
    maximal = tuple(sorted(x for x in negatives if not any(x != y and x & y == x for y in negatives)))
    positive = tuple(sorted((1 << i) | (1 << (len(points)+j))
                            for i,p in enumerate(points) for j,l in enumerate(arms) if p in LINES[l]))
    return positive,maximal


def profiles():
    groups = {}
    for arms in combinations(range(13),3):
        trio = [LINES[i] for i in arms]
        common = set.intersection(*trio)
        if common:
            c = next(iter(common))
            candidates = ([c,*reps] for reps in product(*(sorted(s-common) for s in trio)))
        else:
            candidates = [[next(iter(trio[a] & trio[b])) for a,b in ((0,2),(0,1),(1,2))]]
        for pts in candidates:
            key = project(arms,pts)
            groups[key] = groups.get(key,0)+1
    return groups


def control():
    gates = []

    def gate(op,a,b):
        output = 26+len(gates)
        assert a != b and max(a,b) < output
        gates.append((op,a,b))
        return output

    stars = []
    for l in range(13):
        point = gate("or",l,(l+1)%13)
        point = gate("or",point,(l+3)%13)
        point = gate("or",point,(l+9)%13)
        star = gate("and",13+l,point)
        if l == 0:
            star = gate("and",star,13+l)
            star = gate("and",star,point)
        stars.append(star)

    def merge(xs):
        head = xs[0]
        for nxt in xs[1:]:
            head = gate("or",head,nxt)
        return head

    a,b = merge(stars[:6]),merge(stars[6:])
    assert len(gates) == 65 and (a,b) == (84,90)
    marked = [i for i,(op,x,y) in enumerate(gates) if op == "and" and
              any(q>=26 and gates[q-26][0]=="and" for q in (x,y))]
    assert marked == [4,5]
    def values(P,L):
        ws = [i in P for i in range(13)] + [j in L for j in range(13)]
        for op,x,y in gates:
            ws.append(ws[x] and ws[y] if op=="and" else ws[x] or ws[y])
        return ws[a],ws[b]
    flags = [values({p},{l}) for l,line in enumerate(LINES) for p in line]
    assert all(any(pair) for pair in flags)
    assert (True,False) in flags and (False,True) in flags
    assert all(values(q,ls)==(False,False) for q,ls in QUADS)
    return flags.count((True,False)),flags.count((False,True))


def pencil_four():
    arms = [j for j,line in enumerate(LINES) if 0 in line]
    groups = [LINES[j]-{0} for j in arms]
    yes = tuple(sorted({(1 << v) | (1 << (5+i)) for i in range(4) for v in (0,1+i)}))
    no = {int(0 in q) | sum(1 << (1+i) for i,g in enumerate(groups) if g & q) |
          sum(1 << (5+i) for i,l in enumerate(arms) if l in ls) for q,ls in QUADS}
    return yes, tuple(sorted(x for x in no if not any(x != y and x & y == x for y in no)))


def affine_hits():
    """Three selected points off a line fail to extend precisely when collinear."""
    obstructed = 0
    for line, infinity in enumerate(LINES):
        for q in infinity:
            rows = [s-{q} for j,s in enumerate(LINES) if j != line and q in s]
            available = [quad for quad,misses in QUADS if line in misses]
            assert all(any(set(pair) <= quad for quad in available)
                       for a,b in combinations(rows,2) for pair in product(a,b))
            for choice in product(*rows):
                triple = set(choice)
                extendible = any(triple <= quad for quad in available)
                collinear = any(triple <= s for s in LINES)
                assert extendible != collinear
                obstructed += collinear
    assert obstructed == 468
    return obstructed


def synthesize(n, positives, negatives, size, seconds):
    # Equal operands allow padding any smaller circuit to the fixed budget.
    f = Formula()
    one = f.var()
    f.clauses.append([one])
    rows = positives + negatives
    tables = [[one if x & (1 << j) else -one for j in range(n)] for x in rows]
    gates = []
    for j in range(size):
        op = f.var()
        left, right = f.selectors(n+j), f.selectors(n+j)
        for a in range(n+j):
            f.clauses.extend([-left[a],-v] for v in right[:a])
        if gates:
            _,old_left,old_right = gates[-1]
            for b,was in enumerate(old_right):
                f.clauses.extend([-was,-v] for v in right[:b])
                for a,old in enumerate(old_left):
                    f.clauses.extend([-was,-right[b],-old,-v] for v in left[:a])
        gates.append((op,left,right))
        for table in tables:
            table.append(f.gate(op,f.port(left,table),f.port(right,table)))
    for i,table in enumerate(tables):
        f.clauses.append([table[-1] if i < len(positives) else -table[-1]])
    exe = Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())/"bin/cadical"
    result = subprocess.run([exe,"-q","--check","--checkproof=2","-t",str(seconds)],
                            input=f.text(),text=True,capture_output=True,timeout=seconds+15)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        return "UNSAT"
    if result.returncode == 0 and "UNKNOWN" in result.stdout:
        return "UNKNOWN"
    if result.returncode != 10 or "s SATISFIABLE" not in result.stdout:
        raise RuntimeError((result.returncode,result.stderr[-300:]))
    bits = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
            for v in line.split()[1:] if int(v)>0}
    def port(xs):
        return next(i for i,x in enumerate(xs) if x in bits)
    found = [(op in bits,port(a),port(b)) for op,a,b in gates]
    for i,row in enumerate(rows):
        values = [bool(row & (1 << j)) for j in range(n)]
        for op,a,b in found:
            values.append(values[a] or values[b] if op else values[a] and values[b])
        assert values[-1] == (i < len(positives))
    return ("SAT",found)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds",type=int,default=90)
    parser.add_argument("--four-pencil",action="store_true")
    parser.add_argument("--raw-profile",type=int,choices=[1,2],help="four-pencil representatives in one of the two raw geometries")
    parser.add_argument("--size",type=int,default=10)
    args = parser.parse_args()
    if args.four_pencil or args.raw_profile:
        yes,no = pencil_four()
        if args.raw_profile:
            no = [(15,23,27,90,120,150,180,210,270,300,330,390),
                  (7,11,13,19,21,25,120,180,210,300,330,390)][args.raw_profile-1]
        print("Four-line pencil",len(yes),"positives",len(no),"negative rows",flush=True)
        print(synthesize(9,yes,no,args.size,args.seconds),flush=True)
        raise SystemExit
    print('65-gate control, private flag counts',control(),flush=True)
    models = profiles()
    assert sorted(models.values()) == [234,468,936]
    print(f"{len(QUADS)} quadrangles, {affine_hits()} collinear obstructions in 1404 transversals",flush=True)
    for (yes,no),count in sorted(models.items(),key=lambda item:item[1]):
        n = max(yes+no).bit_length()
        unknown = [x for x in range(1 << n) if not any(x & e == e for e in yes)
                   and not any(x & z == x for z in no)]
        print(f"{count} frames, {n} inputs, unspecified rows {unknown}",flush=True)
        for size in (7,8):
            verdict = synthesize(n,yes,no,size,args.seconds)
            print(size,verdict,flush=True)
            assert verdict == "UNSAT" if size == 7 else isinstance(verdict,tuple)
