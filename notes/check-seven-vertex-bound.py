"""Check the seven-vertex edge-plus-cover bound using six-vertex restrictions."""

import argparse
import tempfile
from contextlib import ExitStack
from itertools import combinations, permutations
from pathlib import Path
from runpy import run_path
from subprocess import run

notes = Path(__file__).parent
representatives = run_path(str(notes / "check-small-cover-bound.py"))["representatives"]
Formula = run_path(str(notes / "search-three-matchings.py"))["Formula"]
N = 7
ALL = (1 << N) - 1


class Graph:
    def __init__(self, edges):
        self.edges = [(1 << a) | (1 << b) for a, b in edges]
        self.size = self.estimate(0, 0)
        self.pins = {(i, v): self.estimate((1-v) << i, v << i)
                     for i in range(N) for v in (0, 1)}
        self.positive = self.edges
        independent = {x for x in range(1 << N) if not self.value(x)}
        self.negative = sorted(x for x in independent if all(
            (x | (1 << j)) not in independent for j in range(N) if not x & (1 << j)))
        edge_set = set(edges)
        self.autos = [p for p in permutations(range(N)) if all(
            tuple(sorted((p[a], p[b]))) in edge_set for a, b in edges)]

    def value(self, x):
        return any(x & e == e for e in self.edges)

    def estimate(self, off, on):
        # In the unpinned case this is the target. After one pin the residual
        # graph has at most six vertices and the published bound applies.
        singles = 0
        for e in self.edges:
            if not e & off and e & on:
                singles |= e & ~on
        rest = [e for e in self.edges if not e & (singles | on | off)]
        cover = min(bin(x).count("1") for x in range(1 << N) if all(e & x for e in rest))
        return max(0, len(rest) + cover + bin(singles).count("1") - 1)

    def boundary(self, bit, val):
        masks = [x for x in range(1 << N) if ((x >> bit) & 1) == val]
        free = [1 << j for j in range(N) if j != bit]
        return [x for x in masks if
                (self.value(x) and not any(self.value(x ^ u) for u in free if x & u)) or
                (not self.value(x) and all(self.value(x | u) for u in free if not x & u))]

    def first_choices(self, budget):
        ans = set()
        for a, b in combinations(range(N), 2):
            if any((max(p[a],p[b]),min(p[a],p[b])) < (b,a) for p in self.autos):
                continue
            for is_or in (False, True):
                if not is_or and ((1 << a) | (1 << b)) not in self.edges:
                    continue
                allowed = True
                for x, y in ((a,b),(b,a)):
                    # With y at the controlling value, the first gate cannot
                    # transmit x. A changing output forces a second reader.
                    second = any(self.value(z) != self.value(z ^ (1 << x)) for z in range(1 << N)
                                 if bool(z & (1 << y)) == is_or)
                    for val in (0,1):
                        loss = 1 + int(second) + int(val == is_or)
                        if self.pins[x,val] + loss > budget:
                            allowed = False
                if allowed:
                    ans.add((is_or,a,b))
        return ans


def search(graph, budget, solver, seconds, first=None):
    possible = graph.first_choices(budget)
    if first is not None:
        possible &= {first}
    if not possible:
        return "UNSAT"
    f = Formula()
    # The min and max rows of every pinned subcube detect all constant
    # restricted signals by monotonicity.
    boundary = {p: graph.boundary(*p) for p in graph.pins}
    rows = sorted(set([x for test in boundary.values() for x in test] + graph.positive + graph.negative +
                      [0, ALL] + [1 << i for i in range(N)] + [ALL ^ (1 << i) for i in range(N)]))
    index = {x:i for i,x in enumerate(rows)}
    pos, neg = ([index[x] for x in cases] for cases in (graph.positive,graph.negative))
    tables = []
    for j in range(N):
        table = f.vars(len(rows))
        f.clauses.extend([v if x & (1 << j) else -v] for x,v in zip(rows,table))
        tables.append(table)

    def witness(u, v):
        # The caller asks whether some row has u true and v false.
        d = f.vars(1)[0]
        f.clauses.extend(([-d,u],[-d,-v]))
        return d

    choices = []
    survivors = {pin: [] for pin in graph.pins}
    for j in range(budget):
        selectors, ports = [], []
        for _ in range(2):
            sel = f.one_of(len(tables))
            port = f.vars(len(rows))
            for pick, table in zip(sel,tables):
                for a,b in zip(port,table):
                    f.clauses.extend(([-pick,-a,b],[-pick,a,-b]))
            selectors.append(sel)
            ports.append(port)
        left,right = selectors
        for b,rb in enumerate(right):
            for la in left[b:]:
                f.clauses.append([-rb,-la])
        is_or = f.vars(1)[0]
        if j == 0:
            for a,b in combinations(range(N),2):
                for op in (False,True):
                    if (op,a,b) not in possible:
                        f.clauses.append([-left[a],-right[b],-is_or if op else is_or])
        if choices:
            _, prev_left, prev_right = choices[-1]
            same = f.vars(1)[0]
            for b,prev in enumerate(prev_right):
                f.clauses.extend([-prev,-v] for v in right[:b])
                f.clauses.append([-prev,-right[b],same])
            for a,prev in enumerate(prev_left):
                f.clauses.extend([-same,-prev,-v] for v in left[:a])
        out = f.vars(len(rows))
        for a,b,y in zip(*ports,out):
            f.clauses.extend(([is_or,-y,a],[is_or,-y,b],[is_or,y,-a,-b],
                              [-is_or,y,-a],[-is_or,y,-b],[-is_or,-y,a,b]))
        # In a smallest circuit no earlier wire is at least as correct on
        # every boundary input. Replacing a dominated gate preserves all
        # positive/negative answers by monotonicity of the suffix.
        f.clauses.append([out[r] for r in pos])
        f.clauses.append([-out[r] for r in neg])
        # If an earlier value dominates on a restricted boundary it can
        # replace this gate. All such replacements may be made simultaneously:
        # each rewritten wire is at least as good on positives and negatives
        # by induction through monotone gates.
        differences = []
        for h, other in enumerate(tables):
            delta = {}
            for r,x in enumerate(rows):
                truth = graph.value(x)
                if h < N:
                    if bool(x & (1 << h)) != truth:
                        delta[r] = out[r] if truth else -out[r]
                else:
                    delta[r] = witness(out[r],other[r]) if truth else witness(other[r],out[r])
            differences.append(delta)
            f.clauses.append([delta[r] for r in pos + neg if r in delta])
        for pin in graph.pins:
            i,val = pin
            lo = index[val << i]
            hi = index[ALL ^ ((1-val) << i)]
            live = f.vars(1)[0]
            survivors[pin].append(live)
            test = [index[x] for x in boundary[pin]]
            for delta in differences:
                f.clauses.append([-live,*[delta[r] for r in test if r in delta]])
            f.clauses.append([-live,*[out[index[x]] for x in boundary[pin] if graph.value(x)]])
            f.clauses.append([-live,*[-out[index[x]] for x in boundary[pin] if not graph.value(x)]])
            for port in ports:
                f.clauses.extend(([-live,-port[lo]],[-live,port[hi]]))
            f.clauses.extend(([-live,-left[i]],[-live,-right[i]]))
        tables.append(out)
        choices.append((is_or,left,right))
    for pin, group in survivors.items():
        for subset in combinations(group,budget-graph.pins[pin]+1):
            f.clauses.append(list(subset))
    for j in range(budget-1):
        wire = N+j
        f.clauses.append([sel[wire] for _,left,right in choices[j+1:] for sel in (left,right)])
    f.clauses.extend([tables[-1][r]] for r in pos)
    f.clauses.extend([-tables[-1][r]] for r in neg)
    result = run([solver,"-q","--check","--checkproof=2","-t",str(seconds)],
                 input=f.dimacs(),text=True,capture_output=True,timeout=seconds+20)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        return "UNSAT"
    if result.returncode == 0 and "UNKNOWN" in result.stdout:
        return "UNKNOWN"
    if result.returncode != 10 or "s SATISFIABLE" not in result.stdout:
        raise RuntimeError((result.returncode,result.stderr[-300:]))
    model = {int(v) for line in result.stdout.splitlines() if line.startswith("v ") for v in line.split()[1:]}
    gates = [(op in model, next(i for i,v in enumerate(l) if v in model),
              next(i for i,v in enumerate(r) if v in model)) for op,l,r in choices]
    for x in range(1 << N):
        wires = [bool(x & (1 << i)) for i in range(N)]
        for op,a,b in gates:
            wires.append((wires[a] or wires[b]) if op else (wires[a] and wires[b]))
        assert wires[-1] == graph.value(x)
    print("SAT witness",gates,flush=True)
    return "SAT"


def cover_program(graph):
    cover = min((x for x in range(1 << N) if all(x & e for e in graph.edges)),
                key=lambda x: bin(x).count("1"))
    stars = {}
    for e in graph.edges:
        center = ((cover & e) & -(cover & e)).bit_length()-1
        leaf = (e ^ (1 << center)).bit_length()-1
        stars.setdefault(center, []).append(leaf)
    gates = []

    def emit(op, a, b):
        gates.append((op, a, b))
        return N + len(gates)-1

    def join(wires):
        root, *others = wires
        for other in others:
            root = emit(1, root, other)
        return root

    join([emit(0, center, join(leaves)) for center,leaves in stars.items()])
    assert len(gates) == graph.size
    permitted = graph.first_choices(graph.size)
    for perm in graph.autos:
        labels = dict(enumerate(perm))
        pending = set(range(len(gates)))
        ordered = []
        while pending:
            ready = [(max(labels[a],labels[b]), min(labels[a],labels[b]), op, j)
                     for j in pending for op,a,b in [gates[j]] if a in labels and b in labels]
            hi,lo,op,j = min(ready)
            labels[N+j] = N+len(ordered)
            ordered.append((op,lo,hi))
            pending.remove(j)
        if ordered[0] in permitted:
            return ordered
    raise AssertionError("canonical first gate missing from upper-bound witness")


def prefix_search(graph, budget, exe, seconds, case, fixed=()):
    choices = graph.first_choices(budget)
    if case is not None:
        choices &= {case}
    fields = [budget, seconds, len(graph.edges), *graph.edges, *graph.pins.values(), len(choices)]
    for op, a, b in sorted(choices):
        fields.extend((int(op),a,b))
    fields.append(len(fixed))
    for gate in fixed:
        fields.extend(gate)
    result = run([exe], input=" ".join(map(str,fields)), text=True, capture_output=True, check=True)
    return result.stdout.strip()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver", nargs="?", default="cadical")
    parser.add_argument("--seconds",type=int,default=30)
    parser.add_argument("--only",type=int,nargs="+")
    parser.add_argument("--split",action="store_true")
    parser.add_argument("--prefix", action="store_true", help="use the exhaustive C++ prefix enumerator")
    parser.add_argument("--verify-upper", action="store_true", help="test the explicit cover circuits with every pruning rule")
    args = parser.parse_args()
    with ExitStack() as cleanup:
        if args.prefix or args.verify_upper:
            directory = cleanup.enter_context(tempfile.TemporaryDirectory())
            exe = str(Path(directory) / "seven-vertex-prefix")
            run(["c++","-O3","-std=c++17",str(notes / "seven-vertex-prefix.cpp"),"-o",exe],check=True)
        for idx,(edges,orbit) in enumerate(representatives(N)):
            if args.only and idx not in args.only:
                continue
            graph = Graph(edges)
            if args.verify_upper:
                upper = prefix_search(graph,graph.size,exe,args.seconds,None,cover_program(graph))
                assert upper.splitlines()[-1].startswith("SAT "), (idx, upper)
                print(idx,"verified upper",graph.size,flush=True)
                continue
            start = max(graph.pins.values()) + 1
            for budget in range(start,graph.size):
                cases = sorted(graph.first_choices(budget)) if args.split else [None]
                for case in cases:
                    status = (prefix_search(graph,budget,exe,args.seconds,case) if args.prefix else
                              search(graph,budget,args.solver,args.seconds,case))
                    print(idx,budget,case,status,flush=True)
            if start >= graph.size:
                print(idx,"deletion",flush=True)
