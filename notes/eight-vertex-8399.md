# The eight-input graph in L-meta-8399 needs exactly 15 gates

The minimum in [L-meta-8399](https://pequalnp.com/lemma#L-meta-8399) is **15** for binary AND/OR/NOT circuits. A 15-gate circuit attains the bound. The argument excludes the negated twin [L-meta-8400](https://pequalnp.com/lemma#L-meta-8400) on the same truth table.

The lower bound uses two exhaustive calculations. Even with free complements of every wire and of the output, the function needs at least 14 binary gates. A circuit spending one gate on a NOT therefore needs at least 15 ordinary gates. For a circuit made only of binary ANDs and ORs, a separate calculation rules out 14 gates. Constants, copies, invalid reads and gates of arity below two are covered by the normalization theorem. The [Lean file](EightVertex8399.lean) verifies the actual indexed 15-gate circuit and proves that the two numerical exclusions imply the exact posted proposition. The numerical exclusions run outside Lean.

## Upper bound

Use a five-vertex cover with centres 0, 1, 3, 5 and 6. OR together the following five terms.

```text
0 AND (1 OR 2 OR 3 OR 4)
1 AND (2 OR 5)
3 AND (4 OR 7)
5 AND 7
6 AND (2 OR 7)
```

The terms use six internal ORs and five ANDs, followed by four more ORs. They contain precisely the eleven edges in the statement. Lean checks agreement on all 256 inputs. As positive controls the search also reconstructs a 15-gate circuit in both models and replays its gates on every input.

## Lower bound

Start with the induced subgraphs, in order of increasing numbers of active vertices. Ignore isolated vertices by setting them to zero. Pinning vertex v low leaves its induced deletion. Pinning it high leaves an OR of its neighbors and the graph function on the non-neighbors. Each disjoint OR literal above a nonconstant residual costs at least one binary gate. Pinning a literal to zero removes a reader. With no residual edge, a disjunction of d neighbors costs d−1 gates. More generally, the live cone of a circuit with n essential inputs and s strictly binary gates has undirected cycle rank s−n+1. Pin, contract constant and copy gates and trim to a nonconstant output. The resulting cone is a graph minor, so losing an essential input saves at least one gate. These restrictions, and the [first-gate elimination recurrence](petersen-gate-elimination.py), supply the initial lower bounds.

The [profile generator](heawood-high-cofactor.py) enumerates numbers of direct readers of each raw input. Their sum is at most s+1 because all s−1 internal outputs other than the circuit output need a reader. A controlling pin can eliminate direct readers and their consumers. The [signed reader argument](petersen-unary-input.md) gives the restriction budgets and the explanation for counting coincident consumers. Apply graph automorphisms only to equivalent profiles. In the signed model choose the representative of a complementary pair of wires that is false on the empty input. The four choices of input signs for a binary AND now include OR by De Morgan's law. The monotone run permits only the AND and OR choices.

For every surviving profile, the [prefix verifier](petersen-raw-prefix.cpp) checks gate pairs in a canonical topological order. It retains the actual truth values, outstanding raw-reader counts, live outputs requiring readers, and loss budgets on pinned subgraphs. The [additional cuts](petersen-profile-cuts.hpp) check separation of opposite outputs and necessary remaining reads. An exhaustive UNSAT result eliminates the profile. A timeout supplies no exclusion. Stronger lower bounds are used only after the relevant smaller cases finish.

With complements free, the eight individual zero deletions in vertex order have exact costs **10, 11, 11, 11, 12, 12, 12, 11**. At the final signed budget of 13, all 30 surviving profiles were excluded in 38,750 visited prefixes. At the final monotone budget of 14, all 748 profiles were excluded in 2,486,553 prefixes. The signed replay from elementary restrictions checked 315 profiles and 153,764 prefixes across all sizes. The 30 and 748 counts concern the final full-graph budgets. No assertion about whether 14 binary gates suffice with free complements is needed for the ordinary minimum.

## Replay

Run this Python 3.10+ block from the root of the research fork with a C++17 compiler available as `c++` or through the `CXX` environment variable. It rebuilds the lower bounds from elementary restrictions. It checks the star construction before each new family of exclusions, rejects every incomplete search, and removes its temporary binaries on exit.

```python
from pathlib import Path
import os, tempfile, subprocess, shlex, runpy
from concurrent.futures import ThreadPoolExecutor

notes=Path("notes").resolve()
library=runpy.run_path(str(notes/"heawood-high-cofactor.py"))
canonical=runpy.run_path(str(notes/"nine-vertex-table-two.py"))["canonical"]
edges=[[0,1],[0,2],[0,3],[0,4],[1,2],[1,5],[2,6],[3,4],[3,7],[5,7],[6,7]]

def active(mask):
    return sum(1<<v for v in {x for a,b in edges if mask>>a & mask>>b & 1 for x in (a,b)})

# Restrictions use the connected live circuit inequality: pinning to a
# nonconstant output pays one gate for every essential input that disappears.
def starting_floors():
    bounds={0:0}
    recurrence=runpy.run_path(str(notes/"petersen-gate-elimination.py"))["lower"]
    for s in sorted(range(1,256), key=int.bit_count):
        if active(s)!=s:
            bounds[s]=bounds[active(s)]
            continue
        vertices=[v for v in range(8) if s>>v&1]
        n=len(vertices)
        pairs=[(vertices.index(a),vertices.index(b)) for a,b in edges if s>>a & s>>b & 1]
        table=tuple(any(x>>a & x>>b & 1 for a,b in pairs) for x in range(1<<n))
        floor=recurrence(table)
        for j,v in enumerate(vertices):
            off=s^(1<<v)
            near=sum(1<<w for a,b in edges if v in (a,b)
                     for w in [b if a==v else a] if s>>w&1)
            low=active(off)
            if low:
                floor=max(floor,bounds[low]+n-low.bit_count())
            core=active(off&~near)
            alarms=near.bit_count()
            high=bounds[core]+alarms-int(core==0)
            floor=max(floor,high+n-alarms-core.bit_count())
        bounds[s]=floor
    return [bounds[i] for i in range(256)]

def replay(tmp, bounds, monotone, target_bound):
    result = dict(enumerate(bounds))
    solved = {}
    for mask in sorted(set(active(i) for i in range(256)) - {0}, key=lambda s:(s.bit_count(),s)):
        vertices = [i for i in range(8) if mask >> i & 1]
        n = len(vertices)
        pairs = [(vertices.index(a),vertices.index(b)) for a,b in edges if mask >> a & mask >> b & 1]
        key, group = canonical(n,pairs)
        if key in solved:
            result[mask] = solved[key]
            continue
        end = (1 << n) - 1
        cover = min(s.bit_count() for s in range(end+1)
                    if all((s >> a | s >> b) & 1 for a,b in pairs))
        upper = len(pairs) + cover - 1
        goal = target_bound if mask == 255 else upper
        floor = result[mask]
        if floor < goal:
            def lift(s):
                return sum(1 << v for j,v in enumerate(vertices) if s >> j & 1)
            lower = [result[active(lift(s))] for s in range(end+1)]
            leaves = [g+1 if g else 0 for g in lower]
            exe = tmp / (f"search-{n}-{int(monotone)}" + (".exe" if os.name == "nt" else ""))
            if not exe.exists():
                subprocess.run([*shlex.split(os.environ.get("CXX","c++")), "-std=c++17", "-O3",
                                f"-DWIDTH={n}", "-DSIGNED_MODE=1", f"-DPETERSEN_PAIR_MODE={3 if monotone else 2}",
                                str(notes/"petersen-raw-prefix.cpp"), "-o", str(exe)], check=True)
            def run(data):
                p = subprocess.run([str(exe)], input=data, text=True, capture_output=True,
                                   check=True, timeout=200)
                return p.stdout.splitlines()[-1].split()
            control = library["PROFILE"]["control"](n,55,leaves,lower,edges=pairs)
            assert run(control)[0] == "SAT"
            for budget in range(floor, goal):
                lower[end] = budget
                leaves[end] = budget + 1
                jobs = list(library["reader_jobs"](n,pairs,group,leaves,lower,budget,55,
                            monotone_mode=monotone,aggregate=True))
                with ThreadPoolExecutor(max_workers=2) as pool:
                    outcomes = list(pool.map(run,(job[2] for job in jobs)))
                assert all(status == "UNSAT" for status,_ in outcomes), (mask,budget,outcomes)
                print(mask, int(monotone), budget, len(jobs), sum(int(nodes) for _,nodes in outcomes))
            floor = goal
        solved[key] = result[mask] = floor
    return [result[active(i)] for i in range(256)]


with tempfile.TemporaryDirectory(prefix="eight-vertex-8399-") as stage:
    signed = replay(Path(stage), starting_floors(), False, 14)
    ordinary = replay(Path(stage), signed, True, 15)
    assert signed[255] == 14 and ordinary[255] == 15
assert not Path(stage).exists()
```
