"""Lower bounds by eliminating the first reused signal in a monotone circuit.

Tables use little-endian assignment order. Constants and unused variables are
removed before each recursive call. The bound concerns the Boolean function.
"""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import runpy


def assignments(mask):
    """Subsets in the order induced by their compact binary coordinates."""
    rows = [0]
    while mask:
        bit = mask & -mask
        rows += [row | bit for row in rows]
        mask ^= bit
    return rows


def project(table, rows):
    return sum(((table >> row) & 1) << j for j, row in enumerate(rows))


def essential(n, table):
    mask = 0
    for i in range(n):
        if any(((table >> r) ^ (table >> (r ^ (1 << i)))) & 1
               for r in range(1 << n) if r & (1 << i)):
            mask |= 1 << i
    return bin(mask).count("1"), project(table, assignments(mask))


@lru_cache(None)
def block(n, table, mask):
    """Return the two outside cofactors for a one-bit monotone block, or None."""
    inside = assignments(mask)
    outside = assignments(((1 << n) - 1) ^ mask)
    low = project(table, outside)
    high = project(table, [r | mask for r in outside])
    if low == high:
        return None
    for a in inside[1:-1]:
        row = project(table, [r | a for r in outside])
        if row != low and row != high:
            return None
    return low, high


@lru_cache(None)
def read_once(n, table):
    if n <= 1:
        return True
    # A deepest gate of any read-once formula joins two raw variables.
    for i, j in combinations(range(n), 2):
        pair = block(n, table, (1 << i) | (1 << j))
        if pair is not None:
            low, high = pair
            if read_once(n-1, low | (high << (1 << (n-2)))):
                return True
    return False


@lru_cache(None)
def lower(n, table):
    if n <= 1:
        return 0
    if read_once(n, table):
        return n-1
    # With a tree on the essential sources, n-1 gates would be read-once.
    best = None
    for mask in range(1, (1 << n)-1):
        pair = block(n, table, mask)
        if pair is None:
            continue
        k = bin(mask).count("1")
        # All possible first reused blocks are included. Extra admissible
        # blocks whose inside function is not read-once can only weaken this bound.
        branches = [lower(*essential(n-k, cofactor)) for cofactor in pair]
        bound = k + 1 + max(branches)
        best = bound if best is None else min(best, bound)
    assert best is not None  # Each singleton is eligible.
    return max(n, best)


def graph(edges):
    n = 1 + max(max(edge) for edge in edges)
    table = sum(int(any((r >> a) & (r >> b) & 1 for a, b in edges)) << r
                for r in range(1 << n))
    return essential(n, table)


def switching_pairs(n, table):
    universe = (1 << n) - 1
    switches = []
    for i, j in combinations(range(n), 2):
        pair = (1 << i) | (1 << j)
        rows = assignments(pair)
        tables = {project(table, [z | r for r in rows]) for z in assignments(universe ^ pair)}
        if 8 in tables and 14 in tables:  # AND and OR on the two variables
            switches.append(pair)
    return switches


def excludes_two_extra_reads(n, table):
    """Certify that a live circuit requires more than two reads beyond the first."""
    universe = (1 << n)-1
    if any(block(n, table, subset) is not None for subset in range(1, universe)
           if subset & (subset-1)):
        return False
    switches = switching_pairs(n, table)
    # Three uses of one raw input, or two reused raw inputs, cannot meet these pairs.
    if any(all(pair & group for pair in switches) for group in range(1 << n)
           if bin(group).count("1") <= 2):
        return False
    for i in range(n):
        x = 1 << i
        for private in assignments(universe ^ x)[1:]:
            if any(not (pair & (x | private)) for pair in switches):
                continue
            inner = assignments(private)
            outer = assignments(universe ^ (x | private))
            ones = (1 << len(inner))-1
            tables = []
            for choice in (0, x):
                cofactors = {project(table, [u | v | choice for u in inner]) for v in outer}
                tables.append(cofactors - {0, ones})
            if any(len(bits) > 1 for bits in tables):
                continue
            if all(tables):
                inside = next(iter(tables[0])) | (next(iter(tables[1])) << len(inner))
                width = bin(private).count("1")+1
                if essential(width, inside)[0] != width or not read_once(width, inside):
                    continue
            return False
    return True


def triangle_family():
    """Cycle plus each possible number of private point inputs."""
    cycle = [(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)]
    for count in range(4):
        edges = cycle + [(6+i,3+i) for i in range(count)]
        n, table = graph(edges)
        assert excludes_two_extra_reads(n,table)
        # Three ordinary stars require one OR per additional private edge.
        print(f"Six-cycle with {count} private leaves: exact minimum {n+2}",flush=True)


def cycle_stars():
    edges = [(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)]
    for centers in ((0,1,2),(3,4,5)):
        for last in range(3):
            gates = []
            stars = []
            for c in centers:
                a,b = sorted(v for e in edges if c in e for v in e if v != c)
                gates.append((True,a,b))
                gates.append((False,c,6+len(gates)-1))
                stars.append(6+len(gates)-1)
            first,second = [stars[j] for j in range(3) if j != last]
            gates.append((True,first,second))
            gates.append((True,stars[last],6+len(gates)-1))
            yield tuple(gates)


def add_private(n, gates):
    """Insert one new OR after any wire and redirect a nonempty subset of its reads."""
    for wire in range(n+len(gates)):
        readers = [(g,k) for g,gate in enumerate(gates) for k in (1,2) if gate[k]==wire]
        if wire == n+len(gates)-1:
            readers.append((len(gates),0))
        for chosen in range(1,1<<len(readers)):
            selected = {r for i,r in enumerate(readers) if chosen & (1<<i)}
            mapping, expanded = dict(enumerate(range(n))), []
            if wire < n:
                replacement = n+1
                expanded.append((True,wire,n))
            for g,(op,a,b) in enumerate(gates):
                left = replacement if (g,1) in selected else mapping[a]
                right = replacement if (g,2) in selected else mapping[b]
                expanded.append((op,left,right))
                mapping[n+g] = n+len(expanded)
                if wire == n+g:
                    replacement = n+1+len(expanded)
                    expanded.append((True,mapping[wire],n))
            yield tuple(expanded)


def circuit_signature(n, gates):
    """Names internal wires by structure; minimum circuits have no duplicate gates."""
    keys = [str(i) for i in range(n)]
    for op,a,b in gates:
        left,right=sorted((keys[a],keys[b]))
        keys.append(("+" if op else "*")+"("+left+","+right+")")
    return keys[-1]


def evaluate_core(n, gates, columns, seeds=None):
    values = list(columns)
    slopes = list(seeds) if seeds is not None else [False]*n
    for op,a,b in gates:
        values.append(values[a]|values[b] if op else values[a]&values[b])
        slopes.append(slopes[a]|slopes[b] if op else (values[a]&slopes[b])|(slopes[a]&values[b]))
    return values[-1],slopes[-1]


def classify_triangle_extensions():
    edges = [(0,3),(1,3),(1,4),(2,4),(2,5),(0,5)]
    circuits = list(cycle_stars())
    assert len({circuit_signature(6,g) for g in circuits}) == 6
    for j in range(3):
        n = 6+j
        edges.append((n,3+j))
        width, truth = graph(edges)
        assert width == n+1
        columns = [sum(((r>>i)&1)<<r for r in range(1<<width)) for i in range(width)]
        retained = {}
        for gates in circuits:
            for extension in add_private(n,gates):
                if evaluate_core(width,extension,columns)[0] == truth:
                    retained[circuit_signature(width,extension)] = extension
        assert retained
        circuits = list(retained.values())
        misses = [0,0,0]
        for gates in circuits:
            for a,b in edges:
                at = [i==a for i in range(width)]
                direction = [i==b for i in range(width)]
                da = evaluate_core(width,gates,at,direction)[1]
                db = evaluate_core(width,gates,direction,at)[1]
                if not da: misses[0]+=1
                if not db: misses[1]+=1
                if not da and not db: misses[2]+=1
        print(f"{j+1} private leaves: {len(circuits)} optimal circuits, "
              f"directional misses {misses[:2]}, double misses {misses[2]}", flush=True)
    return misses


def verify_plane_helpers(plane):
    """Check the surviving point-OR shapes for all triples of unfinished lines."""
    from itertools import product
    edges = plane["INCIDENT"]
    lines = [{p for p,j in edges if j == i} for i in range(13)]
    totals = [0,0]
    for chosen in combinations(range(13),3):
        triple = [lines[i] for i in chosen]
        region = set.union(*triple)
        common = set.intersection(*triple)
        if common:
            private = [sorted(line - common) for line in triple]
            cores = [common | set(reps) for reps in product(*private)]
            expected = set()
        else:
            corners = set.union(*(a & b for a,b in combinations(triple,2)))
            cores = [corners]
            expected = {frozenset((a,c)) for line in triple for a in line-corners
                        for c in corners-line}
        allowed = set()
        for j,line in enumerate(lines):
            if j in chosen:
                continue
            for size in range(2,5):
                for points in combinations(line,size):
                    group = frozenset(points)
                    if group <= region and all(group & core for core in cores):
                        allowed.add(group)
        assert allowed == expected
        totals[bool(common)] += 1
    assert totals == [234,52]
    return totals


def doubled_plane_control():
    plane = runpy.run_path(str(Path(__file__).with_name("check-plane-safe-stars.py")))
    counts = verify_plane_helpers(plane)
    print(f"Helper restrictions passed on {counts[0]} triangles and {counts[1]} pencils.")
    gates, root = plane["star_circuit"](0)
    assert 26 + len(gates)-1 == root and gates[-1][0] == "or"
    gates += [gates[-1], ("and", root, root+1)]
    assert len(gates) == 66
    edges = sorted(plane["INCIDENT"])
    rows = [(1 << p) | (1 << (13+l)) for p,l in edges] + plane["maximal_negatives"]()
    columns = [sum(((r >> i)&1) << j for j,r in enumerate(rows)) for i in range(26)]
    assert plane["wires"](gates, columns)[-1] == (1 << len(edges))-1
    for p,l in edges:
        for x,d in ((p,13+l),(13+l,p)):
            assert not plane["derivative"](gates, root+2, x,d)
    return len(edges), len(rows)


if __name__ == "__main__":
    triangle = [(0,6),(1,6),(3,6),(1,7),(2,7),(4,7),(2,8),(0,8),(5,8)]
    pencil = [(0,4),(1,4),(0,5),(2,5),(0,6),(3,6)]
    path = [(0,3),(1,3),(0,4),(2,4)]
    for name, edges in [("two-line path",path),("three-line pencil",pencil),
                        ("three-line triangle",triangle)]:
        n, table = graph(edges)
        print(name, n, "variables, lower bound", lower(n,table), flush=True)
    triangle_family()
    classify_triangle_extensions()
    flags, rows = doubled_plane_control()
    print(f"66-gate control: both directions vanish at all {flags} flags, {rows} boundary rows passed")
