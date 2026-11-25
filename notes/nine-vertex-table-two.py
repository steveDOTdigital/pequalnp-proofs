"""Reproduce the nine-input ordinary circuit minimum for L-meta-11022/11023."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import permutations, product
from pathlib import Path
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LIB = runpy.run_path(str(HERE / "heawood-high-cofactor.py"))
EDGES = [(0, 4), (0, 5), (1, 5), (2, 6), (3, 6), (0, 7),
         (2, 7), (4, 7), (1, 8), (3, 8), (5, 8), (6, 8)]
BITS = [(1 << a) | (1 << b) for a, b in EDGES]
FULL = (1 << 9) - 1


def vertices(mask):
    return [v for v in range(9) if mask & (1 << v)]


def canonical(n, edges):
    """Compute an isomorphism key and the full stabilizer by permuting equal colors."""
    neighbors = [{b if a == v else a for a, b in edges if v in (a, b)} for v in range(n)]
    colors = {}
    for v, adj in enumerate(neighbors):
        color = len(adj), tuple(sorted(len(neighbors[w]) for w in adj))
        colors.setdefault(color, []).append(v)
    best = None
    maps = []
    for parts in product(*(permutations(colors[c]) for c in sorted(colors))):
        ordering = sum(parts, ())
        g = tuple(ordering.index(v) for v in range(n))
        key = tuple(sorted(tuple(sorted((g[a], g[b]))) for a, b in edges))
        if best is None or key < best:
            best, maps = key, []
        if key == best:
            maps.append(g)
    first = maps[0]
    group = [tuple(first.index(g[v]) for v in range(n)) for g in maps]
    assert all({tuple(sorted((g[a], g[b]))) for a, b in edges} == set(edges) for g in group)
    return (n, best), group


def run(seconds, workers, monotone_check):
    # The initial lower bound uses essential inputs alone. All stronger proper
    # subgraph bounds below have been proved earlier in this same run.
    active = []
    for mask in range(FULL + 1):
        used = 0
        for edge in BITS:
            if mask & edge == edge:
                used |= edge
        active.append(used)
    known = {0: 0}
    solved = {}
    binaries = {}
    totals = [0, 0]

    with tempfile.TemporaryDirectory(prefix="pnp-nine-table-two-") as scratch:
        def executable(n, monotone):
            key = n, monotone
            if key not in binaries:
                out = Path(scratch) / f"search-{n}-{int(monotone)}"
                subprocess.run(["c++", "-O3", "-std=c++17", f"-DWIDTH={n}", "-DSIGNED_MODE=1",
                                f"-DPETERSEN_PAIR_MODE={3 if monotone else 2}",
                                str(HERE / "petersen-raw-prefix.cpp"), "-o", str(out)], check=True)
                binaries[key] = out
            return binaries[key]

        for mask in sorted(set(active) - {0}, key=lambda s: (len(vertices(s)), s)):
            verts = vertices(mask)
            n = len(verts)
            edges = [(verts.index(a), verts.index(b)) for a, b in EDGES if a in verts and b in verts]
            key, group = canonical(n, edges)
            if key in solved:
                known[mask] = solved[key]
                continue
            loc = [sum(1 << verts[i] for i in range(n) if s & (1 << i)) for s in range(1 << n)]
            end = len(loc) - 1
            cover = min(len(vertices(s)) for s in range(1 << n)
                        if all(s & ((1 << a) | (1 << b)) for a, b in edges))
            upper = len(edges) + cover - 1
            floor = n - 1
            lower = [known[active[s]] for s in loc[:-1]] + [floor]
            for v in range(n):
                rest = end ^ (1 << v)
                neighbors = sum(1 << (b if a == v else a) for a, b in edges if v in (a, b))
                core = rest & ~neighbors
                zero_size = len(vertices(active[loc[rest]]))
                if zero_size:
                    floor = max(floor, lower[rest] + n - zero_size)
                high_size = len(vertices(neighbors)) + len(vertices(active[loc[core]]))
                high = lower[core] + len(vertices(neighbors)) - int(lower[core] == 0)
                floor = max(floor, high + n - high_size)
            assert floor <= upper
            if floor < upper:
                # A nonconstant output on both pins is needed for reader savings.
                assert all(active[loc[end ^ (1 << v)]] for v in range(n))
            for mono in ([False, True] if mask == FULL and monotone_check else [False]):
                limit = upper
                if mono:
                    # Replay the separate AND/OR exclusion at the last budget.
                    floor = upper - 1
                trial_count, node_count = 0, 0
                if floor < limit or mask == FULL:
                    binary = executable(n, mono)
                    lower[end] = floor
                    leaves = [g + 1 if g else 0 for g in lower]
                    witness = LIB["PROFILE"]["control"](n, seconds, leaves, lower, edges=edges)
                    checked = subprocess.run([str(binary)], input=witness, text=True,
                                             capture_output=True, check=True)
                    assert checked.stdout.splitlines()[-1].startswith("SAT "), checked.stdout
                    def visit(job):
                        result = subprocess.run([str(binary)], input=job[2], text=True, capture_output=True,
                                                check=True, timeout=seconds + 40)
                        verdict, nodes = result.stdout.splitlines()[-1].split()
                        if verdict != "UNSAT":
                            raise RuntimeError((mask, mono, budget, job[0], result.stdout))
                        return int(nodes)
                    for budget in range(floor, limit):
                        lower[end] = budget
                        leaves[end] = budget + 1
                        jobs = LIB["reader_jobs"](n, edges, group, leaves, lower, budget, seconds,
                                                  monotone_mode=mono, aggregate=True)
                        with ThreadPoolExecutor(max_workers=workers) as pool:
                            for nodes in pool.map(visit, jobs):
                                trial_count += 1
                                node_count += nodes
                        floor = budget + 1
                    print(f"{mask:3} {'AND/OR' if mono else 'signed':6} lower={floor:2} upper={upper:2}"
                          f" profiles={trial_count:4} prefixes={node_count}", flush=True)
                if mask != FULL:
                    totals[0] += trial_count
                    totals[1] += node_count
            if mask == FULL:
                assert floor == upper == 16
            else:
                assert floor == upper
                solved[key] = floor
                known[mask] = floor
        print(f"Proper induced graphs: {len(solved)} isomorphism types; "
              f"{totals[0]} searches, {totals[1]} prefixes.")
        print("Signed and ordinary minimum 16.")
    assert not Path(scratch).exists()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=int, default=90, help="time limit for a single profile")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--monotone-check", action="store_true", help="also replay the AND/OR exclusion at 15")
    args = parser.parse_args()
    if args.seconds < 1 or args.workers < 1:
        parser.error("time and worker limits must be positive")
    run(args.seconds, args.workers, args.monotone_check)
