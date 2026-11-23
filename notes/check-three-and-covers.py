"""Exhaust the eight-corner representations for the partial AND count in L-meta-958.

Requires Python 3.10 or later. All calculations use finite sets or integer bit masks.
"""

import argparse
import subprocess
from functools import lru_cache
from itertools import combinations, permutations, product


def maximal(families):
    return [f for f in families if not any(f < g for g in families)]


def topology_families():
    families = set()
    for left1, right1, left2, right2, output in product(range(2), range(2),
                                                         range(4), range(4), range(8)):
        parents = [0, 0, left1, right1, left2, right2]
        reached = [0] * 6
        for corner in range(8):
            live = output
            for gate in (2, 1, 0):
                if live & (1 << gate):
                    side = 2 * gate + ((corner >> gate) & 1)
                    reached[side] |= 1 << corner
                    live |= parents[side]
        # A vertex belongs to the false set at a corner iff none of the
        # reached sides contains it as a bare variable.
        profiles = {255}
        for side in reached:
            profiles |= {profile & ~side for profile in profiles}
        families.add(frozenset(profiles))
    assert len(families) == 36
    return maximal(families)


def canonical(family, degree):
    # A corner's incident profile sizes are invariant under corner relabeling.
    signatures = [tuple(sum(bool(a & (1 << j)) and a.bit_count() == size for a in family)
                        for size in range(1, degree + 1)) for j in range(degree)]
    blocks = [[j for j in range(degree) if signatures[j] == value]
              for value in sorted(set(signatures))]
    best = None
    for order in product(*(permutations(block) for block in blocks)):
        perm = sum(order, ())
        image = tuple(sorted(sum(((a >> j) & 1) << perm.index(j) for j in range(degree))
                             for a in family))
        if best is None or image < best:
            best = image
    return best


def hosts():
    projected = {}
    for family in topology_families():
        for selected in range(1, 256):
            bits = [j for j in range(8) if selected & (1 << j)]
            restricted = frozenset(sum(((a >> j) & 1) << i for i, j in enumerate(bits))
                                   for a in family) - {0}
            projected.setdefault(len(bits), set()).add(restricted)
    result = {canonical(f, degree) for degree, families in projected.items()
              for f in maximal(families)}
    assert len(result) == 44
    return sorted(result, key=lambda row: (len(row), row))


def check_host(profiles):
    n = len(profiles)
    adj = [sum(1 << j for j, b in enumerate(profiles) if not a & b) for a in profiles]
    forbidden = set()
    for i, j in combinations(range(n), 2):
        common = [k for k in range(n) if adj[i] & adj[j] & (1 << k)]
        for k, l in combinations(common, 2):
            forbidden.add((1 << i) | (1 << j) | (1 << k) | (1 << l))
    for i, j, k in combinations(range(n), 3):
        a, b, c = profiles[i], profiles[j], profiles[k]
        if a & b and b & c and c & a and not a & b & c:
            forbidden.add((1 << i) | (1 << j) | (1 << k))
    forbidden = sorted(forbidden, key=lambda x: (x.bit_count(), x))

    @lru_cache(None)
    def has_cover(active, budget):
        for i in range(n):
            edge_ends = adj[i] & active
            if active & (1 << i) and edge_ends:
                if not budget:
                    return False
                one_end = edge_ends & -edge_ends
                return (has_cover(active ^ (1 << i), budget - 1) or
                        has_cover(active ^ one_end, budget - 1))
        return True

    visited = set()

    def visit(active):
        if active in visited:
            return
        visited.add(active)
        if has_cover(active, 3):
            return
        for obstruction in forbidden:
            if active & obstruction == obstruction:
                # Every admissible subfamily omits at least one of these vertices.
                while obstruction:
                    one = obstruction & -obstruction
                    obstruction ^= one
                    visit(active ^ one)
                return
        raise AssertionError(("cover exceeds three", tuple(a for i, a in enumerate(profiles)
                                                            if active & (1 << i))))

    visit((1 << n) - 1)
    return len(visited)


def check_sat(profiles, solver):
    n = len(profiles)
    if n <= 3:
        return
    clauses, edge_vars = [], {}
    for i, j in combinations(range(n), 2):
        if not profiles[i] & profiles[j]:
            edge = n + len(edge_vars) + 1
            edge_vars[i, j] = edge
            clauses.extend(([-edge, i+1], [-edge, j+1]))
    for triple in combinations(range(n), 3):
        a, b, c = (profiles[j] for j in triple)
        if a & b and a & c and b & c and not a & b & c:
            clauses.append([-j-1 for j in triple])
        # If the three vertices fail to cover the selected graph, at
        # least one selected edge must avoid all three.
        clauses.append([v for (i, j), v in edge_vars.items()
                        if i not in triple and j not in triple])
    for quad in combinations(range(n), 4):
        a, b, c, d = (profiles[j] for j in quad)
        if any(not left & right for left, right in
               [(a | b, c | d), (a | c, b | d), (a | d, b | c)]):
            clauses.append([-j-1 for j in quad])
    dimacs = f"p cnf {n + len(edge_vars)} {len(clauses)}\n"
    dimacs += "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
    result = subprocess.run([solver, "-q", "--check", "--checkproof=2", "-t", "60"],
                            input=dimacs, text=True, capture_output=True, timeout=80)
    if result.returncode != 20 or "s UNSATISFIABLE" not in result.stdout:
        raise RuntimeError(("host SAT check inconclusive", profiles, result.returncode))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", help="also check each nontrivial host by SAT")
    args = parser.parse_args()
    all_hosts = hosts()
    states = sum(check_host(h) for h in all_hosts)
    print("44 hosts verified;", states, "subfamilies visited; largest host:",
          max(map(len, all_hosts)), "profiles.", flush=True)
    if args.solver:
        for host in all_hosts:
            check_sat(host, args.solver)
        print("Independent SAT checks passed for every host with more than three profiles.")
