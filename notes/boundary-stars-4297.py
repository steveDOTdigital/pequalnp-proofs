"""Replay the boundary-gate count for the examples in boundary-stars-4297.md."""
from collections import defaultdict
from itertools import combinations


def check(left, right, edges, gates):
    vertices = left | right
    n = len(vertices)
    rows = range(1 << n)
    assert vertices == set(range(n)) and not left & right and edges
    assert all(u in left and v in right for u, v in edges)
    neighbors = {v: set() for v in vertices}
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    assert all(len(neighbors[u] & neighbors[v]) <= 1 for u, v in combinations(vertices, 2))

    def row(active):
        return sum(1 << v for v in active)

    target = sum(1 << r for r in rows if any(r & (1 << u) and r & (1 << v) for u, v in edges))
    table = [sum(1 << r for r in rows if r & (1 << v)) for v in range(n)]
    used = {n + len(gates) - 1}
    for w in range(max(used), n - 1, -1):
        if w in used:
            used.update(gates[w - n][1:])
    for w, (op, i, j) in enumerate(gates, n):
        assert 0 <= i < w and 0 <= j < w and op in ("or", "and")
        table.append(table[i] | table[j] if op == "or" else table[i] & table[j])
    assert table[-1] == target
    below = {w for w in used if not table[w] & ~target}
    singleton = [{v for v in vertices if t & (1 << (1 << v))} for t in table]
    live = {w for w in used if w >= n}
    boundary, unsafe_ands, origins = set(), set(), set()
    mixed = {w for w in used if singleton[w] & left and singleton[w] & right}
    for w in live:
        op, i, j = gates[w - n]
        if op == "or" and {i, j} & below:
            assert {i, j} <= below
        if w in below and not {i, j} & below:
            assert op == "and"
            boundary.add(w)
        if op == "and" and w not in below:
            unsafe_ands.add(w)
        if w in mixed and not {i, j} & mixed:
            assert op == "or"
            origins.add(w)

    # Each endpoint must register on a different operand as a singleton.
    # A boundary may accept additional edges on two-endpoint inputs.
    assignments = defaultdict(list)
    remaining = set(edges)
    for w in sorted(boundary):
        _, i, j = gates[w - n]
        if not singleton[i] or not singleton[j]:
            continue
        rect = {tuple((u, v) if u in left else (v, u)) for u in singleton[i] for v in singleton[j]}
        assert rect <= edges and min(len(singleton[i]), len(singleton[j])) == 1
        center_wire, leaves_wire = (i, j) if len(singleton[i]) == 1 else (j, i)
        c, = singleton[center_wire]
        assigned = rect & remaining
        if assigned:
            leaves = {v if u == c else u for u, v in assigned}
            assignments[c].append((leaves_wire, leaves))
            remaining -= assigned

    charges = defaultdict(set)
    pure_filters = {}
    for c, stars in assignments.items():
        leaves = set.union(*(group for _, group in stars))
        center_shore, leaf_shore = (left, right) if c in left else (right, left)
        independent = row({c} | (leaf_shore - neighbors[c]))
        assert all(not singleton[w] & center_shore for w, _ in stars)
        forks, seen, labels = set(), set(), set()

        def trace(w):
            hits = singleton[w] & leaves
            assert hits and not (table[w] >> independent) & 1
            if len(hits) == 1:
                leaf, = hits
                labels.add(leaf)
                return leaf
            if w not in seen:
                seen.add(w)
                op, i, j = gates[w - n]
                if op == "and":
                    trace(i if not (table[i] >> independent) & 1 else j)
                else:
                    predecessors = {trace(p) for p in (i, j) if singleton[p] & leaves}
                    if len(predecessors) == 2:
                        forks.add(w)
            return w

        for w, _ in stars:
            trace(w)
        assert labels == leaves and len(forks) >= len(leaves) - len(stars)
        for w in sorted(forks)[:len(leaves) - len(stars)]:
            charges[w].add(c)
        pure_filters[c] = {w for w in seen & unsafe_ands if not singleton[w] & center_shore}

    assert all(len(cs & left) <= 1 and len(cs & right) <= 1 for cs in charges.values())
    doubles = {w: cs for w, cs in charges.items() if len(cs) == 2}
    affected = {c for cs in doubles.values() for c in cs}
    assert all(pure_filters[c] for c in affected)
    assert all(not pure_filters[c] & pure_filters[d] for c, d in combinations(affected, 2))
    assert not (set(charges) & (below | unsafe_ands | origins))
    K = sum(map(len, assignments.values()))
    visible = len(edges - remaining)
    bound = visible - K - len(doubles) + len(unsafe_ands) + len(origins) + 2 * len(boundary) - 1
    assert len(live) >= bound
    cover = min(len(s) for k in range(n + 1) for s in combinations(vertices, k)
                if all(u in s or v in s for u, v in edges))
    return dict(rows=len(rows), edges=len(edges), visible=visible, boundaries=len(boundary),
                stars=K, doubles=len(doubles), paid_filters=len(affected), unsafe_ands=len(unsafe_ands),
                mixed_origins=len(origins), lower_bound=bound, required=len(edges) + cover - 1,
                actual=len(live))


def two_stars(k):
    # a, b are opposite centers. The wire W merges the pairs (x_i OR u_i).
    a, b = 0, 1
    xs = list(range(2, 2 + k))
    us = list(range(2 + k, 2 + 2 * k))
    n = 2 + 2 * k
    gates = []

    def gate(op, i, j):
        gates.append((op, i, j))
        return n + len(gates) - 1

    def join(ws):
        result, *rest = ws
        for w in rest:
            result = gate("or", result, w)
        return result

    mixed = join([gate("or", x, u) for x, u in zip(xs, us)])
    qa = gate("and", mixed, join([*xs, b]))
    qb = gate("and", mixed, join([*us, a]))
    gate("or", gate("and", a, qa), gate("and", b, qb))
    edges = {(a, x) for x in xs} | {(u, b) for u in us}
    result = check({a, *us}, {b, *xs}, edges, gates)
    assert result["doubles"] == k - 1 and result["paid_filters"] == 2
    return result


if __name__ == "__main__":
    for k in (2, 3, 4):
        result = two_stars(k)
        assert result["lower_bound"] >= result["required"]
        print("Two stars of degree", k, result)
    gates = [("or", 0, 1), ("or", 0, 3), ("or", 2, 1), ("or", 2, 3),
             ("and", 4, 5), ("and", 6, 7), ("and", 8, 9)]
    result = check({0, 1}, {2, 3}, {(0, 2), (1, 3)}, gates)
    assert result["visible"] == 1 and result["lower_bound"] >= result["required"]
    print("One hidden matching edge", result)
    gates[4:6] = [("and", 4, 7), ("and", 5, 6)]
    result = check({0, 1}, {2, 3}, {(0, 2), (1, 3)}, gates)
    assert result["visible"] == 0 and result["lower_bound"] >= result["required"]
    print("Two hidden matching edges", result)
