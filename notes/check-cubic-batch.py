"""Reproduce the static seven-erasure certificates. Python 3, standard library."""
from collections import deque
from functools import lru_cache
from itertools import combinations, product


def girth(n, edges):
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
    assert all(len(ns) == 3 for ns in neighbors)
    best = n + 1
    for s, t in edges:
        dist = {s: 0}
        queue = deque([s])
        while queue:
            u = queue.popleft()
            for v in neighbors[u]:
                if (u, v) == (s, t) or v in dist:
                    continue
                dist[v] = dist[u] + 1
                queue.append(v)
        if t in dist:
            best = min(best, 1 + dist[t])
    return best


@lru_cache(None)
def minimum_covers(edges):
    # An uncovered edge forces one of its endpoints. Keep every smallest answer.
    if not edges:
        return (frozenset(),)
    candidates = {c | {s} for s in edges[0] for c in minimum_covers(
        tuple(e for e in edges if s not in e))}
    size = min(map(len, candidates))
    return tuple(sorted((c for c in candidates if len(c) == size), key=sorted))


def build(n, stars, pins, isolated):
    raw = n + len(isolated)
    gates, marks, sums = [], {}, {}
    pinned = set(pins)

    def gate(op, a, b):
        gates.append((op, a, b))
        return raw + len(gates) - 1

    for center, leaves in sorted(stars.items()):
        # Accumulate the surviving leaves before attaching the pinned leaves.
        leaves = sorted(leaves, key=lambda v: (v in pinned, v))
        live = [v for v in leaves if v not in pinned]
        partial = leaves[0]
        anchor = partial if live else pins[0]
        for i, v in enumerate(leaves[1:], 1):
            partial = gate("or", partial, v)
            if center in pinned:
                marks[partial] = ("dead", pins[0])
            elif v in pinned:
                marks[partial] = ("equal", anchor)
            if i + 1 == len(live):
                anchor = partial
        term = gate("and", center, partial)
        if center in pinned or not live:
            marks[term] = ("equal", pins[0])
        sums[center] = term

    others = [w for c, w in sums.items() if c not in pinned] + list(isolated)
    assert others
    total = others[0]
    for w in others[1:]:
        total = gate("or", total, w)
    # If the only other term is a marked AND, it too becomes false.
    anchor = marks.get(total, (None, total))[1]
    for v in pins:
        total = gate("or", total, sums[v])
        marks[total] = ("equal", anchor)
    return gates, total, marks


# A monotone function is determined by its inclusion-minimal true input sets.
# Each bit mask is one such set. An empty collection represents false.
def minimal(terms):
    terms = sorted(set(terms), key=lambda t: bin(t).count("1"))
    result = []
    for t in terms:
        if all((s & t) != s for s in result):
            result.append(t)
    return frozenset(result)


def wires(n, gates, pins):
    row = [frozenset() if i in pins else frozenset({1 << i}) for i in range(n)]
    for op, a, b in gates:
        assert 0 <= a < len(row) and 0 <= b < len(row)
        x, y = row[a], row[b]
        if op == "or":
            row.append(minimal(x | y))
        else:
            assert op == "and"
            row.append(minimal(s | t for s in x for t in y))
    return row


def verify(n, edges, stars, pins, extras):
    isolated = tuple(range(n, n + extras))
    gates, out, marks = build(n, stars, pins, isolated)
    raw = n + extras
    assert len(gates) == len(edges) + len(stars) + extras - 1
    target = frozenset([1 << i for i in isolated] + [(1 << u) | (1 << v) for u, v in edges])
    assert wires(raw, gates, ())[out] == target
    rest = frozenset(t for t in target if all(not t & (1 << v) for v in pins))
    first = wires(raw, gates, pins)
    assert first[out] == rest
    # First check every site against the single original circuit.
    assert len(marks) == 7
    for w, (reason, p) in marks.items():
        assert raw <= w < raw + len(gates) and 0 <= p < w and p not in marks
        if reason == "equal":
            assert first[w] == first[p]
        else:
            assert w != out and all(w not in (a, b) or raw + j in marks
                                    for j, (_, a, b) in enumerate(gates))
    # Independently replay the desk's eraseRedirect and the two legal-move tests.
    sizes = len(gates)
    for w, (reason, p) in sorted(marks.items(), reverse=True):
        j = w - raw
        row = wires(raw, gates, pins)
        assert row[out] == rest
        if reason == "equal":
            assert row[w] == row[p]
        else:
            assert out != w and all(w not in (a, b) for _, a, b in gates[j + 1:])
        def redirect(i):
            return p if i == w else i - (i > w)
        gates = gates[:j] + [(op, redirect(a), redirect(b)) for op, a, b in gates[j + 1:]]
        out = redirect(out)
    assert len(gates) + 7 == sizes and wires(raw, gates, pins)[out] == rest


def examine(n, edges, extras, exhaustive):
    edges = tuple(sorted(edges))
    covers = minimum_covers(edges)
    trials = 0
    for cover in covers if exhaustive else covers[:1]:
        shared = [(u, v) for u, v in edges if u in cover and v in cover]
        for choices in product((0, 1), repeat=len(shared)) if exhaustive else [(0,) * len(shared)]:
            owners = {e: e[b] for e, b in zip(shared, choices)}
            stars = {s: [] for s in cover}
            for u, v in edges:
                s = owners.get((u, v), u if u in cover else v)
                stars[s].append(v if u == s else u)
            assert all(stars.values())
            for pins in shared:
                verify(n, edges, stars, pins, extras)
                trials += 1
    print(f"{n} graph vertices, {extras} isolated OR inputs, girth {girth(n, edges)}, "
          f"{len(covers)} minimum covers of size {len(covers[0])}, {trials} traces verified.")


if __name__ == "__main__":
    n = 24
    cage = {tuple(sorted((u, (u + d) % n))) for u in range(n)
            for d in (1, (12, 7, -7)[u % 3])}
    assert len(cage) == 36 and girth(n, cage) == 7
    examine(n, cage, 0, True)
    examine(n, cage, 2, False)
    # Triangles stress the case in which one outside center owns two pinned leaves.
    examine(4, set(combinations(range(4), 2)), 0, True)
