"""Replay the residual-edge bounds for L-meta-2382 using the actual eleven-vertex graph."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import runpy

graph = runpy.run_path(str(Path(__file__).with_name("eleven-dirty-search.py")))
EDGES = tuple(graph["POS"])
NEG = tuple(graph["NEG"])


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask -= bit


def free_sources(edges):
    """Grant all raw literals and ORs of covered neighbors of any center."""
    endpoints = 0
    for edge in edges:
        endpoints |= edge
    sources = set(bits(endpoints))
    for vertex in range(11):
        center = 1 << vertex
        hood = sum(e ^ center for e in EDGES if e & center and e not in edges)
        sub = hood & endpoints
        while sub:
            sources.add(sub)
            sub = (sub - 1) & hood & endpoints
    return tuple(sorted(sources))


def warm_rows(edges, sources):
    clauses = [s for s in sources if all(s & e for e in edges)]
    return [row for row in NEG if all(row & s for s in clauses)]


def check_products():
    pairs = [p for p in combinations(EDGES, 2) if not warm_rows(p, free_sources(p))]
    assert len(pairs) == 4
    for a, b in combinations(pairs, 2):
        if set(a).isdisjoint(b):
            sources = free_sources(set(a) | set(b))
            assert warm_rows(a, sources) or warm_rows(b, sources)
    for triple in combinations(EDGES, 3):
        sources = free_sources(triple)
        warm = warm_rows(triple, sources)
        assert warm
        # One additional OR of two sources must itself reject every warm row.
        cold = [s for s in sources if not any(s & row for row in warm)]
        assert not any(all((a | b) & e for e in triple) for a in cold for b in cold)
    print("560 triples excluded with one extra raw OR; four feasible pairs; no disjoint pair of pairs.")


def projected_negatives(edges, negatives):
    endpoints = 0
    for edge in edges:
        endpoints |= edge
    rows = {row & endpoints for row in negatives}
    return sorted(row for row in rows if not any(row != other and row & other == row for other in rows))


def sources_suffice(edges, negatives, sources, limit):
    """Hitting set for the source wires that can distinguish each positive/negative pair."""
    conditions = {sum(1 << i for i, s in enumerate(sources) if s & e and not s & n)
                  for e in edges for n in negatives}
    minimal = tuple(sorted((c for c in conditions if not any(t != c and t & c == t
                                                             for t in conditions)),
                           key=int.bit_count))

    @lru_cache(None)
    def choose(left, slots):
        if not left:
            return True
        if not slots:
            return False
        return any(choose(tuple(c for c in left if not c & wire), slots - 1)
                   for wire in bits(left[0]))

    return choose(minimal, limit)


def check_extra_pairs():
    def possible(pairs):
        union = set().union(*pairs)
        if len(union) != 2 * len(pairs):
            return False
        sources = free_sources(union)
        must_hit = set()
        forbidden = 0
        for pair in pairs:
            warm = warm_rows(pair, sources)
            if warm:
                must_hit.update(pair)
                for row in warm:
                    forbidden |= row
        candidates = [s for s in sources if not s & forbidden]
        return not must_hit or any(all((a | b) & e for e in must_hit)
                                  for a in candidates for b in candidates)

    pairs = [pair for pair in combinations(EDGES, 2) if possible([pair])]
    assert len(pairs) == 48
    assert sum(possible(group) for group in combinations(pairs, 2)) == 49
    assert not any(possible(group) for group in combinations(pairs, 3))
    print("With one extra raw OR, at most two disjoint pairs can be served together.")


def check_guard():
    # A non-singleton allowed guard lies in N(v). The edge joining v to a
    # guard neighbor is covered and cannot be among the hidden edges.
    families = set()
    for vertex in range(11):
        center = 1 << vertex
        hood = sum(e ^ center for e in EDGES if e & center)
        for group in ([e for e in EDGES if e & hood and not e & center],
                      [e for e in EDGES if e & center]):
            for size in range(2, len(group) + 1):
                families.update(combinations(group, size))
    counts = Counter()
    for edges in families:
        sources = free_sources(edges)
        guards = [s for s in sources if all(s & e for e in edges)]
        for guard in guards:
            if any(t != guard and t & guard == t for t in guards):
                continue
            negatives = [row for row in NEG if row & guard]
            counts[len(edges)] += 1
            assert not sources_suffice(edges, negatives, sources, len(edges) - 1)
    assert counts == {2: 141, 3: 193, 4: 137, 5: 55, 6: 12, 7: 1}
    print("539 guarded families require at least one source wire per hidden edge.")


def circuit_exists(edges, sources, budget):
    negatives = projected_negatives(edges, NEG)
    rows = list(edges) + negatives
    p, n = len(edges), len(negatives)
    pos_mask, neg_mask = (1 << p) - 1, (1 << n) - 1
    required = (1 << (p * n)) - 1

    @lru_cache(None)
    def separates(value):
        cold = neg_mask ^ (value >> p)
        return sum(cold << (i * n) for i in range(p) if value & (1 << i))

    def sufficient(wires):
        pairs = 0
        for wire in wires:
            pairs |= separates(wire)
        return pairs == required

    @lru_cache(None)
    def search(wires, left):
        if pos_mask in wires:
            return True
        if not left or len(wires) > left + 1 or not sufficient(wires):
            return False
        for i, j in combinations(range(len(wires)), 2):
            a, b = wires[i], wires[j]
            rest = wires[:i] + wires[i + 1:j] + wires[j + 1:]
            for value in (a & b, a | b):
                if value in wires or not separates(value):
                    continue
                # Mark either use as final or keep the operand for a later fanout.
                for retained in ((), (a,), (b,), (a, b)):
                    after = rest + retained + (value,)
                    if len(after) <= left and search(tuple(sorted(after)), left - 1):
                        return True
        return False

    values = sorted({sum(1 << i for i, row in enumerate(rows) if row & s) for s in sources})
    for size in range(1, min(budget + 1, len(values)) + 1):
        for chosen in combinations(values, size):
            if sufficient(chosen) and search(chosen, budget):
                return True
    return False


def check_no_mixing(min_size, max_size):
    for size in range(min_size, max_size + 1):
        survivors = 0
        for edges in combinations(EDGES, size):
            sources = free_sources(edges)
            if sources_suffice(edges, NEG, sources, size - 1):
                survivors += 1
                assert not circuit_exists(edges, sources, size - 2), edges
        print(size, "edges:", survivors, "source tests survived; all excluded", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-size", type=int, choices=range(3, 17), default=3)
    parser.add_argument("--max-size", type=int, choices=range(3, 17), default=16)
    args = parser.parse_args()
    assert args.min_size <= args.max_size
    # Two incident edges form a two-gate star on raw inputs.
    star = (EDGES[0], EDGES[1])
    literals = (1, 1 << 9, 1 << 10)
    assert circuit_exists(star, literals, 2) and not circuit_exists(star, literals, 1)
    check_products()
    check_extra_pairs()
    check_guard()
    check_no_mixing(args.min_size, args.max_size)
