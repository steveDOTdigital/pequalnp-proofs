"""Check local simplifications for edge functions with a single repeated input."""
from functools import lru_cache
from itertools import combinations


def raw_tables(n):
    return [sum(1 << row for row in range(1 << n) if row & (1 << v)) for v in range(n)]


def partitions(mask, repeats):
    """One unordered split of the private labels and the repeated copies of input zero."""
    first = mask
    while True:
        for k in range(repeats + 1):
            left = (first, k)
            right = (mask ^ first, repeats - k)
            if left != (0, 0) and right != (0, 0) and left <= right:
                yield left, right
        if not first:
            break
        first = (first - 1) & mask


def graph_bounds(n, raw):
    pairs = list(combinations(range(n), 2))
    bounds = {}
    for mask in range(1, 1 << len(pairs)):
        edges = [e for i, e in enumerate(pairs) if mask & (1 << i)]
        neighbors = [set() for _ in range(n)]
        for u, v in edges:
            neighbors[u].add(v)
            neighbors[v].add(u)
        if not all(neighbors) or any(len(neighbors[u] & neighbors[v]) > 1 for u, v in pairs):
            continue
        if not any(all(((s >> u) ^ (s >> v)) & 1 for u, v in edges) for s in range(1 << n)):
            continue
        cover = min(s.bit_count() for s in range(1 << n)
                    if all(((s >> u) | (s >> v)) & 1 for u, v in edges))
        target = 0
        for u, v in edges:
            target |= raw[u] & raw[v]
        bounds[target] = len(edges) + cover - 1
    return bounds


def count_graph_cases(n, max_repeats):
    raw = raw_tables(n)
    bounds = graph_bounds(n, raw)

    @lru_cache(None)
    def tables(mask, k):
        if mask.bit_count() + k == 1:
            return {raw[mask.bit_length() - 1 if mask else 0]: 0}
        result = {}
        for left, right in partitions(mask, k):
            for a, active_a in tables(*left).items():
                for b, active_b in tables(*right).items():
                    active = active_a | active_b
                    meet, join = a & b, a | b
                    # Union over all realizations preserves existential evidence of a dirty AND.
                    result[meet] = result.get(meet, 0) | active | meet
                    result[join] = result.get(join, 0) | active
        return result

    represented = dirty = 0
    for k in range(1, max_repeats + 1):
        for target, active in tables((1 << n) - 2, k).items():
            if target not in bounds:
                continue
            represented += 1
            if active & ~target:
                dirty += 1
                assert bounds[target] < n + k - 2
    return represented, dirty


def check_tree_edits():
    # Actual formulas, including targets with singleton minterms and arbitrary graph edges.
    n = 4
    raw = raw_tables(n)
    full = (1 << (1 << n)) - 1
    nodes = []
    truth, below_test, edits = [], [], []
    names = {}

    def node(op, i, j):
        key = (op, i, j)
        if key in names:
            return names[key]
        idx = names[key] = len(nodes)
        nodes.append(key)
        if op == "input":
            truth.append(raw[i])
            below_test.append(0)
            edits.append(set())
            return idx
        combine = int.__and__ if op == "and" else int.__or__
        t = combine(truth[i], truth[j])
        truth.append(t)
        below_test.append(below_test[i] | below_test[j] | (t if op == "and" else 0))
        # Every candidate uses fewer gates. A nonconstant pin discards at least one
        # gate only when the subtree syntactically contains the pinned input.
        candidates = {truth[i], truth[j], raw[0]}
        if (contains_zero(i) or contains_zero(j)):
            for pin in (0, 1):
                cofactor = sum(1 << r for r in range(1 << n) if t & (1 << ((r & ~1) | pin)))
                if cofactor not in (0, full):
                    candidates.add(cofactor)
        candidates.update(combine(u, truth[j]) for u in edits[i])
        candidates.update(combine(truth[i], u) for u in edits[j])
        edits.append(candidates)
        return idx

    @lru_cache(None)
    def contains_zero(i):
        op, u, v = nodes[i]
        return u == 0 if op == "input" else contains_zero(u) or contains_zero(v)

    @lru_cache(None)
    def trees(mask, k):
        if mask.bit_count() + k == 1:
            return [node("input", mask.bit_length()-1 if mask else 0, -1)]
        result = set()
        for left, right in partitions(mask, k):
            for i in trees(*left):
                for j in trees(*right):
                    a, b = sorted((i, j))
                    result.update((node("and", a, b), node("or", a, b)))
        return sorted(result)

    @lru_cache(None)
    def eligible(t):
        minterms = [r for r in range(1 << n) if t & (1 << r)
                    and all(not t & (1 << (r ^ (1 << i))) for i in range(n) if r & (1 << i))]
        return (all(r.bit_count() <= 2 for r in minterms)
                and all(any(r & (1 << i) for r in minterms) for i in range(n)))

    total = dirty = 0
    for k in (1, 2, 3):
        for root in trees(14, k):
            t = truth[root]
            if eligible(t):
                total += 1
                if below_test[root] & ~t:
                    dirty += 1
                    assert t in edits[root]
    return total, dirty


if __name__ == "__main__":
    results = [count_graph_cases(n, k) for n, k in ((3, 5), (4, 5), (5, 4), (6, 4))]
    print("Labeled graph and occurrence-count cases:", results)
    print("Rank-two formulas and dirty formulas with a verified smaller edit:", check_tree_edits())
