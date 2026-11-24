"""Monotone first-gate and forest lower bounds on induced Heawood subgraphs."""
from functools import lru_cache
from itertools import combinations


EDGES = ((0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11))
N = 14
ALL = (1 << N) - 1
ADJ = [0] * N
for a, b in EDGES:
    ADJ[a] |= 1 << b
    ADJ[b] |= 1 << a


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def size(mask):
    return bin(mask).count("1")


@lru_cache(None)
def support(mask):
    return sum(1 << v for v in vertices(mask) if mask & ADJ[v])


@lru_cache(None)
def matching(mask):
    for a in vertices(mask):
        if a >= 7:
            break
        rest = mask ^ (1 << a)
        return max([matching(rest)] + [1 + matching(rest ^ (1 << b))
                   for b in vertices(rest & ADJ[a])])
    return 0


def forest(mask):
    todo = mask
    while todo:
        leaf = next((v for v in vertices(todo) if size(todo & ADJ[v]) <= 1), None)
        if leaf is None:
            return False
        todo ^= 1 << leaf
    return True


@lru_cache(None)
def slice_at(mask, v, bit):
    rest = mask ^ (1 << v)
    singles = rest & ADJ[v] if bit else 0
    graph = support(rest & ~singles)
    cost = lower(graph) + size(singles) if graph else max(0, size(singles) - 1)
    return graph | singles, cost


def first(mask, p, q, control):
    # The controlling restriction deletes the first gate and one consumer.
    # A bypass exists when the input stays essential with the other pinned.
    result = 0
    for u, v in ((p, q), (q, p)):
        bypass = bool(slice_at(mask, v, control)[0] & (1 << u))
        for bit in (0, 1):
            _, residual = slice_at(mask, u, bit)
            result = max(result, residual + 1 + bypass + (bit == control))
    return result


@lru_cache(None)
def lower(mask):
    mask2 = support(mask)
    if mask != mask2:
        return lower(mask2)
    if not mask:
        return 0
    if forest(mask):
        edges = sum(size(ADJ[v] & mask) for v in vertices(mask)) // 2
        return edges + matching(mask) - 1
    width = size(mask)
    bound = width - 1
    for v in vertices(mask):
        for bit in (0, 1):
            used, residual = slice_at(mask, v, bit)
            # Pin newly irrelevant variables as well. The result must be nonconstant.
            if used:
                bound = max(bound, residual + width - size(used))
    first_gate = min(first(mask, p, q, c) for p, q in combinations(vertices(mask), 2)
                     for c in (False, True))
    return max(bound, first_gate)


if __name__ == "__main__":
    assert len(EDGES) == 21 and matching(ALL) == 7
    full = lower(ALL)
    print("Unrestricted monotone lower bound:", full)
    print("With one point pinned to zero or one:", [slice_at(ALL, 0, b)[1] for b in (0, 1)])
    # Adding the free OR at the front costs one gate. A circuit that uses it may
    # fail to be globally minimum; the first-gate lemma requires minimality.
    print("When an unrestricted minimum begins with OR(0,1):", first(ALL, 0, 1, True))
    print("Universal paid lower bound with OR(0,1) free:",
          min(full + 1, first(ALL, 0, 1, True)) - 1)
