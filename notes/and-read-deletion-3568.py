"""Check the twelve-active-vertex boundary for L-meta-3568 with Python 3."""
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import runpy

previous = runpy.run_path(str(Path(__file__).with_name("incidence-exits-3491.py")))
graph = previous["graph"]


@lru_cache(maxsize=None)
def relabelings(degrees):
    # Sorting the left shore by degree leaves only within-class ties to try.
    groups = [tuple(i for i,d in enumerate(degrees) if d == k) for k in sorted(set(degrees))]
    orders = [sum(parts, ()) for parts in product(*(permutations(g) for g in groups))]
    return [tuple(sum(((m >> v) & 1) << i for i,v in enumerate(order)) for m in range(64))
            for order in orders]


def canonical(rows):
    degrees = tuple(sum((m >> i) & 1 for m in rows) for i in range(6))
    return min(tuple(sorted(mapping[m] for m in rows)) for mapping in relabelings(degrees))


def transpose(rows):
    return tuple(sum(((m >> i) & 1) << j for j,m in enumerate(rows)) for i in range(6))


def catalogue():
    current = {()}
    for _ in range(6):
        following = set()
        for rows in current:
            for m in range(1,64):
                # Two common neighbors are precisely a four-cycle. Repeated
                # singleton rows are legal and have not been excluded.
                if all((m & r).bit_count() <= 1 for r in rows):
                    following.add(canonical(rows + (m,)))
        current = following
    return {min(rows,canonical(transpose(rows))) for rows in current
            if graph["matching"](graph["parts"]((6,rows))[2]) == 6}


@lru_cache(maxsize=None)
def proper_bound(code):
    edges = graph["parts"](code)[2]
    t = graph["matching"](edges)
    assert t <= 5
    return len(edges) + t - 1 if edges else 0


def classify(masks):
    code = (6,masks)
    edges = graph["parts"](code)[2]
    adj = graph["neighbors"](edges)
    for neighbors in adj.values():
        if len(neighbors) == 1:
            parent, = neighbors
            if len(adj[parent]) <= 2 or sum(len(adj[v]) == 1 for v in adj[parent]) >= 2:
                return "leaf peeling"
    groups = graph["components"](edges)
    if all(any(max(len(adj[v]) for v in group if (v < 6) == side) <= 2
               for side in (True,False)) for group in groups):
        return "subdivisions"
    if all(sum(len(adj[v]) for v in group) <= 2*len(group) for group in groups):
        return "pseudoforests"
    if min(map(len,adj.values())) >= 2 and len(edges) == len(adj)+1:
        return "one excess edge"
    target = len(edges)+5
    if graph["bound"].__wrapped__(code) >= target:
        return "restriction"
    options = previous["surviving"](masks,target-1,6)
    return "shared-wire count" if options is not None and options[1] == 0 else "open"


if __name__ == "__main__":
    rows = catalogue()
    assert len(rows) == 385
    # The old recurrence must consult the established five-cover result on
    # every proper pin, including pins inside the shared-wire calculation.
    scope = graph["bound"].__wrapped__.__globals__
    original = scope["bound"]
    scope["bound"] = proper_bound
    try:
        classes = {row: classify(row) for row in rows}
    finally:
        scope["bound"] = original
    counts = Counter(classes.values())
    assert counts == {"leaf peeling":282, "subdivisions":2, "pseudoforests":7,
                      "one excess edge":4, "shared-wire count":53, "open":37}
    for category in sorted(counts):
        print(category, counts[category])
    print("Unresolved six-by-six incidence masks", sorted(r for r,c in classes.items() if c == "open"))
