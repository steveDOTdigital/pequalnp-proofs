"""Check six-point cores for the saturated fanout argument in singleton-high-pin.md."""
from itertools import combinations
from pathlib import Path
import runpy

helpers = runpy.run_path(str(Path(__file__).with_name('five-cover-singleton-pins.py')))
canonical = helpers['compressed']
lower = helpers['bound']
neighbors = helpers['neighbors']

def main():
    points = range(6)
    triple = (0, 1, 2)
    pairs = [pair for pair in combinations(points, 2) if not set(pair) <= set(triple)]
    results = {}
    for chosen in combinations(pairs, 8):
        lines = (triple, *chosen)
        edges = {(v, 6+i) for i, line in enumerate(lines) for v in line}
        adj = neighbors(edges)
        if min(len(adj[v]) for v in points) < 3:
            continue
        if any(len(set.union(*(adj[v] for v in subset))) < k+2
               for k in range(1, 7) for subset in combinations(points, k)):
            continue
        code = canonical(edges)
        if code in results:
            continue
        point_costs, leaf_costs = [], []
        for v in points:
            without = {e for e in edges if v not in e}
            residual = {e for e in without if adj[v].isdisjoint(e)}
            assert residual and len(edges) == 19 and len(adj) == 15
            point_costs.append(lower(canonical(residual)) + len(adj[v]))
            leaf_costs.append(1 + lower(canonical(without)))
        masks = tuple(sorted(sum(1 << v for v in line) for line in lines))
        results[code] = (min(point_costs), min(leaf_costs), masks)
    assert sorted((p, l) for p, l, _ in results.values()) == [(18,20),(19,20),(19,20)]
    for p, l, masks in results.values():
        print(masks, 'minimum point-high cost', p, 'minimum new leaf-high cost', l)

if __name__ == '__main__':
    main()
