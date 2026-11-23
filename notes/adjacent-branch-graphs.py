"""Check the finite obstructions when a graph has two adjacent branch vertices."""

from collections import Counter
from itertools import combinations


def paths_graph(paths):
    n = 1 + max(v for path in paths for v in path)
    adj = [set() for _ in range(n)]
    for path in paths:
        for v,w in zip(path,path[1:]):
            adj[v].add(w)
            adj[w].add(v)
    return adj


def has_reduction(adj):
    def run(path):
        if len(path) == 6:
            return True
        return any(run(path+[w]) for w in adj[path[-1]] if w not in path and len(adj[w]) <= 2)
    for v,ns in enumerate(adj):
        if len(ns) == 1:
            p, = ns
            if len(adj[p]) <= 2 or any(w != v and len(adj[w]) == 1 for w in adj[p]):
                return True
        if len(ns) <= 2 and run([v]):
            return True
    return False


def measures(adj):
    edges = [(1 << i) | (1 << j) for i,ns in enumerate(adj) for j in ns if i < j]
    cover = min(bin(c).count("1") for c in range(1 << len(adj)) if all(c & e for e in edges))
    return len(edges),cover


def restrictions(adj):
    counts = Counter()
    for mask in range(1 << len(adj)):
        sub = [{j for j in ns if mask & (1 << j)} if mask & (1 << i) else set()
               for i,ns in enumerate(adj)]
        if not any(sub) or has_reduction(sub):
            continue
        active = sum(bool(row) for row in sub)
        edges,cover = measures(sub)
        degrees = Counter(map(len,(row for row in sub if row)))
        if active == 9:
            assert (edges,cover,degrees) == (9,4,{1:2,2:5,3:2})
            leaves = [i for i,ns in enumerate(sub) if len(ns) == 1]
            core = [ns.difference(leaves) if i not in leaves else set() for i,ns in enumerate(sub)]
            assert measures(core) == (7,4)
            first,second = [next(iter(sub[i])) for i in leaves]
            assert second in sub[first] and all(not ns or len(ns)==2 for ns in core)
        else:
            assert active == 12 and (edges,cover) == (13,6)
        counts[(active,edges,cover)] += 1
    return counts


if __name__ == "__main__":
    theta = paths_graph([[0,1], [0,2,3,4,5,6,1], [0,7,8,9,10,11,1]])
    decorated_cycle = paths_graph([[0,1,2,3,4,5,6,0], [0,7], [1,8]])
    broken = [ns - {4} if i != 4 else set() for i,ns in enumerate(theta)]
    assert measures(broken) == (11,6)
    print("Decorated seven-cycle:",restrictions(decorated_cycle))
    print("Theta:",restrictions(theta))
    print("Deleting the middle of a long path leaves eleven edges and cover number six.")
