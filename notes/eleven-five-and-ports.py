"""Enumerate necessary raw-port patterns for a five-AND realization with free OR."""
from itertools import combinations
from pathlib import Path
from runpy import run_path

data = run_path(str(Path(__file__).with_name("eleven-dirty-search.py")))
edges = {frozenset(e) for e in data["EDGES"]}
negative = data["NEG"]
counts = [sum(bool(row & (1<<v)) for row in negative) for v in range(11)]
limits = [5 - (c-1).bit_length() for c in counts]
remaining = [v for v in range(11) if limits[v] == 2]
assert len(negative) == 24 and limits == [1]*4 + [2]*7


def embeddings(ports, forced, size):
    order = sorted(range(size),key=lambda v:-sum(v in e for e in forced))
    mapping = {}
    def visit():
        if len(mapping) == size:
            yield tuple(sorted(sum(1<<mapping[v] for v in p) for p in ports))
            return
        v = order[len(mapping)]
        for label in remaining:
            if label in mapping.values():
                continue
            if any(frozenset((v,w)) in forced and frozenset((label,other)) not in edges
                   for w,other in mapping.items()):
                continue
            mapping[v] = label
            yield from visit()
            del mapping[v]
    yield from visit()


def check():
    patterns = set()
    abstract_count = 0
    # Each surviving variable occurs in two ports. Two ports meet in at most
    # one variable, so a variable is an edge of a simple graph on the ports.
    for t in range(3,7):
        pairs = list(combinations(range(t),2))
        for size in range(t+1,8):
            for chosen in combinations(pairs,size):
                ports = [{v for v,e in enumerate(chosen) if j in e} for j in range(t)]
                if min(map(len,ports)) < 2:
                    continue
                abstract_count += 1
                forced = {frozenset((x,y)) for v,(a,b) in enumerate(chosen)
                          for x in ports[a]-{v} for y in ports[b]-{v}}
                patterns.update(embeddings(ports,forced,size))
    assert abstract_count == 1182 and patterns == {(144,320,592,1408,1536)}
    for ports in patterns:
        assert not any(p & (1<<4) and p & (1<<8) for p in ports)
    assert {next(iter(e-{1})) for e in edges if 1 in e} == {4,8}
    print("24 maximal negatives; raw port bounds",limits)
    print(abstract_count,"simple port graphs and one possible labeled core",patterns)
    print("No partner for the singleton input 1 covers both required edges.")


if __name__ == "__main__":
    check()
