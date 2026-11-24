"""Cross-check the seven-vertex reduction for L-meta-4131 on every deleted-edge set."""
from collections import Counter

EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
PORTS = 15  # Vertices 0 to 3 are independent in the original graph.
def count(bits):
    return bin(bits).count("1")

def internal(vertices):
    return sum(1 << i for i,(u,v) in enumerate(EDGES)
               if vertices & (1 << u) and vertices & (1 << v))

def main():
    all_vertices = range(1 << 11)
    independent_four = [s for s in all_vertices if count(s) == 4 and not internal(s)]
    contains_four = [any(s & witness == witness for witness in independent_four) for s in all_vertices]
    assert len(independent_four) == 22
    # Direct definition: a residual independent superset of four original independent vertices.
    direct = [0] * (1 << 16)
    for s in all_vertices:
        if contains_four[s]:
            removed = internal(s)
            direct[removed] = max(direct[removed], count(s) - 4)
    for index in range(16):
        edge = 1 << index
        for deleted in range(1 << 16):
            if edge & deleted:
                direct[deleted] = max(direct[deleted], direct[deleted ^ edge])

    cores = []
    for compressed in range(128):
        core = compressed << 4
        boundary = [sum(1 << j for j,(v,w) in enumerate(EDGES)
                        if v == a and core & (1 << w)) for a in range(4)]
        cores.append((core, internal(core), boundary))

    excess = Counter()
    worst = [0]*17
    for deleted in range(1 << 16):
        best = unrestricted = 0
        for core, required, boundary in cores:
            if required & ~deleted:
                continue
            free_ports = sum(1 << v for v, crossing in enumerate(boundary) if not (crossing & ~deleted))
            completed = core | free_ports
            deficit = count(completed) - 4
            unrestricted = max(unrestricted, deficit)
            if contains_four[completed]:
                best = max(best, deficit)
        assert best == direct[deleted], (deleted,best,direct[deleted])
        excess[unrestricted-best] += 1
        worst[count(deleted)] = max(worst[count(deleted)],best)
    assert excess == {0:65519,1:17}
    print("All 65536 deletion patterns agree. Unrestricted excess:",dict(excess))
    print("Largest possible deficit by number of deleted edges:",worst)

if __name__ == "__main__":
    main()
