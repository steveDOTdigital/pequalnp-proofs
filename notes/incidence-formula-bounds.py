"""Reproduce the finite formula bounds for desk cases 9757 and 9807."""
from functools import lru_cache
from pathlib import Path
from runpy import run_path
from types import FunctionType


NOTES = Path(__file__).resolve().parent
FANO = run_path(str(NOTES / "heawood-signed-formulas.py"))
PLANE_EDGES = [(i, 13 + (i + delta) % 13)
               for i in range(13) for delta in (0, 4, 10, 12)]
NEIGHBORS = [sorted(b if a == v else a for a, b in PLANE_EDGES if v in (a, b))
             for v in range(26)]
assert len(PLANE_EDGES) == 52 and all(len(row) == 4 for row in NEIGHBORS)


def count(mask):
    return bin(mask).count("1")


def local_bits(vertex, vertices):
    return sum(((vertices >> w) & 1) << i for i, w in enumerate(NEIGHBORS[vertex]))


@lru_cache(None)
def contribution(clean, mixed, allowed, forced, nonempty):
    best = 20
    for owned in range(16):
        if owned & ~allowed or forced & ~owned or (nonempty and not owned):
            continue
        for reads in range(1 + int(mixed), 5):
            masks = FANO["local_masks"](reads, clean, 4)
            if any(dominated & ~owned == 0 for dominated in masks):
                best = min(best, reads - 4 + count(owned))
                break
    return best


def small_covers():
    shore = (1 << 13) - 1
    all_vertices = (1 << 26) - 1
    for points in range(1 << 13):
        blocked = 0
        for v in range(13):
            if points >> v & 1:
                for w in NEIGHBORS[v]:
                    blocked |= 1 << (w - 13)
        available = shore ^ blocked
        lines = available
        while True:
            independent = points | (lines << 13)
            cover = all_vertices ^ independent
            if count(cover) <= 20:
                yield cover, [local_bits(v, independent) for v in range(26)]
            if not lines:
                break
            lines = (lines - 1) & available


def positive_floor(mixed_vertices, covers):
    mixed = sum(1 << v for v in mixed_vertices)
    clean = [15 ^ local_bits(v, mixed) for v in range(26)]

    def price(v, forced, owner):
        return contribution(clean[v], (mixed >> v) & 1, 15 if owner else 0,
                            forced if owner else 0, owner)

    # A larger cover pays at least 21 before local losses. Each local loss
    # is maximized over being outside or inside, with no forced incidences.
    losses = [max(0, -price(v, 0, False), 1 - price(v, 0, True)) for v in range(26)]
    answer = 52 + 21 - sum(losses)
    for cover, outside in covers:
        bound = 52 + sum(price(v, outside[v], bool((cover >> v) & 1)) for v in range(26))
        answer = min(answer, bound)
    return answer


def punctured_fano():
    edges = [e for e in FANO["EDGES"] if e not in {(0, 7), (0, 8)}]
    assert len(edges) == 19
    edge_set = set(edges)
    group = [g for g in FANO["automorphisms"]()
             if {tuple(sorted((g[a], g[b]))) for a, b in edges} == edge_set]
    original = FANO["check_induced"]
    check = FunctionType(original.__code__, dict(original.__globals__, EDGES=edges))
    leaves = check((1 << 14) - 1, group)
    assert leaves == 26
    # The seven point stars use 19 incidence operands and seven point operands.
    assert len(edges) + len({a for a, _ in edges}) - 1 == 25
    print("9807: minimum signed formula uses 26 leaves and 25 binary gates.")


if __name__ == "__main__":
    punctured_fano()
    covers = list(small_covers())
    assert len(covers) == 23168
    for mixed, expected in [((), 65), ((0,), 64), ((13,), 64), ((0, 1), 62),
                            ((0, 13), 63), ((0, 15), 61), ((0, 1, 2), 59),
                            ((0, 1, 13), 59)]:
        positive = positive_floor(mixed, covers)
        assert positive == expected
        print("9757:", mixed, "positive leaves >=", positive,
              "all leaves >=", positive + len(mixed))
