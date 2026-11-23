"""Enumerate normalized five- and six-gate cones for one of three cyclic matchings."""

import argparse
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
from runpy import run_path

source = run_path(str(Path(__file__).with_name("search-three-matchings.py")))
INPUTS = tuple(source["INPUTS"])
TARGETS = tuple(source["targets"]())
MASK = source["MASK"]


def expressions(leaves):
    """Enumerate unordered binary trees; keep subtree lists, stream the root."""
    @lru_cache(None)
    def children(mask):
        return tuple(generate(mask))

    def generate(mask):
        if mask & (mask - 1) == 0:
            yield leaves[mask.bit_length() - 1], ()
            return
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if left < right:
                for a, ga in children(left):
                    for b, gb in children(right):
                        if a == b:
                            continue
                        earlier = ga + gb
                        for value in (a & b, a | b):
                            if value != a and value != b:
                                yield value, earlier + (value,)
            left = (left - 1) & mask
    try:
        yield from generate((1 << len(leaves)) - 1)
    finally:
        children.cache_clear()


def prefixes():
    outputs = {5: set(), 6: set()}

    def record(gates):
        values = frozenset(gates)
        if len(values) == len(gates) and not values.intersection((*INPUTS, 0, MASK)):
            outputs[len(gates)].add(values)

    for value, gates in expressions(INPUTS):
        if value == TARGETS[0]:
            record(gates)
    for size in range(1, 6):
        for indices in combinations(range(6), size):
            outside = tuple(x for i, x in enumerate(INPUTS) if i not in indices)
            for shared, tree in expressions(tuple(INPUTS[i] for i in indices)):
                # The two leaves below denote the one shared signal.
                for value, upper in expressions((*outside, shared, shared)):
                    if value == TARGETS[0]:
                        record(tree + upper)
    return outputs


def symmetries():
    # Simultaneous permutations preserve matching zero and permute the other
    # two (the cyclic group of order three is normal in S3). Side swap does too.
    for perm in permutations(range(3)):
        for flip in (0, 1):
            p = tuple(perm[i % 3] + 3*((i//3)^flip) for i in range(6))
            yield tuple(sum(((row >> i) & 1) << p[i] for i in range(6)) for row in range(64))


def orbits(values):
    actions = list(symmetries())
    def transform(table, action):
        return sum(((table >> i) & 1) << j for i, j in enumerate(action))
    todo = values.copy()
    reps = []
    while todo:
        first = min(todo, key=lambda s: tuple(sorted(s)))
        reps.append(first)
        todo.difference_update(frozenset(transform(v, p) for v in first) for p in actions)
    return reps


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver")
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--case", type=int, choices=range(7))
    args = parser.parse_args()
    for size, values in prefixes().items():
        reps = orbits(values)
        print(f"{size} gates: {len(values)} distinct signal sets, {len(reps)} symmetry classes",
              flush=True)
        if size == 6 and args.solver:
            for i, rep in enumerate(reps):
                if args.case is None or i == args.case:
                    print(f"Six-gate class {i}", flush=True)
                    source["synthesize"](args.solver, 1, 14, args.seconds, True, sorted(rep))
