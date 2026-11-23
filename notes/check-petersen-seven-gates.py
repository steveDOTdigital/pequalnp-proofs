"""Classify the outside-signal truth tables of seven endpoint-dependent gates."""

import argparse
import subprocess
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
from runpy import run_path


ROWS = {0, 10, 12, 14, 15}
INVALID = -1


def trees(leaves, full, one_not=False):
    """Packed tables of all read-once binary trees; optionally insert one NOT."""
    normal, negated = {}, {}
    for mask in range(1, 1 << len(leaves)):
        if mask & (mask - 1) == 0:
            value = leaves[mask.bit_length() - 1]
            normal[mask] = {value}
            if one_not:
                negated[mask] = {full ^ value}
            continue
        yes, no = set(), set()
        left = (mask - 1) & mask
        while left:
            right = mask ^ left
            if left < right:
                pairs = [(normal[left], normal[right], no)]
                if one_not:
                    pairs += [(negated[left], normal[right], yes),
                              (normal[left], negated[right], yes)]
                for a_values, b_values, target in pairs:
                    for a in a_values:
                        for b in b_values:
                            target.add(a & b)
                            target.add(a | b)
            left = (left - 1) & mask
        normal[mask] = no
        if one_not:
            yes.update(full ^ v for v in no)
            negated[mask] = yes
    return (negated if one_not else normal)[(1 << len(leaves)) - 1]


def prune_with_formulas(patterns, count):
    """Remove tables implemented on every valid row by a six-gate formula."""
    contexts = 1 << count
    full = (1 << (4 * contexts)) - 1
    leaves = [12 * (full // 15), 10 * (full // 15)]
    leaves.extend(sum(15 << (4*i) for i in range(contexts) if i & (1 << j))
                  for j in range(count))
    remaining = patterns.copy()
    # Six binary gates allow seven leaf occurrences. All outside wires keep
    # their actual phases, and the replacement does not use the first OR.
    for repeats in range(8 - len(leaves)):
        for extra in combinations_with_replacement(leaves, repeats):
            by_mask = {}
            for p in remaining:
                mask = sum(15 << (4*i) for i, r in enumerate(p) if r != INVALID)
                bits = sum(r << (4*i) for i, r in enumerate(p) if r != INVALID)
                by_mask.setdefault(mask, {})[bits] = p
            outputs = trees(leaves + list(extra), full)
            for mask, wanted in by_mask.items():
                hits = {bits & mask for bits in outputs} & wanted.keys()
                remaining.difference_update(wanted[bits] for bits in hits)
    return remaining


def classify(count, kind, require_both=False, shorten=False, signed=True):
    contexts = 1 << count
    width = 4 * contexts
    half = (1 << width) - 1
    full = (1 << (3 * width)) - 1

    def same(bits):
        return bits | (bits << width) | (bits << (2 * width))

    unit = half // 15
    leaves = [same(12 * unit), same(10 * unit), 14 * unit | (half << width)]
    for j in range(count):
        leaves.append(same(sum(15 << (4*i) for i in range(contexts) if i & (1 << j))))
    patterns = set()

    def collect(tables):
        for t in tables:
            actual, forced = t & half, (t >> width) & half
            if actual == forced:
                continue
            rows = tuple((actual >> (4*i)) & 15 for i in range(contexts))
            if not ROWS.issubset(rows):
                continue
            if require_both:
                zero = t >> (2 * width)
                if all(r not in ROWS or r == ((zero >> (4*i)) & 15)
                       for i, r in enumerate(rows)):
                    continue
            if any(r in ROWS and r != ((forced >> (4*i)) & 15) for i, r in enumerate(rows)):
                patterns.add(tuple(r if r in ROWS else INVALID for r in rows))

    if kind == "fanout":
        for size in range(1, len(leaves) + 1):
            for group in combinations(range(len(leaves)), size):
                inside = [leaves[i] for i in group]
                outside = [v for i, v in enumerate(leaves) if i not in group]
                for repeated in trees(inside, full):
                    collect(trees(outside + [repeated, repeated], full))
    else:
        collect(trees(leaves, full, one_not=kind == "not"))

    if shorten:
        patterns = prune_with_formulas(patterns, count)

    # Quotient by permutations and complements of signal coordinates and by
    # swapping the two endpoints. Complements here relabel signals only.
    unclassified = patterns.copy()
    representatives = []
    while unclassified:
        row = min(unclassified)
        representatives.append(row)
        for perm in permutations(range(count)):
            permuted = [sum(((i >> j) & 1) << perm[j] for j in range(count))
                        for i in range(contexts)]
            for flip in range(contexts if signed else 1):
                image = tuple(row[i ^ flip] for i in permuted)
                unclassified.discard(image)
                unclassified.discard(tuple({10: 12, 12: 10}.get(r, r) for r in image))
    return len(patterns), representatives


def exclude_six(row, count, solver):
    encode = run_path(str(Path(__file__).with_name("search-petersen-first-or.py")))["truth_instance"]
    n = count + 2
    rows = [x for x in range(1 << n) if row[x // 4] != INVALID]
    inputs = [sum(((x >> j) & 1) << x for x in range(1 << n)) for j in range(n)]
    target = sum(bits << (4*i) for i, bits in enumerate(row) if bits != INVALID)
    formula, _ = encode(rows, inputs, 6, target)
    result = subprocess.run([solver, "-q", "--check", "--checkproof=2", "-t", "60"],
                            input=formula.dimacs(), text=True, capture_output=True, timeout=80)
    if result.returncode != 20 or "s UNSATISFIABLE" not in result.stdout:
        raise RuntimeError(("six-gate exclusion inconclusive", result.returncode, row))


def minimum_nonmonotone(row, count, solver):
    """Find the fewest outside coordinates that must violate monotonicity."""
    data = run_path(str(Path(__file__).with_name("search-petersen-first-or.py")))
    vertices = [1, 3, 4, 5, 6, 7, 8, 9]
    labels = []
    for y in range(256):
        x = sum(((y >> i) & 1) << v for i, v in enumerate(vertices))
        labels.append(sum(((data["TARGET"] >> (x | (p >> 1) | ((p & 1) << 2))) & 1) << p
                          for p in range(4)))
    for size in range(count + 1):
        for free in combinations(range(count), size):
            formula = data["Formula"]()
            wires = [formula.vars(count) for _ in labels]
            for y, label in enumerate(labels):
                for z, r in enumerate(row):
                    if r != label:
                        formula.clauses.append([-v if z & (1 << i) else v
                                                for i, v in enumerate(wires[y])])
                for j in range(8):
                    if not y & (1 << j):
                        for i in range(count):
                            if i not in free:
                                formula.clauses.append([-wires[y][i], wires[y | (1 << j)][i]])
            result = subprocess.run([solver, "-q", "--check", "--checkproof=2", "-t", "60"],
                                    input=formula.dimacs(), text=True, capture_output=True, timeout=80)
            if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
                continue
            if result.returncode != 10 or "s SATISFIABLE" not in result.stdout:
                raise RuntimeError(("outside monotonicity check inconclusive", result.returncode))
            model = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
                     for v in line.split()[1:]}
            images = [sum((v in model) << i for i, v in enumerate(w)) for w in wires]
            assert all(row[z] == label for z, label in zip(images, labels))
            required = sum(1 << i for i in range(count) if i not in free)
            assert all(not (images[y] & ~images[y | (1 << j)] & required)
                       for y in range(256) for j in range(8))
            return size
    raise AssertionError("no encoding of the five rows")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", help="also prove sharpness for all rows in each remaining table")
    args = parser.parse_args()
    for count, kind, expected in [(3, "not", (36, 2)), (3, "fanout", (102, 10)),
                                  (4, "tree", (864, 22))]:
        total, reps = classify(count, kind)
        assert (total, len(reps)) == expected
        print(kind, total, "tables in", len(reps), "classes")
        strong_total, strong = classify(count, kind, require_both=True)
        assert (strong_total, len(strong)) == ((0, 0) if kind == "not" else expected)
        print("Requiring sensitivity to both constant replacements:", len(strong), "classes")
        survivors, final = classify(count, kind, require_both=True, shorten=True, signed=False)
        assert (survivors, len(final)) == {"not": (0, 0), "fanout": (18, 2),
                                           "tree": (336, 9)}[kind]
        print("After six-gate replacements:", survivors, "tables in", len(final), "classes")
        for index, r in enumerate(final):
            print(" ".join(str(x) if x != INVALID else "-" for x in r))
            if args.solver:
                exclude_six(r, count, args.solver)
                needed = minimum_nonmonotone(r, count, args.solver)
                assert needed == int(index in ({1} if count == 3 else {1, 3, 5}))
                print("Minimum nonmonotone outside signals:", needed)
