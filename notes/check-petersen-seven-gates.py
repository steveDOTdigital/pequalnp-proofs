"""Classify the outside-signal truth tables of seven endpoint-dependent gates."""

from itertools import combinations, permutations


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


def classify(count, kind, require_both=False):
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
            for flip in range(contexts):
                image = tuple(row[i ^ flip] for i in permuted)
                unclassified.discard(image)
                unclassified.discard(tuple({10: 12, 12: 10}.get(r, r) for r in image))
    return len(patterns), representatives


if __name__ == "__main__":
    for count, kind, expected in [(3, "not", (36, 2)), (3, "fanout", (102, 10)),
                                  (4, "tree", (864, 22))]:
        total, reps = classify(count, kind)
        assert (total, len(reps)) == expected
        print(kind, total, "tables in", len(reps), "classes")
        strong_total, strong = classify(count, kind, require_both=True)
        assert (strong_total, len(strong)) == ((0, 0) if kind == "not" else expected)
        print("Requiring sensitivity to both constant replacements:", len(strong), "classes")
        for r in reps:
            print(" ".join(str(x) if x != INVALID else "-" for x in r))
