"""Check L-meta-908 for five-gate circuits with at most one internal AND gate."""

from collections import defaultdict


EDGES = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5),
         (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)]
EDGE_MASKS = [(1 << a) | (1 << b) for a, b in EDGES]
RAW_MASK = (1 << 9) - 1
INTERNAL = 1 << 9


def independent(vertices):
    return all(vertices & edge != edge for edge in EDGE_MASKS)


def traces(points):
    """A raw OR's bit table on the given points, indexed by its nine input bits."""
    return [sum(1 << i for i, vertices in enumerate(points) if vertices & raw)
            for raw in range(1 << 9)]


def maximal_masks(masks):
    maximal = []
    for mask in sorted(set(masks), key=int.bit_count, reverse=True):
        if all(mask & ~other for other in maximal):
            maximal.append(mask)
    return maximal


def maximal_gates(compatible, positive, all_positive):
    """Complete each left side to the largest safe right side, and then back."""
    def common_neighbors(side):
        result = (1 << len(compatible)) - 1
        for i, neighbors in enumerate(compatible):
            if side & (1 << i):
                result &= neighbors
        return result

    pairs = set()
    for left in range(1, 1 << len(compatible)):
        right = common_neighbors(left)
        if right:
            pairs.add(tuple(sorted((common_neighbors(right), right))))

    # On each positive point, distinguish the two possible internal signal values.
    result = []
    for left, right in pairs:
        raw_left, raw_right = positive[left & RAW_MASK], positive[right & RAW_MASK]
        zero = raw_left & raw_right
        one = ((all_positive if left & INTERNAL else raw_left)
               & (all_positive if right & INTERNAL else raw_right))
        result.append((zero, one))
    return result


def can_cover(terms, count, all_positive):
    terms = maximal_masks(terms)
    rows = [sum(1 << i for i, term in enumerate(terms) if term & (1 << j))
            for j in range(all_positive.bit_length())]
    constraints = sorted(set(rows), key=int.bit_count)

    def search(chosen, left):
        for row in constraints:
            if not chosen & row:
                if left == 0:
                    return False
                while row:
                    gate = row & -row
                    row -= gate
                    if search(chosen | gate, left - 1):
                        return True
                return False
        return True

    return search(0, count)


def main():
    negative = [x for x in range(512) if independent(x) and
                all(not independent(x | (1 << v)) for v in range(9) if not x & (1 << v))]
    additions = [x | (1 << v) for x in negative for v in range(9) if not x & (1 << v)]
    positive = sorted(set(additions))
    assert (len(negative), len(additions), len(positive)) == (16, 96, 67)
    no, yes = traces(negative), traces(positive)
    all_positive = (1 << len(positive)) - 1
    inputs = [no[1 << i] for i in range(9)]
    raw_neighbors = [sum(1 << j for j, other in enumerate(inputs) if not signal & other)
                     for signal in inputs]

    # Five terminal gates. C4-freeness makes each safe raw biclique a star.
    least_centers = min(s.bit_count() for s in range(512)
                        if all(any(edge & s and point & edge == edge for edge in EDGE_MASKS)
                               for point in positive))
    assert least_centers == 6

    # The one internal gate H has two arbitrary raw OR sides. For output safety
    # it suffices to know which individual signals it can co-occur with.
    groups = defaultdict(set)
    for left in range(512):
        for right in range(left + 1):
            negative_trace = no[left] & no[right]
            neighbors = sum(1 << i for i, raw in enumerate(inputs) if not raw & negative_trace)
            groups[neighbors, bool(negative_trace)].add(yes[left] & yes[right])

    survivors = 0
    for (neighbors, ever_negative), positive_traces in groups.items():
        rows = [row | (INTERNAL if neighbors & (1 << i) else 0)
                for i, row in enumerate(raw_neighbors)]
        rows.append(neighbors | (0 if ever_negative else INTERNAL))
        gates = maximal_gates(rows, yes, all_positive)
        for signal in maximal_masks(positive_traces):
            survivors += 1
            assert not can_cover([zero | (signal & one) for zero, one in gates], 4, all_positive)
    print(f"{len(negative)} negatives, {len(positive)} distinct positives from {len(additions)} additions")
    print(f"Parallel gates require {least_centers} star centers")
    print(f"{len(groups)} compatibility relations, {survivors} maximal internal traces, no four-gate cover")


if __name__ == "__main__":
    main()
