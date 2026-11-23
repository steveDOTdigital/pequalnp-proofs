"""Bound the support size of a complex permanent level space.

On a support S, the linear term forces sum(x) = 0. On this hyperplane
the polar form of the quadratic term, up to a nonzero scalar, pairs two
matrix units with 1 exactly when their rows and columns differ. In the
basis e_i-e_0 its Gram matrix is computed below. If its rank is r in
dimension d, every totally isotropic complex subspace has dimension at
most d-ceil(r/2), by passing to the quotient by the radical. Each level
space is totally isotropic because it is linear and the quadratic term
vanishes on all of it. This test is necessary; higher terms also matter.
"""

from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations
from math import comb, factorial, prod


def echelon(matrix):
    pivots = {}
    for entries in matrix:
        row = list(map(Fraction, entries))
        for j, basis in sorted(pivots.items()):
            if row[j]:
                multiple = row[j]
                row = [a - multiple * b for a, b in zip(row, basis)]
        if any(row):
            j = next(k for k, v in enumerate(row) if v)
            pivots[j] = [v / row[j] for v in row]
    return pivots


def kernel(pivots, dimension):
    for free in range(dimension):
        if free in pivots:
            continue
        vector = [0] * dimension
        vector[free] = 1
        for j, row in sorted(pivots.items(), reverse=True):
            vector[j] = -sum(a * b for a, b in zip(row[j + 1:], vector[j + 1:]))
        yield vector


def restrict_form(matrix, basis):
    images = [[sum(a * b for a, b in zip(row, v)) for row in matrix] for v in basis]
    return [[sum(a * b for a, b in zip(v, w)) for w in images] for v in basis]


def rejected_by_radical(support, form, pivots, height, width, target):
    # Equality forces inclusion of the entire radical in the candidate.
    dimension = len(support) - 1
    vectors = list(kernel(pivots, dimension))
    if not vectors:
        return False
    radical = []
    for vector in vectors:
        matrix = [0] * (height * width)
        for k, x in zip(support, [-sum(vector)] + vector):
            matrix[k] = x
        radical.append(matrix)
    matchings = [tuple(i * width + j for i, j in enumerate(cols))
                 for cols in permutations(range(width), height)]
    # A single unequal value certifies rejection. Failure to find one
    # leaves the support undecided. No genericity assumption is needed.
    normals = []
    forms = [form]
    for matrix in radical + [[sum(entries) for entries in zip(*radical)]]:
        for t in range(1, height + 1):
            shifted = [1 + t * x for x in matrix]
            value = sum(prod(shifted[k] for k in m) for m in matchings)
            if value != len(matchings):
                return True
            # Differentiate on the candidate at this radical point.
            # Its gradient must annihilate L. Its Hessian vanishes on L x L.
            if t != 1:
                continue
            grad = [0] * (height * width)
            hess = [[0] * len(grad) for _ in grad]
            for m in matchings:
                for i in m:
                    grad[i] += prod(shifted[k] for k in m if k != i)
                for i, j in combinations(m, 2):
                    term = prod(shifted[k] for k in m if k != i and k != j)
                    hess[i][j] += term
                    hess[j][i] += term
            a = support[0]
            normals.append([grad[i] - grad[a] for i in support[1:]])
            forms.append([[hess[i][j] - hess[i][a] - hess[a][j] + hess[a][a]
                           for j in support[1:]] for i in support[1:]])
    basis = list(kernel(echelon(normals), dimension))
    for candidate in forms:
        rank = len(echelon(restrict_form(candidate, basis)))
        if len(basis) - (rank + 1) // 2 < target:
            return True
    return False


def analyze(height, width, size, target):
    masks = range(1 << width)
    weights = [bin(mask).count("1") for mask in masks]
    relabel = [[sum(1 << perm[j] for j in range(width) if mask & (1 << j))
                for mask in masks] for perm in permutations(range(width))]
    seen = set()
    bounds = {}
    surviving = []
    labeled_count = 0
    for rows in combinations_with_replacement(masks, height):
        if sum(weights[r] for r in rows) != size or rows in seen:
            continue
        # Sorting quotients by row permutations. Mark precisely the orbit
        # of this representative under all column permutations as well.
        orbit = {tuple(sorted(perm[r] for r in rows)) for perm in relabel}
        seen.update(orbit)
        row_orders = factorial(height)
        for row in set(rows):
            row_orders //= factorial(rows.count(row))
        labeled_count += len(orbit) * row_orders
        support = [i * width + j for i, row in enumerate(rows)
                   for j in range(width) if row & (1 << j)]
        a = support[0]
        def pair(x, y):
            return int(x // width != y // width and x % width != y % width)
        form = [[pair(x, y) - pair(x, a) - pair(a, y)
                 for y in support[1:]] for x in support[1:]]
        pivots = echelon(form)
        rank = len(pivots)
        bound = size - 1 - (rank + 1) // 2
        if bound == target and rejected_by_radical(support, form, pivots, height, width, target):
            bound -= 1
        bounds[bound] = bounds.get(bound, 0) + 1
        if bound >= target:
            surviving.append(rows)
    assert labeled_count == comb(height * width, size)
    return bounds, surviving


if __name__ == "__main__":
    for height, target in [(4, 7), (5, 8)]:
        # Adding allowed positions preserves any subspace supported there.
        # Once k entries are ruled out, all smaller supports are ruled out.
        for size in range(13 if height == 4 else 14, height * 5 + 1):
            histogram, surviving = analyze(height, 5, size, target)
            maximum = max(histogram)
            print(f"{height}x5, {size} entries: max dimension bound {maximum}; "
                  f"{sum(histogram.values())} support orbits", flush=True)
            if maximum >= target:
                print(f"Surviving row masks: {surviving}", flush=True)
                break
