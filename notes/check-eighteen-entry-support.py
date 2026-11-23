"""Exact rank and Fourier-coefficient checks for the surviving 18-entry support."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from math import prod
from pathlib import Path
from runpy import run_path

linear = run_path(str(Path(__file__).with_name("check-sparse-level-spaces.py")))
echelon, kernel, restrict_form = (linear[k] for k in ("echelon", "kernel", "restrict_form"))
support = [5*i+j for i, row in enumerate((1, 15, 15, 15, 31))
           for j in range(5) if row & (1 << j)]
matchings = [tuple(5*i+j for i, j in enumerate(p)) for p in permutations(range(5))]
radical = {0: -3, 5: 1, 10: 1, 15: 1, 21: -1, 22: -1, 23: -1, 24: 3}


def derivatives(multiple):
    values = [1 + multiple * radical.get(k, 0) for k in range(25)]

    def partial(indices):
        return sum(prod(values[k] for k in perm if k not in indices)
                   for perm in matchings if all(k in perm for k in indices))

    gradient = [partial((k,)) for k in support]
    hessian = [[partial((k, l)) if k != l else 0 for k in support] for l in support]
    # Use the coordinates e_i - e_0 on the total-sum-zero hyperplane.
    return ([d-gradient[0] for d in gradient[1:]],
            [[hessian[i][j]-hessian[i][0]-hessian[0][j]+hessian[0][0]
              for j in range(1, len(support))] for i in range(1, len(support))])


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def rank_checks():
    _, original = derivatives(0)
    gradient, shifted = derivatives(1)
    rad = [radical.get(k, 0) for k in support[1:]]
    assert sum(radical.values()) == 0 and len(echelon(original)) == 16
    assert all(dot(row, rad) == 0 for row in original)

    tangent = list(kernel(echelon([gradient]), 17))
    form = [[3*b-a for a, b in zip(row_a, row_b)]
            for row_a, row_b in zip(original, shifted)]
    assert len(tangent) == 16 and len(echelon(restrict_form(form, tangent))) == 10
    for row, col in product((1, 2), repeat=2):
        v = [(int(k//5 == row)-int(k//5 == 3))*(int(k%5 == col)-int(k%5 == 3))
             for k in support[1:]]
        assert dot(gradient, v) == 0
        assert all(dot(w, [dot(r, v) for r in form]) == 0 for w in tangent)


def fourier_checks():
    # In Q[z]/(1+z+z^2), reduce counts of exponents modulo three.
    modes = [(1, 1), (1, 2), (2, 1), (2, 2)]
    expected = {2: {(0, 3): 54, (1, 2): 54},
                3: {(i, i, i): 12 for i in range(4)}}
    for degree in (2, 3):
        actual = {}
        for monomial in combinations_with_replacement(range(4), degree):
            counts = Counter()
            for perm in matchings:
                cells = [divmod(k, 5) for k in perm if 1 <= k//5 <= 3 and 1 <= k%5 <= 3]
                for positions in combinations(cells, degree):
                    for order in set(permutations(monomial)):
                        phase = sum(modes[h][0]*(r-1) + modes[h][1]*(c-1)
                                    for (r, c), h in zip(positions, order))
                        counts[phase % 3] += 1
            assert counts[1] == counts[2]
            coefficient = counts[0] - counts[2]
            if coefficient:
                actual[monomial] = coefficient
        assert actual == expected[degree], actual

if __name__ == "__main__":
    rank_checks()
    fourier_checks()
    print("Verified ranks 16 and 10, four kernel directions, and both Fourier polynomials.")
