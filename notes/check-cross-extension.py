"""Exact certificate for the standard six-dimensional cross in L-gct-179.

Run with Python 3.8 or newer. Matrices are flattened in row-major order.
The proof works over the complex numbers: all certificate matrices are
integral, so their rational and complex ranks agree.
"""

from fractions import Fraction
from itertools import combinations, permutations
from math import prod


MATCHINGS = tuple(tuple(5 * i + j for i, j in enumerate(cols))
                  for cols in permutations(range(5), 4))
ZERO = (0,) * 20


def difference(i, j):
    return tuple(int(k == i) - int(k == j) for k in range(20))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def rank(vectors):
    pivots = {}
    for vector in vectors:
        row = list(map(Fraction, vector))
        for pivot, basis in sorted(pivots.items()):
            multiple = row[pivot]
            row = [a - multiple * b for a, b in zip(row, basis)]
        if any(row):
            pivot = next(i for i, entry in enumerate(row) if entry)
            pivots[pivot] = [entry / row[pivot] for entry in row]
    return len(pivots)


def value(matrix):
    return sum(prod(1 + matrix[k] for k in matching) for matching in MATCHINGS)


def gradient(matrix):
    result = [0] * 20
    for matching in MATCHINGS:
        for k in matching:
            result[k] += prod(1 + matrix[j] for j in matching if j != k)
    return result


def check():
    # U has three zero-sum row differences outside column zero and
    # three zero-sum differences in column zero. Each matching uses at
    # most two cross entries. Hence F on U has total degree at most two.
    basis = [difference(j, 4) for j in (1, 2, 3)]
    basis += [difference(j, 0) for j in (5, 10, 15)]
    assert rank(basis) == 6
    support = {k for k in range(20) if any(b[k] for b in basis)}
    assert all(len(support.intersection(m)) <= 2 for m in MATCHINGS)
    pairs = [add(a, b) for a, b in combinations(basis, 2)]
    probes = [ZERO] + basis + pairs
    # Evaluation at 0, e_i, 2e_i, and e_i+e_j determines a quadratic.
    assert all(value(p) == 120 for p in probes + [add(b, b) for b in basis])

    # For a level space L containing U, every gradient at a point
    # of U annihilates L, by differentiating F(p + t*x) at t = 0.
    normals = [gradient(p) for p in probes]
    assert rank(normals) == 13
    extra = (-4, 1, 1, 1, 1) * 4
    kernel_basis = basis + [extra]
    assert rank(kernel_basis) == 7
    assert all(sum(x * y for x, y in zip(n, b)) == 0
               for n in normals for b in kernel_basis)
    # Rank-nullity identifies the common kernel with U + C*extra.
    # Any strict extension of U inside that kernel contains extra.
    assert value(extra) == -1920
    print("Cross dimension 6; gradient rank 13; common kernel dimension 7.")
    print("F(extra) = -1920, so the cross has no strict level-space extension.")


if __name__ == "__main__":
    check()
