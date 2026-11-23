"""Test two opposite column frequencies in the 4 by 5 permanent over Q."""

from itertools import combinations

from sympy import QQ, groebner, symbols


def main():
    p, q, r, s = symbols("p q r s")
    # Row permutation makes the first two coordinates a chart on A.
    basis_a = [(1, 0, p, r), (0, 1, q, s)]
    # With M = J-I, the opposite plane is B = (J-3I) ker(A transpose).
    normals = [(-p, -q, 1, 0), (-r, -s, 0, 1)]
    basis_b = [tuple(sum(v) - 3*x for x in v) for v in normals]
    pairs = tuple(combinations(range(4), 2))

    def samples(basis):
        return [*basis, tuple(x+y for x, y in zip(*basis))]

    # A bihomogeneous polynomial of bidegree (2,2) vanishes everywhere
    # exactly when it vanishes at these nine pairs of projective points.
    equations = [
        sum(a[i]*a[j]*b[k]*b[l] for (i,j), (k,l) in zip(pairs, reversed(pairs)))
        for a in samples(basis_a) for b in samples(basis_b)
    ]
    basis = groebner(equations, p, q, r, s, order="grevlex", domain=QQ)
    assert list(basis) == [1]
    print("Reduced Groebner basis over Q:", list(basis), flush=True)


if __name__ == "__main__":
    main()
