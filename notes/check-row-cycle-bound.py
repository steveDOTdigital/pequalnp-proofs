"""Exact finite checks for the four-by-five row-cycle bound."""

from itertools import combinations, permutations, product


def row_factor(frequencies):
    # Count fourth roots by exponent, so cancellation is checked in integers.
    counts = [0] * 4
    for rows in permutations(range(4), len(frequencies)):
        counts[sum(r * k for r, k in zip(rows, frequencies)) % 4] += 1
    assert counts[1] == counts[3]
    return counts[0] - counts[2]


def pencil(roots):
    # Coefficients of det(s M + N), constant term first, modulo eleven.
    result = [0] * 5
    for p in permutations(range(4)):
        if any(i == j for i, j in enumerate(p)):
            continue
        inversions = sum(p[i] > p[j] for i, j in combinations(range(4), 2))
        coeff = [(-1) ** inversions]
        for i, j in enumerate(p):
            coeff = [(a * (roots[i] + roots[j]) + b) % 11
                     for a, b in zip(coeff + [0], [0] + coeff)]
        result = [(a + b) % 11 for a, b in zip(result, coeff)]
    return result


expected = {(1, 3): -4, (1, 3, 0): -8, (1, 3, 0, 0): -8,
            (1, 1, 3, 3): 8, (1, 1, 2): 8, (1, 1, 2, 0): 8,
            (2, 2): -4, (2, 2, 0): -8, (2, 3, 3): 8,
            (1, 1, 1, 1): -24, (3, 3, 3, 3): -24, (2, 2, 2, 2): 24}
assert all(row_factor(f) == value for f, value in expected.items())
roots = [pow(3, i, 11) for i in range(5)]
assert roots == [1, 3, 9, 5, 4] and sum(roots) % 11 == 0
residues = []
for i, j in combinations(range(5), 2):
    a, b, c = [v for k, v in enumerate(roots) if k not in (i, j)]
    residues.append(sum((roots[i] + roots[j] - 2 * v) * w * w
                        for v, w in [(a, b-c), (b, c-a), (c, a-b)]) % 11)
assert residues == [3, 1, 4, 5, 4, 5, 9, 9, 3, 1]
det = pencil(roots[1:])
assert det == [1, 4, 4, 6, 8]
monic = [c * pow(det[-1], -1, 11) % 11 for c in det]
for a, b in product(range(11), repeat=2):
    assert monic != [b*b % 11, 2*a*b % 11, (a*a + 2*b) % 11, 2*a % 11, 1]

# Expand each monomial in the four independent row amplitudes of the
# proposed extremizer. Cancellation in Z[z]/(1+z+z²+z³+z⁴) is exact.
for n in range(5):
    for rows in combinations(range(4), n):
        counts = [0] * 5
        for cols in permutations(range(5), 4):
            counts[sum(cols[i] for i in rows) % 5] += 1
        if rows:
            assert len(set(counts)) == 1
        else:
            assert counts == [120, 0, 0, 0, 0]
print("12 row factors, 10 nonzero residues, nonsquare determinant,"
      " and all 16 extremizer coefficients verified.")
