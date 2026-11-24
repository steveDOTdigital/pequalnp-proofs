"""Check forced clauses on the Fano and order-three cyclic planes."""
from itertools import combinations
from math import comb


def population(mask):
    return bin(mask).count("1")


def subsets_unless_larger(n, maximum):
    for size in range(maximum + 1):
        for indices in combinations(range(n), size):
            yield sum(1 << i for i in indices)


def check_plane(q, differences):
    n = q * q + q + 1
    all_vertices = (1 << n) - 1
    blocks = [
        sum(1 << ((line + d) % n) for d in differences)
        for line in range(n)
    ]
    assert all(population(block) == q + 1 for block in blocks)
    assert all(population(a & b) == 1 for a, b in combinations(blocks, 2))

    def incident(points, lines):
        return any((lines >> i) & 1 and points & block
                   for i, block in enumerate(blocks))

    # Count gates with false output in the standard OR-per-line star circuit.
    # Each line contributes q point ORs and one AND. The final OR tree has
    # n-1 gates; all of these are false on the incidence-free rows used here.
    def false_ors_on_negative(points, lines):
        gates = n - 1
        for i, block in enumerate(blocks):
            values = [bool(points & (1 << p)) for p in range(n) if block & (1 << p)]
            part = values[0]
            for bit in values[1:]:
                part = part or bit
                gates += int(not part)
            assert not (part and lines & (1 << i))
        return gates

    # Points in the selected union and lines outside the selection are the
    # literals of the unique positive clause falsified on this maximal row.
    clauses = set()
    max_clause_size = 0
    for selected in subsets_unless_larger(n, q):
        covered = 0
        for i, block in enumerate(blocks):
            if selected >> i & 1:
                covered |= block
        outside_points = all_vertices ^ covered
        outside_lines = all_vertices ^ selected
        assert not incident(outside_points, selected)
        for i, block in enumerate(blocks):
            if outside_lines >> i & 1:
                assert population(outside_points & block) >= q + 1 - population(selected)
                assert incident(outside_points, selected | (1 << i))
        for p in range(n):
            if covered >> p & 1:
                assert incident(outside_points | (1 << p), selected)
        clause = covered | (outside_lines << n)
        assert clause not in clauses
        assert false_ors_on_negative(outside_points, selected) >= population(clause) - 1
        clauses.add(clause)
        max_clause_size = max(max_clause_size, population(clause))

    count = sum(comb(n, k) for k in range(q + 1))
    assert len(clauses) == count
    assert max_clause_size == 2 * q * q + 2
    for i, block in enumerate(blocks):
        for p in range(n):
            if block >> p & 1:
                flag = (1 << p) | (1 << (n + i))
                assert all(clause & flag for clause in clauses)

    # Test the maximum monotone completion on every 14-bit Fano input.
    checked = 0
    if q == 2:
        for row in range(1 << (2 * n)):
            points, lines = row & all_vertices, row >> n
            expected = population(lines) > q or incident(points, lines)
            assert all(row & clause for clause in clauses) == expected
            checked += 1
    print(f"q={q}, clauses={count}, largest clause={max_clause_size}, "
          f"full assignments={checked}, all boundary checks passed")


if __name__ == "__main__":
    check_plane(2, (0, 1, 3))
    check_plane(3, (0, 1, 3, 9))
