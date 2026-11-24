"""Check the raw-operand rectangle classification against actual forbidden rows."""
from itertools import combinations_with_replacement


def check(n, residues, pure_only=False):
    # Points occupy bits 0..n-1, lines bits n..2n-1.
    flags = [(1 << p) | (1 << (n + l)) for p in range(n) for l in range(n)
             if (p - l) % n in residues]
    allowed = set(flags)
    points = [1 << i for i in range(2 * n)]
    forbidden = {p | v for p, v in combinations_with_replacement(points, 2)
                 if (p | v) not in allowed}
    neighbors = {e: [row for row in forbidden if row & e] for e in flags}
    if pure_only:
        supports = ((a, b << n) for a in range(1 << n) for b in range(1 << n))
    else:
        supports = combinations_with_replacement(range(1 << (2 * n)), 2)
    checked = sharp = 0
    for a, b in supports:
        direct = lambda row: bool(row & a and row & b)
        accepted = [e for e in flags if direct(e)]
        guarded = [e for e in accepted if not any(direct(row) for row in neighbors[e])]
        if any(direct(row) for row in forbidden):
            assert len(guarded) <= 1
            if guarded and len(accepted) >= 3:
                sharp += 1
        elif accepted:
            assert guarded == accepted
            common = accepted[0]
            for e in accepted:
                common &= e
            assert common
        checked += 1
    assert sharp
    print(f"{n} points, {checked} support pairs, "
          f"{sharp} non-full examples with one protected flag and at least three accepted flags")


if __name__ == "__main__":
    check(3, (0, 1))                 # All mixed supports on a six-cycle
    check(7, (0, 1, 3), pure_only=True)  # All point/line rectangles on the Fano plane
