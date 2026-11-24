"""Check the three-input obstruction used to count shared OR gates.

Run with Python 3. Raw indices 0..12 are points and 13..25 are lines.
For a fixed center, test every possible four-cycle among the raw inputs
outside its incidence neighborhood. No third-party packages are needed.
"""

from itertools import combinations, combinations_with_replacement


def main():
    points = set(range(13))
    lines = set(range(13, 26))
    offsets = {0, 1, 3, 9}
    on_line = {
        line: {p for p in points if (p - (line - 13)) % 13 in offsets}
        for line in lines
    }
    neighbors = {
        **on_line,
        **{p: {line for line in lines if p in on_line[line]} for p in points},
    }
    rows = []
    for four_points in combinations(sorted(points), 4):
        quad = set(four_points)
        if all(len(quad & incident) <= 2 for incident in on_line.values()):
            rows.append(quad | {line for line in lines if quad.isdisjoint(on_line[line])})
    assert len(rows) == 234

    maxima = []
    for center in range(26):
        outside = (points | lines) - neighbors[center] - {center}
        rows_at_center = [row for row in rows if center in row]
        # An edge means that the two inputs can never be active with the center.
        conflict = {x: set() for x in outside}
        for x, y in combinations_with_replacement(sorted(outside), 2):
            if not any(x in row and y in row for row in rows_at_center):
                assert x != y, (center, x)
                conflict[x].add(y)
                conflict[y].add(x)
        common = max(len(conflict[x] & conflict[y]) for x, y in combinations(outside, 2))
        assert common <= 1, (center, common)
        maxima.append(common)
    print(f"{len(rows)} quadrangles, {len(maxima)} centers, "
          f"maximum common conflict neighbors: {max(maxima)}")


if __name__ == "__main__":
    main()
