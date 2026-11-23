"""Exclude all normalized five-gate topologies using only their linearized clauses."""

import runpy
from itertools import combinations_with_replacement, product
from pathlib import Path


def shapes(internal):
    """Return the different families of reachable gate sides for each choice of sides."""
    sides = []
    for gate in range(5):
        count = 1 << min(gate, internal)
        sides.append([(a, b) for a in range(count) for b in range(a, count) if not a & b])
    result = set()
    for hidden in product(*sides[:internal]):
        for visible in combinations_with_replacement(sides[internal], 5 - internal):
            wiring = hidden + visible
            corners = set()
            for choice in range(32):
                live = 31 ^ ((1 << internal) - 1)
                reached = 0
                for gate in reversed(range(5)):
                    if live & (1 << gate):
                        side = (choice >> gate) & 1
                        reached |= 1 << (2 * gate + side)
                        live |= wiring[gate][side]
                corners.add(reached)
            if len(corners) < 16:
                continue
            # An internal signal that is always reached can feed the output
            # directly. An internal signal that is never reached can be removed.
            if any(len({bool(c & (3 << (2 * g))) for c in corners}) == 1
                   for g in range(internal)):
                continue
            result.add(tuple(sorted(corners)))
    return result


def vertex_profiles(corners):
    """A vertex is absent from a clause exactly when none of its bare sides is reached."""
    profiles = {(1 << len(corners)) - 1}
    for side in range(10):
        absent = sum(1 << j for j, c in enumerate(corners) if not c & (1 << side))
        profiles |= {p & absent for p in profiles}
    return sorted(profiles)


def profile_symmetries(corners, profiles):
    # Use only permutations that preserve the actual family of reachable sides.
    # These need not generate every symmetry for the pruning to be sound.
    proposed = []
    for a in range(5):
        left = 1 << (2 * a)
        proposed.append(tuple((c & ~(3 * left)) | ((c & left) << 1)
                              | ((c & (left << 1)) >> 1) for c in corners))
        for b in range(a):
            right = 1 << (2 * b)
            for flip in (False, True):
                changed = []
                for c in corners:
                    x, y = (c // left) & 3, (c // right) & 3
                    if flip:
                        x, y = ((x & 1) << 1) | (x >> 1), ((y & 1) << 1) | (y >> 1)
                    changed.append((c & ~(3 * left | 3 * right)) | (x * right) | (y * left))
                proposed.append(tuple(changed))
    positions = {c: i for i, c in enumerate(corners)}
    indices = {p: i for i, p in enumerate(profiles)}
    permutations = set()
    for changed in proposed:
        if set(changed) != set(corners):
            continue
        order = [positions[c] for c in changed]
        image = tuple(indices[sum(1 << j for i, j in enumerate(order) if p & (1 << i))]
                      for p in profiles)
        if image != tuple(range(len(profiles))):
            permutations.add(image)
    return sorted(permutations)


def representatives(options, symmetries):
    seen = set()
    for option in options:
        if option in seen:
            continue
        seen.add(option)
        todo = [option]
        while todo:
            current = todo.pop()
            for permutation in symmetries:
                following = permutation[current]
                if following not in seen:
                    seen.add(following)
                    todo.append(following)
        yield option, [p for p in symmetries if p[option] == option]


def fits(corners, negative):
    wanted = [sum(1 << i for i, point in enumerate(negative) if point & (1 << v))
              for v in range(9)]
    profiles = vertex_profiles(corners)
    visits = 0

    def search(used, cells, symmetries):
        nonlocal visits
        visits += 1
        if used == 511:
            return True
        best = None
        for v, mask in enumerate(wanted):
            if used & (1 << v):
                continue
            # Each target row in a cell needs a distinct candidate corner.
            limits = [(available, (target & mask).bit_count(),
                       available.bit_count() - (target & ~mask).bit_count())
                      for target, available in cells]
            options = [i for i, p in enumerate(profiles)
                       if all(lo <= (p & available).bit_count() <= hi for available, lo, hi in limits)]
            if not options:
                return False
            if best is None or len(options) < len(best[1]):
                best = v, options
        v, options = best
        for i, stabilizer in representatives(options, symmetries):
            mask, p = wanted[v], profiles[i]
            divided = []
            for target, available in cells:
                if target & mask:
                    divided.append((target & mask, available & p))
                if target & ~mask:
                    divided.append((target & ~mask, available & ~p))
            if search(used | (1 << v), divided, stabilizer):
                return True
        return False

    start = [((1 << len(negative)) - 1, (1 << len(corners)) - 1)]
    answer = search(0, start, profile_symmetries(corners, profiles))
    return answer, visits


if __name__ == "__main__":
    graph = runpy.run_path(str(Path(__file__).with_name("check-nine-vertex-internal-gates.py")))
    negative, _ = graph["defined_points"]()
    for internal in range(5):
        families = shapes(internal)
        states = 0
        for corners in sorted(families):
            possible, count = fits(corners, negative)
            assert not possible
            states += count
        print(f"{internal} internal gates: {len(families)} families, {states} search states, no match",
              flush=True)
