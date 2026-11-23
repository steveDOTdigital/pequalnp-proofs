"""Check small linear families of OR outputs in the one-NOT, binary fan-in model."""

from collections import Counter
from itertools import combinations, permutations


def large_set_cores(n):
    """Drop pairs and families already excluded by the largest-output bound."""
    candidates = [
        sum(1 << i for i in group)
        for size in range(3, n + 1)
        for group in combinations(range(n), size)
    ]
    remaining = set()

    def visit(core, choices):
        excess = [s.bit_count() - 2 for s in core]
        if excess and sum(excess) - max(excess) > 1:
            remaining.add(tuple(sorted(core)))
        for index, subset in enumerate(choices):
            compatible = [s for s in choices[index + 1:] if (s & subset).bit_count() <= 1]
            visit(core + [subset], compatible)

    visit([], candidates)
    permutations_of_masks = []
    for perm in permutations(range(n)):
        image = [0] * (1 << n)
        for mask in range(1, 1 << n):
            bit = mask & -mask
            image[mask] = image[mask ^ bit] | (1 << perm[bit.bit_length() - 1])
        permutations_of_masks.append(image)

    cores = []
    while remaining:
        core = min(remaining)
        orbit = {tuple(sorted(image[s] for s in core)) for image in permutations_of_masks}
        assert orbit <= remaining
        remaining.difference_update(orbit)
        cores.append((core, len(orbit)))
    return cores


def check_core(n, core):
    """Give all compatible pairs for free, then enumerate all possible extra gates."""
    full = (1 << (1 << n)) - 1
    inputs = [sum(1 << a for a in range(1 << n) if a >> i & 1) for i in range(n)]

    def disjunction(mask):
        table = 0
        for i, bit in enumerate(inputs):
            if mask >> i & 1:
                table |= bit
        return table

    targets = frozenset(disjunction(s) for s in core)
    free = {0, full, *inputs}
    for i, j in combinations(range(n), 2):
        mask = (1 << i) | (1 << j)
        if all(s & mask != mask for s in core):
            free.add(disjunction(mask))

    def closure(wires):
        wires = set(wires)
        while True:
            produced = {
                result for a, b in combinations(wires, 2)
                for result in (a & b, a | b) if result in targets
            }
            if produced <= wires:
                return wires
            wires.update(produced)

    # Positive control: private prefixes build each required OR with exactly
    # sum(|S|-2) auxiliary gates when its final gate is free.
    control = set()
    for mask in core:
        bits = [i for i in range(n) if mask >> i & 1]
        for end in range(2, len(bits)):
            partial = sum(1 << i for i in bits[:end])
            assert disjunction(partial) == disjunction(partial ^ (1 << bits[end-1])) | inputs[bits[end-1]]
            control.add(disjunction(partial))
    exact = sum(s.bit_count() - 2 for s in core)
    assert len(control) == exact and targets <= closure(free | control)
    levels = Counter()

    # The larger double-four case stores only interior states. Its terminal
    # count includes repeated visits; the truth-table test is identical.
    dead = set()
    remember_leaves = not (n == 7 and all(s.bit_count() == 4 for s in core))

    def search(extra, used_not):
        key = (extra, used_not)
        if key in dead:
            return False
        levels[len(extra)] += 1
        wires = closure(free | extra)
        if targets <= wires:
            return True
        if len(extra) == exact - 1:
            if remember_leaves:
                dead.add(key)
            return False
        candidates = {result for a, b in combinations(wires, 2) for result in (a & b, a | b)}
        for result in sorted(candidates - wires - targets):
            if search(extra | {result}, used_not):
                return True
        if not used_not:
            for a in sorted(wires):
                result = full ^ a
                if result not in wires and result not in targets and search(extra | {result}, True):
                    return True
        dead.add(key)
        return False

    found = search(frozenset(), False)
    dead.clear()
    return found, sorted(levels.items())


if __name__ == "__main__":
    for n in range(2, 8):
        cores = large_set_cores(n)
        print(f"{n} inputs: {len(cores)} remaining core types", flush=True)
        for core, multiplicity in cores:
            # Keep the earlier small exhaustive checks as cross-checks. The
            # private-parent proof also handles these triple-only cases.
            if n == 7 and sum(s.bit_count() - 2 for s in core) != 3:
                if sum(s.bit_count() - 3 for s in core) <= 1:
                    print("  private-parent bound", core, multiplicity, flush=True)
                    continue
                assert sorted(s.bit_count() for s in core) == [4, 4]
            found, levels = check_core(n, core)
            print("  checked", core, multiplicity, "witness", found, "states", levels, flush=True)
