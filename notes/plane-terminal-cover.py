"""Search fixed projective-plane prefixes with a minimum-cost set cover of terminal wires."""
from itertools import combinations
from random import Random


def near(p, line):
    return (p + line) % 13 in (0, 1, 3, 9)


def pack(points, lines):
    return sum(1 << p for p in points) | sum(1 << (13+l) for l in lines)


def off(points):
    return tuple(l for l in range(13) if all(not near(p, l) for p in points))


def boundary():
    positives = sorted(pack([p], [l]) for p in range(13) for l in range(13) if near(p, l))
    negatives = set()
    for k in range(4):
        for s in combinations(range(13), k):
            t = off(s)
            negatives.update((pack(s, t), pack(t, s)))
    # Every negative is below a maximal negative. Compute all closed sets
    # independently by enumerating their entire thirteen-point side.
    closed = set()
    for mask in range(8192):
        points = tuple(p for p in range(13) if mask >> p & 1)
        lines = off(points)
        if off(lines) == points:
            closed.add(pack(points, lines))
    assert len(positives) == 52 and len(negatives) == 704 and negatives == closed
    return positives, sorted(negatives)


POS, NEG = boundary()
ROWS = POS + NEG
YES = (1 << len(POS)) - 1
ALL = (1 << len(ROWS)) - 1
NO = ALL ^ YES
RAW = [sum(1 << i for i, x in enumerate(ROWS) if x >> v & 1) for v in range(26)]


def evaluate(kind, a, b):
    return a & b if kind == "and" else a | b


class Prefix:
    def __init__(self, op, operand):
        self.op, self.operand = op, operand
        self.values = RAW + [evaluate(op, RAW[0], RAW[operand])]
        self.gates = []

    def gate(self, op, a, b):
        value = evaluate(op, self.values[a], self.values[b])
        if value in self.values:
            return self.values.index(value)
        self.gates.append((op, a, b))
        self.values.append(value)
        return len(self.values)-1


def make_prefix(seed, op, operand):
    rng = Random(seed)
    prefix = Prefix(op, operand)
    orientation = seed % 2
    omitted = (seed // 2) % 4
    centers = list(range(13))
    rng.shuffle(centers)
    for index, c in enumerate(centers):
        leaves = [v if not orientation else 13+v for v in range(13) if near(c, v)]
        if not orientation and op == "or" and operand == 1 and 0 in leaves and 1 in leaves:
            leaves = [v for v in leaves if v not in (0, 1)] + [26]
        stop = 2 if index < omitted else 1
        while len(leaves) > stop:
            a = leaves.pop(rng.randrange(len(leaves)))
            b = leaves.pop(rng.randrange(len(leaves)))
            leaves.append(prefix.gate("or", a, b))
    if seed >= 8:
        # Feed a point/line conjunction back into a disjunction. The terminal
        # scan can reuse either signal at arbitrary positions.
        for _ in range(1 + seed % 3):
            v = rng.randrange(13)
            side = 13 + rng.randrange(13)
            helper = rng.randrange(26, len(prefix.values))
            crossed = prefix.gate("and", side if not orientation else v, helper)
            prefix.gate("or", crossed, v if not orientation else side)
    return prefix


def catalog(prefix, intersect, start=0, initial=None):
    target = NO if intersect else YES
    wrong = YES if intersect else NO
    options = {} if initial is None else initial.copy()

    def add(value, cost, source):
        covered = (ALL ^ value) if intersect else value
        if not covered or covered & wrong:
            return
        if covered not in options or cost < options[covered][0]:
            options[covered] = cost, source

    for i in range(start, len(prefix.values)):
        a = prefix.values[i]
        add(a, 1, i)
        for j, b in enumerate(prefix.values[:i]):
            add(a & b, 2, ("and", j, i))
            add(a | b, 2, ("or", j, i))
    return target, options


def cover(target, options, budget):
    """Exact bounded set cover. Each returned choice is a wire or one new gate."""
    masks = sorted(options, key=lambda x: (options[x][0], -bin(x).count("1")))
    maximal = []
    for mask in masks:
        if not any(mask & other == mask and options[other][0] <= options[mask][0] for other in maximal):
            maximal.append(mask)
    support = {}
    missing = target
    while missing:
        bit = missing & -missing
        support[bit] = [x for x in maximal if bit & x]
        missing ^= bit
    if any(not candidates for candidates in support.values()):
        return None
    # Disjoint candidate families give an additive lower bound: no terminal can
    # pay for two selected rows whose families are disjoint.
    order = sorted(support, key=lambda b: len(support[b]))
    family = {b: set(support[b]) for b in order}
    failed = {}

    def search(left, funds):
        if left == 0:
            return []
        if failed.get(left, -1) >= funds:
            return None
        used = set()
        bound = 0
        pivot = None
        for bit in order:
            if left & bit:
                if pivot is None:
                    pivot = bit
                if family[bit].isdisjoint(used):
                    bound += min(options[x][0] for x in support[bit])
                    used.update(family[bit])
        if bound <= funds:
            for candidate in support[pivot]:
                cost, source = options[candidate]
                if cost <= funds:
                    suffix = search(left & ~candidate, funds-cost)
                    if suffix is not None:
                        return [source] + suffix
        failed[left] = funds
        return None
    return search(target, budget)


def materialize(prefix, sources, intersect):
    gates = prefix.gates.copy()
    terminals = []
    for source in sources:
        if isinstance(source, int):
            terminals.append(source)
        else:
            gates.append(source)
            terminals.append(26+len(gates))
    acc = terminals[0]
    for wire in terminals[1:]:
        gates.append(("and" if intersect else "or", acc, wire))
        acc = 26 + len(gates)
    values = RAW + [evaluate(prefix.op, RAW[0], RAW[prefix.operand])]
    for op, a, b in gates:
        values.append(evaluate(op, values[a], values[b]))
    assert values[acc] == YES
    return gates, acc


def main():
    control = make_prefix(0, "or", 1)
    assert len(control.gates) == 38
    target, options = catalog(control, False)
    terminals = cover(target, options, 26)
    assert terminals is not None
    example, _ = materialize(control, terminals, False)
    assert len(example) == 63
    assert cover(target, options, 25) is None
    print("Control: 38 paid prefix gates and 13 AND terminals give 63 gates on all 756 rows.", flush=True)
    tried = 0
    for seed in range(24):
        for op in ("and", "or"):
            for operand in (1, 13, 15):
                prefix = make_prefix(seed, op, operand)
                for intersect in (False, True):
                    target, options = catalog(prefix, intersect)
                    terminals = cover(target, options, 63 - len(prefix.gates))
                    tried += 1
                    if terminals is not None:
                        gates, out = materialize(prefix, terminals, intersect)
                        assert len(gates) <= 62
                        print("VERIFIED", op, operand, gates, out, flush=True)
                        return
    print("Exact cover decisions:", tried, "over 144 generated prefixes; no 62-gate witness.", flush=True)
    extensions = 0
    for seed in (0, 1, 2, 3):
        for op in ("and", "or"):
            for operand in (1, 13, 15):
                prefix = make_prefix(seed, op, operand)
                old_size = len(prefix.values)
                initial = [catalog(prefix, b)[1] for b in (False, True)]
                seen = set(prefix.values)
                for j in range(old_size):
                    for i in range(j):
                        for kind in ("and", "or"):
                            val = evaluate(kind, prefix.values[i], prefix.values[j])
                            if val in seen:
                                continue
                            seen.add(val)
                            prefix.values.append(val)
                            prefix.gates.append((kind, i, j))
                            extensions += 1
                            for b in (False, True):
                                target, options = catalog(prefix, b, old_size, initial[b])
                                terminals = cover(target, options, 63-len(prefix.gates))
                                if terminals is not None:
                                    gates, out = materialize(prefix, terminals, b)
                                    assert len(gates) <= 62
                                    print("VERIFIED", op, operand, gates, out, flush=True)
                                    return
                            prefix.gates.pop()
                            prefix.values.pop()
    print("Distinct one-gate extensions over 24 bases:", extensions,
          "with both final operators tested; no witness.", flush=True)


if __name__ == "__main__":
    main()
