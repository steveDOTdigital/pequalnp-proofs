"""Finite certificates for the quadrangle formula bound in L-meta-1692."""
from collections import Counter
from itertools import combinations

N = 13
DIFFERENCE = {0, 1, 3, 9}
EDGES = [(p, N + l) for p in range(N) for l in range(N) if (p - l) % N in DIFFERENCE]
STARS = [[e for e in EDGES if v in e] for v in range(2 * N)]
NEG = []
for points in combinations(range(N), 4):
    counts = [sum((p - l) % N in DIFFERENCE for p in points) for l in range(N)]
    if max(counts) <= 2:
        NEG.append(set(points) | {N + l for l, n in enumerate(counts) if not n})
ROWS = [set(e) for e in EDGES] + NEG
RAW = [sum(1 << i for i, t in enumerate(ROWS) if v in t) for v in range(2 * N)]
TARGET = (1 << len(EDGES)) - 1
ALL = (1 << len(ROWS)) - 1


def pop(m):
    return bin(m).count('1')


def disjoint_unions(family):
    choices = {0}
    for row_set in family:
        choices.update(m | row_set for m in list(choices) if not m & row_set)
    return choices


def slots(family, support):
    patterns = [set(i for i, r in enumerate(family) if r & (1 << j)) for j in range(4)]
    selected = [i for i in range(4) if support & (1 << i)]
    return sum(any(i != j and patterns[j] <= patterns[i] for j in selected) for i in selected)


def check_local():
    for v in range(26):
        neighbors = [next(w for w in edge if w != v) for edge in STARS[v]]
        frequencies = Counter(sum(1 << i for i, w in enumerate(neighbors) if w in t)
                              for t in NEG if v not in t)
        a, b = (27, 9) if v < 13 else (18, 18)
        assert frequencies == {t: (a if pop(t) == 1 else b) for t in range(16)
                               if 1 <= pop(t) <= 2}
    for p, l in EDGES:
        for _, other_line in STARS[p]:
            for other_point, _ in STARS[l]:
                if other_point != p and other_line != l:
                    assert (other_point, other_line) not in EDGES
                    assert any({other_point, other_line} <= t for t in NEG)
    for right in (False, True):
        unique = {}
        a, b, unit = (18, 18, 504) if right else (27, 9, 486)
        for support in range(1, 16):
            rows = [r for r in range(1, 16) if r & support == r]
            degree = pop(support)
            for k in range(1, degree + 1):
                for bank in combinations(rows, k):
                    choices = disjoint_unions(bank)
                    if any(not any((t & support) & ~m == 0 for m in choices) for t in range(16)
                           if 1 <= pop(t) <= 2):
                        continue
                    cost = sum((a if pop(t) == 1 else b) *
                               min(pop(m) for m in choices if (t & support) & ~m == 0)
                               for t in range(16) if 1 <= pop(t) <= 2)
                    slack = 432*k + 216*slots(bank, support) + cost - unit*degree
                    assert slack >= 0
                    if degree == 4:
                        unique.setdefault(slack, []).append(bank)
        assert set(unique[0]) == {(15,), (1, 2, 4, 8)}
        print('Point' if not right else 'Line', 'minimum positive full-degree slack',
              min(x for x in unique if x))


def induced_max(size):
    best = 0
    for a in range(max(0, size - N), min(size, N) + 1):
        for points in combinations(range(N), a):
            hits = sorted((sum((p-l) % N in DIFFERENCE for p in points) for l in range(N)),
                          reverse=True)
            best = max(best, sum(hits[:size-a]))
    return best


def evaluate(gates, out):
    words = RAW.copy()
    for op, a, b in gates:
        assert 0 <= a < len(words) and 0 <= b < len(words)
        words.append(words[a] | words[b] if op == 'or' else words[a] & words[b])
    return words, words[out]


def fixture():
    gates = []
    def gate(op, a, b):
        gates.append((op, a, b))
        return 25 + len(gates)
    def fold(op, wires):
        out = wires[0]
        for w in wires[1:]:
            out = gate(op, out, w)
        return out

    stars = [gate('and', p, fold('or', [l for _, l in STARS[p]])) for p in range(N)]
    root = fold('or', stars)
    assert len(gates) == 64 and evaluate(gates, root)[1] == TARGET
    # Exercise all four forms of class-constant sharing. Labels may alternate
    # in gate order. The pre-existing star at index zero is also shared.
    high_flags = fold('or', sorted(set(range(26)) - NEG[0]))
    low_flags = gate('and', 0, 1)
    high_neg = fold('or', list(range(1, 13)))
    root = gate('or', gate('and', root, high_flags), gate('and', stars[0], high_flags))
    root = gate('or', root, gate('and', low_flags, stars[0]))
    root = gate('or', root, gate('and', low_flags, stars[1]))
    # This guard is high on every negative. The OR of the two branches
    # retains the unconditional path to the original output.
    root = gate('or', gate('and', root, high_neg), root)
    root = gate('or', root, gate('and', stars[1], high_neg))
    return gates, root


def unshare(gates, out):
    words, original = evaluate(gates, out)
    live, uses = set(), Counter()
    def visit(i):
        if i < 26 or i in live:
            return
        live.add(i)
        for w in gates[i-26][1:]:
            uses[w] += 1
            visit(w)
    visit(out)
    shared = sorted(w for w in live if uses[w] >= 2)
    pins, priority, kinds = {}, [], set()
    for w in shared:
        hot, warm = words[w] & TARGET, words[w] & (ALL ^ TARGET)
        if not hot:
            pins[w] = False
            kinds.add('low on flags')
        elif warm == (ALL ^ TARGET):
            pins[w] = True
            kinds.add('high on negatives')
        elif not warm:
            pins[w] = False
            priority.append(w)
            kinds.add('low on negatives')
        elif hot == TARGET:
            pins[w] = True
            priority.append(w)
            kinds.add('high on flags')
        else:
            raise ValueError('The circuit has a shared signal varying on both classes.')

    # Trees use raw indices or explicit Boolean constants at their leaves.
    def join(op, a, b):
        for x, other in ((a, b), (b, a)):
            if type(x) is bool:
                if (op == 'or' and x) or (op == 'and' and not x):
                    return x
                return other
        return (op, a, b)

    residual = list(range(26))
    def wire(w):
        return pins[w] if w in pins else residual[w]
    for op, a, b in gates:
        residual.append(join(op, wire(a), wire(b)))
    result = residual[out]
    for w in reversed(priority):
        result = join('and' if pins[w] else 'or', residual[w], result)
    def interpret(tree):
        if type(tree) is bool:
            return 0, ALL if tree else 0
        if isinstance(tree, int):
            return 0, RAW[tree]
        op, a, b = tree
        ca, va = interpret(a)
        cb, vb = interpret(b)
        return 1 + ca + cb, va | vb if op == 'or' else va & vb
    size, values = interpret(result)
    assert values == original == TARGET and size <= len(live)
    return len(live), size, kinds


if __name__ == '__main__':
    assert len(EDGES) == 52 and len(NEG) == 234
    check_local()
    maxima = [induced_max(n) for n in range(2, 9)]
    assert maxima == [1, 2, 3, 4, 6, 7, 9]
    assert all(5*maxima[g-1] < 4*g + 12 for g in range(1, 7))
    old, new, kinds = unshare(*fixture())
    assert len(kinds) == 4
    print('Induced maxima for 2 through 8 vertices:', maxima)
    print('Mixed-order four-class control:', old, 'circuit gates to', new, 'formula gates.')
