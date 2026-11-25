"""Verify single-read obstructions on paths and the two-star Fano restriction."""
from collections import defaultdict
from pathlib import Path
import re
import runpy


def truth_inputs(n):
    return [sum(1 << row for row in range(1 << n) if row & (1 << i))
            for i in range(n)]


def edge_table(wires, edges):
    table = 0
    for a, b in edges:
        table |= wires[a] & wires[b]
    return table


def trials(n, edges):
    # Two singleton/derivative directions per marked edge, packed into bitsets.
    base, delta = [0] * n, [0] * n
    for j, (a, b) in enumerate(edges):
        base[a] |= 1 << (2*j)
        base[b] |= 2 << (2*j)
        delta[a] |= 2 << (2*j)
        delta[b] |= 1 << (2*j)
    return base, delta


def apply(is_or, a, b, truth, base, delta):
    if is_or:
        return truth[a] | truth[b], base[a] | base[b], delta[a] | delta[b]
    return (truth[a] & truth[b], base[a] & base[b],
            (base[a] & delta[b]) | (delta[a] & base[b]))


def check(n, gates, output, marked, target):
    truth = truth_inputs(n)
    base, delta = trials(n, [marked])
    for is_or, a, b in gates:
        t, v, d = apply(is_or, a, b, truth, base, delta)
        truth.append(t)
        base.append(v)
        delta.append(d)
    return truth[output] == target and delta[output] == 0


def path_witnesses(n, budget, diagonals):
    edges = [(i, i+1) for i in range(n-1)]
    truth = truth_inputs(n)
    target = edge_table(truth, edges)
    base, delta = trials(n, edges)
    truth += [0] * budget
    base += [0] * budget
    delta += [0] * budget
    answers = defaultdict(list)
    gates = []
    # A newly available gate has a larger second operand than the gate just
    # scheduled. Thus independent gates can be ordered by (right, left, op).
    options = []
    for w in range(n, n+budget):
        options.append([((b*(n+budget)+a)*2+op, op, a, b, (1<<a)|(1<<b))
                        for b in range(w) for a in range(b+int(diagonals))
                        for op in (0, 1)])

    def visit(depth, unused, key):
        remaining = budget-depth-1
        for newkey, op, a, b, operands in options[depth]:
            if newkey < key:
                continue
            untouched = unused & ~operands
            # Every essential input and live gate still needs a path to the output.
            if untouched.bit_count() > remaining:
                continue
            t, v, d = apply(op, a, b, truth, base, delta)
            if not remaining:
                if t == target:
                    for e in range(n-1):
                        if not d & (3 << (2*e)):
                            answers[e].append(tuple(gates+[(op, a, b)]))
                continue
            idx = n+depth
            truth[idx], base[idx], delta[idx] = t, v, d
            gates.append((op, a, b))
            visit(depth+1, untouched | (1<<idx), newkey)
            gates.pop()

    visit(0, (1<<n)-1, -1)
    return answers


def extensions(n, gates, output):
    # Undo a zero pin that removed exactly one gate. The restored raw input
    # feeds an OR. Any nonempty subset of uses of its other operand may move.
    for source in range(n+len(gates)):
        uses = [(i, port) for i, (_, a, b) in enumerate(gates)
                for port, wire in enumerate((a, b)) if wire == source]
        if output == source:
            uses.append((-1, 0))
        for mask in range(1, 1 << len(uses)):
            chosen = {u for j, u in enumerate(uses) if mask & (1<<j)}
            mapped = list(range(n))
            result = []
            for i in range(len(gates)+1):
                if i == max(0, source-n+1):
                    new_or = n+1+len(result)
                    result.append((1, mapped[source], n))
                if i < len(gates):
                    op, a, b = gates[i]
                    mapped.append(n+1+len(result))
                    result.append((op, new_or if (i,0) in chosen else mapped[a],
                                   new_or if (i,1) in chosen else mapped[b]))
            yield tuple(result), new_or if (-1,0) in chosen else mapped[output]


def main():
    paths = path_witnesses(5, 6, True)
    assert [len(paths[e]) for e in range(4)] == [6, 2, 2, 6]
    for e in (0, 1):
        marked = (e, e+1)
        pool = {(gates, 10) for gates in paths[e]}
        edges = [(0,1), (1,2), (2,3), (3,4)]
        for n, center in ((5,1), (6,3)):
            edges.append((n, center))
            target = edge_table(truth_inputs(n+1), edges)
            pool = {case for gates, wire in pool for case in extensions(n, gates, wire)
                    if check(n+1, *case, marked, target)}
        legal = [(g, w) for g, w in pool if all(a != b for _, a, b in g)]
        first_and = [g for g, _ in legal if any(not op and max(a,b)<7 for op,a,b in g)]
        assert (len(pool), len(legal), len(first_and)) == ((66,48,0) if e==0 else (18,0,0))
        print('Marked path edge', marked, 'extensions, distinct-input, raw AND:',
              len(pool), len(legal), len(first_and))

    # Replay the existing 28-gate Lean control on every ordinary input and the two derivatives.
    notes = Path(__file__).parent
    evaluator = runpy.run_path(str(notes/'fano-collision-controls.py'))
    edges = evaluator['EDGES']
    neighbors = [set() for i in range(14)]
    for p, l in edges:
        neighbors[p].add(l)
        neighbors[l].add(p)
    count = 0
    for mask in range(1 << 14):
        if mask & 129 != 129:
            continue
        vertices = {i for i in range(14) if mask >> i & 1}
        seen, stack = {0}, [0]
        while stack:
            more = (neighbors[stack.pop()] & vertices) - seen
            seen.update(more)
            stack.extend(more)
        # A connected bipartite graph has an induced four-vertex path
        # precisely when at least one cross pair is missing.
        if seen == vertices and any((p,l) not in edges for p in vertices if p<7
                                    for l in vertices if l>=7):
            count += 1
    assert count == 2168
    print('Connected marked restrictions containing an induced four-vertex path:', count)
    source = (notes/'FanoFinalAnd.lean').read_text(encoding='utf-8')
    control = source.split('def control : Circuit :=', 1)[1].split('def ors', 1)[0]
    gates = [(op, int(a), int(b)) for op,a,b in re.findall(r'⟨\.(or|and),\[(\d+),(\d+)\]⟩', control)]
    assert len(gates) == 28 and all(a!=b for _,a,b in gates)
    assert evaluator['truth'](gates, 41) == evaluator['TARGET']
    assert all(not evaluator['derivative'](gates,41,a,b) for a,b in ((0,7),(7,0)))
    print('28-gate control: 16,384 Boolean inputs and both failed single-read trials verified.')


if __name__ == '__main__':
    main()
