"""Check the Fano geometry and the possible OR insertions for a fourth line."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import runpy


LINES = {j: frozenset((j, (j+1) % 7, (j+3) % 7)) for j in range(7)}


def geometry(picked):
    lines = [LINES[j] for j in picked]
    union = frozenset.union(*lines)
    common = frozenset.intersection(*lines)
    corners = {v for v in union if sum(v in line for line in lines) > 1}
    if common:
        c, = common
        cores = [{c, *points} for points in product(*(line-common for line in lines))]
    else:
        cores = [corners]
    # To survive both outside settings, a used OR must stay inside the union
    # and meet every choice of the retained core.
    candidates = {frozenset(points) for j in set(LINES)-set(picked)
                  for size in (2, 3) for points in combinations(LINES[j], size)
                  if set(points) <= union and all(set(points) & core for core in cores)}
    assert all(len(union-core) == 3 for core in cores)
    if common:
        assert len(union) == 7 and len(cores) == 8 and not candidates
        return 'pencil'
    assert len(union) == 6 and len(corners) == 3 and len(candidates) == 3
    for pair in candidates:
        c, = pair & corners
        a, = pair-corners
        assert all(c not in line for line in lines if a in line)
    return 'triangle'


def star_trees(picked):
    # Seven point variables and three raw line variables are numbered 0 to 9.
    neighbors = [sorted(LINES[j]) for j in picked]
    for last_points in product(range(3), repeat=3):
        gates, stars = [], []
        for index, last in enumerate(last_points):
            a, b = [v for i, v in enumerate(neighbors[index]) if i != last]
            base = 10+len(gates)
            gates.extend([(True, a, b), (True, base, neighbors[index][last]),
                          (False, 7+index, base+1)])
            stars.append(base+2)
        for last in range(3):
            a, b = [wire for i, wire in enumerate(stars) if i != last]
            yield tuple(gates + [(True, a, b), (True, 19, stars[last])])


def evaluate(gates, inputs):
    values = list(inputs)
    for is_or, a, b in gates:
        values.append(values[a] | values[b] if is_or else values[a] & values[b])
    return values[-1]


def main():
    helper = runpy.run_path(str(Path(__file__).with_name('plane-small-core-bounds.py')))
    insert_or = helper['add_private']
    inputs = [sum(((row >> i) & 1) << row for row in range(1 << 11)) for i in range(11)]
    stars = [inputs[10] & (inputs[a] | inputs[b] | inputs[c]) for a,b,c in map(sorted, LINES.values())]
    types = Counter()
    shapes = extensions = cases = 0
    for picked in combinations(LINES, 3):
        types[geometry(picked)] += 1
        old = sorted(set(LINES)-set(picked))
        expected = 0
        for i,j in enumerate(picked):
            a,b,c = LINES[j]
            expected |= inputs[7+i] & (inputs[a] | inputs[b] | inputs[c])
        for base in star_trees(picked):
            shapes += 1
            assert evaluate(base, inputs[:10]) == expected
            # Give the new channel all 2,048 assignments as a raw line, then
            # specialize it to that line's actual star for each completed line.
            successes = [0] * 4
            for extended in insert_or(10, base):
                extensions += 1
                raw = evaluate(extended, inputs)
                for i,j in enumerate(old):
                    target = expected | stars[j]
                    assert raw != target
                    if evaluate(extended, inputs[:10]+[stars[j]]) == target:
                        successes[i] += 1
            # Three star outputs and two upper OR outputs are precisely five
            # single-use positions. Joining the new star to any of them works.
            assert successes == [5]*4
            cases += 4
    assert types == {'pencil': 7, 'triangle': 28} and cases == 11340
    print(dict(types), shapes, 'three-star trees,', extensions, 'OR insertions,', cases,
          'tree and completed-line choices; raw channels never suffice.')


if __name__ == '__main__':
    main()
