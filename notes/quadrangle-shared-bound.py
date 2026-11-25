"""One shared result on the order-three plane. Run with Python 3."""
import itertools, runpy, math
from collections import Counter
from functools import lru_cache
from pathlib import Path

notes = Path(__file__).resolve().parent
data = runpy.run_path(str(notes / 'quadrangle-partition.py'))
edges, neg, raw = data['EDGES'], data['NEG'], data['RAW']
pop, unions = data['pop'], data['disjoint_unions']
es = [[i for i, e in enumerate(edges) if v in e] for v in range(26)]
# Up to three arbitrary local rectangles. Four singleton rectangles minimize
# both cost and the number of reports once the budget reaches four.
banks = []
for k in range(5):
    families = itertools.combinations(range(1, 16), k) if k < 4 else [(1, 2, 4, 8)]
    for family in families:
        patterns = [{j for j, rows in enumerate(family) if rows & (1 << i)} for i in range(4)]
        dom = sum(1 << i for i, p in enumerate(patterns) if p and any(
            i != j and other and other <= p for j, other in enumerate(patterns)))
        banks.append((k, dom, tuple(sorted(unions(family)))))


@lru_cache(maxsize=None)
def price_local(histogram, eligible):
    best = 10**9
    for k, dominated, choices in banks:
        cost = 432*k + 216*pop(dominated & eligible)
        for forced, charged, count in histogram:
            options = [pop(charged & rows) for rows in choices if not forced & ~rows]
            if not options:
                cost = best
                break
            cost += count * min(options)
            if cost >= best:
                break
        best = min(best, cost)
    return best


def cutprice(hot, warm):
    eligible = set(edges)
    for p, line in edges:
        for left_index in es[line]:
            other_point = edges[left_index][0]
            if other_point == p:
                continue
            for right_index in es[p]:
                other_line = edges[right_index][1]
                if other_line == line:
                    continue
                both_cold = edges[left_index] not in hot and edges[right_index] not in hot
                if not any(other_point in col and other_line in col and (both_cold or t in warm)
                           for t, col in enumerate(neg)):
                    eligible.discard((p, line))
    total = 0
    for v in range(26):
        local = [edges[i] for i in es[v]]
        allowed = sum(1 << i for i, e in enumerate(local) if e in eligible)
        cold = sum(1 << i for i, e in enumerate(local) if e not in hot)
        neighbors = [b if a == v else a for a, b in local]
        histogram = Counter()
        for t, col in enumerate(neg):
            if v in col:
                continue
            charged = 15 if t in warm else cold
            forced = sum(1 << i for i, w in enumerate(neighbors) if w in col) & charged
            histogram[forced, charged] += 1
        total += price_local(tuple(sorted((a, b, n) for (a, b), n in histogram.items())), allowed)
    mandatory = len(neg)*52 - (len(neg)-len(warm))*len(hot)
    return len(eligible), (total - 216*len(eligible) - mandatory + 431) // 432


# The existing matching-cover verifier builds the projectivities from frames.
group = runpy.run_path(str(notes / 'quadrangle-four-clauses.py'))['group']()
perms = [tuple(edges[g[es[v][0]]][int(v >= 13)] for v in range(26)) for g in group]


def orbit_reps(n, previous):
    seen, reps = set(), []
    for mask in previous:
        for v in range(26):
            if mask & (1 << v):
                continue
            candidate = mask | (1 << v)
            if candidate in seen:
                continue
            vertices = [i for i in range(26) if candidate & (1 << i)]
            seen.update(sum(1 << perm[i] for i in vertices) for perm in perms)
            reps.append(candidate)
    assert len(seen) == math.comb(26, n)
    return reps


def supports(n, minimum):
    line_masks = [sum(1 << p for p, l in edges if l == 13+j) for j in range(13)]
    seen = set()
    for a in range(max(1, n-13), min(13, n-1)+1):
        for points in itertools.combinations(range(13), a):
            mask = sum(1 << p for p in points)
            counts = [pop(mask & line) for line in line_masks]
            if sum(sorted(counts, reverse=True)[:n-a]) < minimum:
                continue
            for lines in itertools.combinations(range(13), n-a):
                if sum(counts[l] for l in lines) < minimum:
                    continue
                vertices = points + tuple(13+l for l in lines)
                if sum(1 << v for v in vertices) in seen:
                    continue
                seen.update(sum(1 << perm[v] for v in vertices) for perm in perms)
                yield vertices


def forcedwarm(flags, repeated):
    retained = [e for e in flags if not set(e) & repeated]
    remaining = {v for e in retained for v in e}
    warm = set()
    while remaining:
        stack = [min(remaining)]
        component = set(stack)
        while stack:
            v = stack.pop()
            for a, b in retained:
                if v != a and v != b:
                    continue
                other = b if a == v else a
                if other not in component:
                    component.add(other)
                    stack.append(other)
        remaining -= component
        points = {v for v in component if v < 13}
        lines = component - points
        warm.update(j for j, col in enumerate(neg) if col & points and col & lines)
    return warm


def splits(leaves):
    seen = set()
    for mask in range(1, (1 << len(leaves))-1, 2):
        left = tuple(v for j, v in enumerate(leaves) if mask & (1 << j))
        right = tuple(v for j, v in enumerate(leaves) if not mask & (1 << j))
        pair = tuple(sorted((left, right), key=lambda part: (len(part), part)))
        if pair not in seen:
            seen.add(pair)
            yield pair


@lru_cache(maxsize=600)
def values(leaves):
    if len(leaves) == 1:
        return {raw[leaves[0]]}
    result = set()
    for left, right in splits(leaves):
        for x in values(left):
            for y in values(right):
                result.update((x | y, x & y))
    return result


def minwarm(leaves, flags):
    required = sum(1 << edges.index(e) for e in flags)
    result = set()
    for a, b in splits(leaves):
        if len(a) == 1 and any(a[0] not in e for e in flags):
            # A raw OR child admits a singleton. A raw AND child misses a flag.
            continue
        left, right = values(a), values(b)
        accept_left = [x for x in left if x & required == required]
        accept_right = [y for y in right if y & required == required]
        for x in accept_left:
            for y in accept_right:
                result.add((x & y) >> 52)
        # At an OR root the second child must cover all rows that the first misses.
        groups = {}
        for x in left:
            groups.setdefault(required & ~x, []).append(x >> 52)
        for missed, xs in groups.items():
            ys = [y >> 52 for y in right if y & missed == missed]
            for x in xs:
                for y in ys:
                    result.add(x | y)
    minimal = []
    for word in sorted(result, key=pop):
        if all(other & ~word for other in minimal):
            minimal.append(word)
    return minimal


def check_raw_disjunctions():
    reps = [0]
    for size, orbit_count, lower, residual in [
            (1, 2, 27, 2), (2, 4, 41, 3), (3, 10, 51, 4),
            (4, 25, 52, 4), (5, 56, 57, 0), (6, 128, 61, 0)]:
        reps = orbit_reps(size, reps)
        failures = 0
        worst = 65
        for mask in reps:
            support = {v for v in range(26) if mask & (1 << v)}
            warm = {j for j, t in enumerate(neg) if support & t}
            warm_bound = cutprice(set(edges), warm)[1]
            worst = min(worst, warm_bound)
            if warm_bound <= 63 - size:
                hot = {e for e in edges if set(e) & support}
                failures += cutprice(hot, warm)[1] <= 63 - size
        assert (len(reps), worst, failures) == (orbit_count, lower, residual)
        print(size, 'raw literals:', orbit_count, 'orbits;', failures, 'left by the cut bound.')


def check_small_helpers():
    for g, expected_cases, expected_direct in [(7, 19, 0), (8, 106, 2), (9, 793, 4)]:
        minimum = (4*g + 16) // 5
        cases = direct = 0
        for n in range(8, g+2):
            for S in supports(n, minimum):
                induced = [e for e in edges if set(e) <= set(S)]
                for k in range(minimum, len(induced) + 1):
                    for flags in itertools.combinations(induced, k):
                        F = set(flags)
                        for repeat in itertools.combinations(S, min(g + 1 - n, n)):
                            cases += 1
                            warm = forcedwarm(F, set(repeat))
                            if cutprice(F, warm)[1] > 62 - g:
                                continue
                            direct += 1
                            assert len(repeat) == 1 and g == n
                            masks = minwarm(tuple(sorted(S + repeat)), flags)
                            for w in masks:
                                warm = {j for j in range(len(neg)) if w & (1 << j)}
                                assert cutprice(F, warm)[1] > 62 - g
        assert (cases, direct) == (expected_cases, expected_direct)
        print(g, 'inner gates:', cases, 'support/flag/repetition cases;',
              direct, 'required root enumeration.')


def pair_banks(u, v):
    neighbors = [next(w for w in edges[i] if w != u) for i in es[u]]
    baseline = 216 if u < 13 else 288
    counts = Counter((sum(1 << j for j, w in enumerate(neighbors) if w in t), v in t)
                     for t in neg if u not in t)
    required = 0
    for forced, blocked in counts:
        if blocked:
            required |= forced
    result = []
    for private in range(1, 16):
        if required & ~private:
            continue
        for triple in itertools.combinations_with_replacement(range(16), 3):
            family = (private,) + triple
            choices = unions(family)
            dominated = data['slots'](family, 15)
            cost = sum(n * (pop(private) if blocked else
                       min((pop(x) for x in choices if not forced & ~x), default=1000000))
                       for (forced, blocked), n in counts.items())
            slack = 216 * dominated + cost - baseline
            result.append((slack, family, dominated))
    return sorted(result), baseline, neighbors


def joint_states(a, b):
    states = []
    for active in range(8):
        left = [a[j+1] for j in range(3) if active & (1 << j)]
        right = [b[j+1] for j in range(3) if active & (1 << j)]
        la = lb = 0
        for x in left:
            la |= x
        for x in right:
            lb |= x
        if pop(la) != sum(map(pop, left)) or pop(lb) != sum(map(pop, right)):
            continue
        for x in ([la] if la & a[0] else [la, la | a[0]]):
            for y in ([lb] if lb & b[0] else [lb, lb | b[0]]):
                states.append((active, x, y, pop(x) + pop(y)))
    return states


def check_pair_fanout():
    for u, v, minimum, expected in [(0,1,(165,165),96), (13,14,(144,144),144),
                                    (0,14,(403,442),0)]:
        A, ba, na = pair_banks(u,v)
        B, bb, nb = pair_banks(v,u)
        assert (A[0][0], B[0][0]) == minimum
        counts = Counter((sum(1 << i for i,w in enumerate(na) if w in t),
                          sum(1 << i for i,w in enumerate(nb) if w in t), u in t, v in t)
                         for t in neg)
        trials = 0
        for ca, a, da in A:
            if ca + B[0][0] > 432:
                break
            for cb, b, db in B:
                if ca + cb > 432:
                    break
                for triple in set(itertools.permutations(b[1:])):
                    trials += 1
                    states = joint_states(a, (b[0],) + triple)
                    score = 216*(da+db)-ba-bb
                    for (fa, fb, ua, ub), count in counts.items():
                        valid = [weight for active,x,y,weight in states
                                 if (not active or not (ua or ub)) and
                                 (not ua or not x) and (not ub or not y) and
                                 not fa & ~x and not fb & ~y]
                        if not valid:
                            break
                        score += count * min(valid)
                    else:
                        assert score > 432
        assert trials == expected
        print('Three helper uses, pair', (u,v), ':', trials, 'aligned banks excluded.')


if __name__ == '__main__':
    check_raw_disjunctions()
    check_pair_fanout()
    check_small_helpers()
