"""Verify the order-four incidence, local rank tests and special-line preprocessing bounds."""
from itertools import combinations, combinations_with_replacement

N = 21
points = range(N)
lines = range(N)
offsets = (0, 5, 7, 17, 20)
special = frozenset(range(2, N, 3))
heavy = frozenset(range(0, N, 3))
near = {p: frozenset((p + d) % N for d in offsets) for p in points}
through = {l: frozenset(p for p in points if l in near[p]) for l in lines}
pairs = [frozenset((3*i+d) % N for d in (5, 17)) for i in range(7)]
triples = [frozenset((3*i+d) % N for d in (5, 17, 20)) for i in range(7)]
alarms = pairs + triples
flags = [(p,l) for p in points for l in sorted(near[p])]
keep = [(p,l) for p,l in flags if p not in heavy or l not in special]
assert len(flags) == 105 and len(keep) == 84
assert all(len(near[p] & special) == (3 if p in heavy else 1) for p in points)
assert all(len(through[l] & heavy) == (3 if l in special else 1) for l in lines)
assert all(len(near[p] & near[q]) == 1 for p,q in combinations(points,2))
assert all(len(through[l] & through[m]) == 1 for l,m in combinations(lines,2))
assert set(triples) == {near[p] & special for p in heavy}

def independent(P, L):
    return not any(near[p] & L for p in P)

def raw(P, L):
    return set(P) | {21+l for l in L}

def match(rows):
    """Return one maximum matching, by augmenting an alternating path."""
    by_point = {p: [l for q,l in rows if q == p] for p in points}
    owner = {}
    def extend(p, seen):
        for l in by_point[p]:
            if l in seen:
                continue
            seen.add(l)
            if l not in owner or extend(owner[l], seen):
                owner[l] = p
                return True
        return False
    for p in points:
        extend(p, set())
    return {(p,l) for l,p in owner.items()}

# A cover meeting the diagonal matching once per edge is a choice of one
# endpoint per matched pair. An edge p -> l forces l's right endpoint if
# p's right endpoint was chosen. Strong connectivity leaves only two choices.
assert all((p,p) in keep for p in points)
for p in points:
    reached = {p}
    for _ in points:
        reached |= {l for q,l in keep if q in reached}
    assert len(reached) == N

extra = [frozenset(c) for k in range(2,8) for c in combinations(special,k)]
def extend_inputs(P, L):
    return raw(P,L) | {42+i for i,A in enumerate(extra) if A & L}

tested = 0
for p,l in keep:
    P = through[l] - {p}
    L = near[p] - {l}
    if l in special:
        P -= heavy
        L |= special - {l}
    assert independent(P,L)
    negative = extend_inputs(P,L)
    for q,m in keep:
        if q != p and m != l:
            continue
        diff = extend_inputs({q},{m}) - negative
        wanted = raw({q} if q == p else set(), {m} if m == l else set())
        assert diff == wanted
        tested += 1

# A truth-preserving pin of one line removes all points on it. Every other
# point keeps degree five, and a matching saturates those sixteen points.
for l in special:
    retained = [(p,m) for p,m in flags if p not in through[l]]
    assert len(retained) == 80 and len(match(retained)) == 16
    eliminated = 1 + sum(sum(q == p for q,m in keep) for p in through[l])
    assert eliminated == 17

# With the OR of all seven special lines pinned high, these 91 flags retain
# original negative crosses containing a special line. Their cover size is 21.
survive = [(p,l) for p,l in flags if (near[p] - {l}) & special]
assert len(survive) == 91 and len(match(survive)) == 21

# Enumerate supports reachable with at most two gates in a special-only
# prefix. At singleton inputs AND is intersection and OR is union.
signals = set(alarms) | {frozenset([l]) for l in special}
def next_supports(inputs):
    return {r for a,b in combinations(inputs,2) for r in (a | b, a & b)}
first = next_supports(signals)
assert max(map(len,first)) == 5
assert max(len(b) for a in first for b in next_supports(signals | {a})) == 7

# Enumerate cardinality profiles consistent with the expansion and raw bounds.
profiles = set()
for prefix in range(1,7):
    for t in range(7-prefix):
        for profile in combinations_with_replacement(range(2,8),t):
            if prefix == 1 and (any(s>5 for s in profile) or
                    len({s for s in profile if s>3})>1):
                continue
            if t == 0 or max(profile) <= 3 or sum(s-1 for s in profile) < 16+prefix:
                continue
            Rmax = 111-prefix-t
            profiles.add((prefix,t,Rmax))
            if Rmax == 105:
                assert sum(s*(7-s) for s in profile) < 7*8
            else:
                assert (prefix,profile,Rmax) == (2,(7,7,7),106)
assert profiles == {(1,5,105),(2,4,105),(2,3,106)}

# Build the upper bound and verify its symbolic input sets and its paid gates.
stars = []
for p in points:
    leaves = [21+l for l in sorted(near[p])]
    if p in heavy:
        leaves = [21+l for l in sorted(near[p] - special)] + [49+p//3]
    supported = set()
    for v in leaves:
        supported |= {v-21} if v<42 else set(alarms[v-42])
    assert supported == near[p]
    stars.append(leaves)
paid = sum(len(term) for term in stars) + len(stars)-1
assert paid == 111
print(f"{len(keep)} flags, {tested} local cells, {len(extra)} special-line OR supports")
print("Both minimum covers certified; every line pin leaves 96 required raw leaves.")
print("Special-high pin leaves 112 required raw leaves; all prefix profiles checked.")
print(f"Compressed point stars compute the exact incidence function with {paid} paid gates.")
