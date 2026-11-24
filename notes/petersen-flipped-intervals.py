"""Exact descending intervals of the Petersen edge function with one input flipped."""
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]


def graph(row):
    return any((row >> i) & (row >> j) & 1 for i,j in EDGES)


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub-1) & mask


def intervals(i):
    bit = 1 << i
    # The helper is increasing and independent of the flipped coordinate.
    # Inclusion of raw physical rows is exactly the order on the supplied pins.
    values = [graph(y ^ bit) for y in range(512)]
    lows, highs, middle = set(),set(),set()
    pairs = 0
    for high in range(512):
        if values[high]:
            continue
        for low in subsets(high):
            if not values[low]:
                continue
            pairs += 1
            lows.add(low)
            highs.add(high)
            middle.update(low | extra for extra in subsets(high ^ low))
    forced_zero = {z for y in lows for z in subsets(y)}
    forced_one = {z for z in range(512) if any((z & w) == w for w in highs)}
    assert forced_zero.isdisjoint(forced_one)
    assert all(not y & bit for y in forced_zero)
    assert all(y & bit for y in forced_one)
    return pairs,len(forced_zero),len(forced_one),len(middle)


def small_prefixes(i):
    from itertools import combinations

    raw = [sum(1 << r for r in range(512) if r & (1 << j)) for j in range(9)]
    sources = raw + [raw[0] | raw[6]]
    one = {h for a,b in combinations(sources,2) for h in (a | b,a & b)} - set(sources)
    two = {h for a in sources for b in one for h in (a | b,a & b)} - set(sources) - one
    pairs = [r for r in range(512) if not r & (1 << i) and graph(r | (1 << i)) and not graph(r)]
    def fits(h):
        return all(not (h >> r) & 1 and (h >> (r | (1 << i))) & 1 for r in pairs)
    assert {h for h in sources if fits(h)} == {raw[i]}
    assert not any(fits(h) for h in one)
    possible = {h for h in two if fits(h)}
    below = {h for h in possible if not h & ~raw[i]}
    above = {h for h in possible if not raw[i] & ~h}
    assert possible == below | above
    return len(below),len(above)


if __name__ == "__main__":
    for i in (1,2,3,4,5,7,8):
        print(i,*intervals(i),*small_prefixes(i))
