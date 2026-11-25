"""Check the selected-AND boundary, local leaf profiles, and five-line geometry."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations

OFFSETS = (0, 1, 3, 9)
LINES = [sum(1 << ((i + d) % 13) for d in OFFSETS) for i in range(13)]
FULL = (1 << 13) - 1


def bits(mask):
    return [i for i in range(13) if mask & (1 << i)]


def union_table(lines):
    table = [0] * (1 << len(lines))
    for i in range(1, len(table)):
        bit = i & -i
        table[i] = table[i ^ bit] | lines[bit.bit_length() - 1]
    return table


def boundary():
    covers = union_table(LINES)
    pencils = [sum(1 << i for i, l in enumerate(LINES) if l & (1 << p)) for p in range(13)]
    hits = union_table(pencils)
    maximal = []
    for ls, cover in enumerate(covers):
        points = FULL ^ cover
        if FULL ^ hits[points] == ls:
            maximal.append((points, ls))
    groups = [pencils[p] ^ 1 for p in bits(LINES[0])]
    assert all(len(bits(t)) == 3 for t in groups)
    assert sum(groups) == FULL ^ 1
    counts = Counter()
    # For each point mask, enumerate the submasks of all compatible lines.
    for points in range(1 << 13):
        allowed = FULL ^ hits[points]
        ls = allowed
        while True:
            z = bool(ls & 1)
            h = bool(points & LINES[0])
            blocked = all(ls & t for t in groups)
            can_high = not h
            can_low = not z and not blocked
            counts[z, can_high, can_low] += 1
            if can_high:
                extended_lines = ls | 1
                full_points = FULL ^ covers[extended_lines]
                assert points & ~full_points == 0
                assert (FULL ^ hits[full_points]) & 1
            if can_low:
                p = next(p for p in bits(LINES[0]) if not pencils[p] & ls)
                full_lines = FULL ^ hits[points | (1 << p)]
                assert ls & ~full_lines == 0 and not full_lines & 1
            if not ls:
                break
            ls = (ls - 1) & allowed
    positives = [(1 << p, 1 << l) for l, line in enumerate(LINES) for p in bits(line)]

    # Independent replay of the 65-gate witness on all mandatory boundary rows.
    gates = []
    def gate(op, a, b):
        assert a != b and max(a, b) < 26 + len(gates)
        gates.append((op, a, b))
        return 25 + len(gates)
    def disj(xs):
        return xs[0] if len(xs) == 1 else gate("or", xs[0], disj(xs[1:]))
    stars = [gate("and", 13+l, disj([(l+d) % 13 for d in OFFSETS])) for l in range(1, 13)]
    rest = disj(stars)
    a = gate("or", rest, disj(list(OFFSETS)))
    b = gate("or", rest, 13)
    out = gate("and", a, b)
    assert len(gates) == 65
    for positive, rows in ((True, positives), (False, maximal)):
        for points, ls in rows:
            mask = points | ls << 13
            w = [bool((1 << i) & mask) for i in range(26)]
            for op, left, right in gates:
                w.append(w[left] or w[right] if op == "or" else w[left] and w[right])
            assert w[out] == positive
            assert (w[a] and w[b]) if positive else not w[a if ls & 1 else b]
    assert max(bin(x).count('1') + bin(y).count('1') for x,y in maximal if x and y) == 10
    assert [(x,y) for x,y in maximal if not y & 1 and bin(x).count('1') + bin(y).count('1') >= 11] == [(FULL,0)]
    print("Flags", len(positives), "maximal negatives by selector",
          sorted(Counter(bool(y & 1) for _, y in maximal).items()))
    print("Independent rows", sum(counts.values()), "by selector and high/low extension", sorted(counts.items()))


def local_profiles():
    for degree in (2, 3, 4):
        for n in range(1, degree):
            masks = range(1, 1 << n)
            dominated = []
            for rows in combinations_with_replacement(masks, degree):
                if any(not any(all(bin(a & r).count("1") == 1 for r in triple) for a in masks)
                       for triple in combinations(rows, min(3, degree))):
                    continue
                dominated.append(sum(any(i != j and v & w == w for j, w in enumerate(rows))
                                     for i, v in enumerate(rows)))
            assert min(dominated) == degree - n + 1
            print("Degree", degree, "leaf slots", n, "admissible profiles", len(dominated),
                  "minimum dominated rows", min(dominated))


def geometry():
    # The two-triple core used in the compiled search. Encode each core point
    # by the subset of the five unfinished lines on which it lies.
    flags = [(0,6),(0,7),(0,9),(1,7),(1,8),(1,10),(2,5),(2,8),(2,9),
             (3,9),(3,10),(4,5),(4,6),(4,10)]
    template = [sum(1 << j for j, k in flags if k == p) for p in range(5, 11)]
    free = {frozenset((template[0], template[2])), frozenset((template[1], template[3]))}
    orbits = [{i} for i in range(11)]
    for perm in permutations(range(5)):
        masks = [sum(1 << perm[j] for j in bits(h)) for h in template]
        if sorted(masks) != sorted(template):
            continue
        move = dict(zip(template, masks))
        if {frozenset(move[h] for h in pair) for pair in free} != free:
            continue
        image = list(perm) + [5 + template.index(h) for h in masks]
        for v, w in enumerate(image):
            orbits[v].add(w)
    distinct = sorted(set(tuple(sorted(s)) for s in orbits))
    assert distinct == [(0, 1, 2, 4), (3,), (5, 6, 7, 8), (9, 10)]
    print("Two-triple core vertex orbits", distinct)
    counts = Counter()
    for u in combinations(range(13), 5):
        hood = [sum(1 << j for j, l in enumerate(u) if 1 << p & LINES[l]) for p in range(13)]
        triple = sum(len(bits(mask)) == 3 for mask in hood)
        counts[triple, max(len(bits(mask)) for mask in hood)] += 1
        if triple != 2:
            continue
        core = [p for p, mask in enumerate(hood) if len(bits(mask)) > 1]
        helpers = [set(p for p in core if LINES[i] & (1 << p)) for i in range(13) if i not in u]
        for perm in permutations(range(5)):
            moved = {p: sum(1 << perm[j] for j in bits(hood[p])) for p in core}
            if sorted(moved.values()) != sorted(template):
                continue
            image = {frozenset(moved[p] for p in s) for s in helpers if len(s) > 1}
            if image == free:
                break
        else:
            raise AssertionError(u)
    print("Five-line sets by triple count and maximum concurrency", sorted(counts.items()))


def affine_bound():
    import subprocess
    import tempfile
    from pathlib import Path
    base=Path(__file__).with_name('cubic-pair-restrictions.cpp').read_text().split('std::vector<Mask> cage(){')[0]
    with tempfile.TemporaryDirectory(prefix='pnp-affine-lower-') as td:
     exe=Path(td)/'search'
     main=r'''
    int main(){
        std::vector<int> pts={2,4,5,6,7,8,10,11,12};
        std::vector<Mask> edges(21);
        for(int i=0;i<9;++i)for(int l=1;l<=12;++l){
            int d=(pts[i]+13-l)%13;
            if(d!=0 && d!=1 && d!=3 && d!=9)continue;
            int j=8+l;edges[i]|=1u<<j;edges[j]|=1u<<i;
        }
        Bounder binary(edges,true,-1),mono(edges,true,0,nullptr,&binary);
        auto all=(1u<<21)-1;
        std::cout<<"signed "<<binary.solve(all)<<" monotone "<<mono.solve(all)<<" upper "<<mono.upper(all)<<" masks "<<mono.calls<<std::endl;
    }
    '''
     subprocess.run(['c++','-std=c++17','-O3','-x','c++','-','-o',str(exe)],input=base+main,text=True,check=True)
     subprocess.run([str(exe)],check=True)
    assert not Path(td).exists()


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--affine-bound"]:
        affine_bound()
        sys.exit(0)
    boundary()
    local_profiles()
    geometry()
