"""Check the schoolbook circuit and the feature symmetries for L-meta-18919."""
from itertools import permutations


def schoolbook():
    gates, ports = [], []
    for i in range(3):
        for j in range(3):
            start = 18 + len(gates)
            gates.extend(("and", 3*i+k, 9+3*k+j) for k in range(3))
            gates.extend([("or", start, start+1), ("or", start+3, start+2)])
            ports.append(start+4)
    return gates, ports


def check_product():
    gates, ports = schoolbook()
    size = 1 << 18
    mask = (1 << size) - 1
    # Column for input i: 2**i zeros alternate with 2**i ones.
    wires = []
    for i in range(18):
        block = 1 << i
        wires.append((mask // ((1 << block) + 1)) << block)
    for op, a, b in gates:
        wires.append(wires[a] & wires[b] if op == "and" else wires[a] | wires[b])
    # Independent row-by-row oracle, using intersections of three-bit sets.
    columns = [wires[o].to_bytes(size // 8, "little") for o in ports]
    right = [sum(((v >> (3*k+j)) & 1) << k for k in range(3))
             for v in range(512) for j in range(3)]
    for x in range(size):
        left, off = x & 511, 3*(x >> 9)
        byte, bit = divmod(x, 8)
        for i in range(3):
            row = (left >> (3*i)) & 7
            for j in range(3):
                assert ((columns[3*i+j][byte] >> bit) & 1) == bool(row & right[off+j])
    assert len(gates) == 45
    print("45 gates; nine outputs checked on all 262144 inputs.")


def check_encodings():
    # These are all directed edges of the three-dimensional Boolean lattice.
    covers = [(x, x | (1 << k)) for x in range(8) for k in range(3) if not x & (1 << k)]
    keep = {p for p in permutations(range(8)) if all(p[x] & p[y] == p[x] for x, y in covers)}
    coords = {tuple(sum(((x >> source) & 1) << target for target, source in enumerate(order))
                    for x in range(8)) for order in permutations(range(3))}
    assert keep == coords
    print("Exactly six of the 40320 row encodings preserve inclusion, all coordinate permutations.")


def local_check():
    # Three accepted pair rows occupy bits 0..2; six mixed negative rows
    # occupy bits 3..8. A set bit means the wire is true on that row.
    size, target = 512, 7
    def eligible(w):
        left = right = 7
        for i in range(1,7):
            if not (w >> (2+i)) & 1:
                left &= i
                right &= 7 ^ i
        return (w & 7).bit_count() > max(left.bit_count(),right.bit_count())
    free = [w for w in range(size) if not eligible(w)]
    def mask(values):
        out=0
        for w in values: out |= 1 << w
        return out
    def members(bits):
        while bits:
            single=bits & -bits
            yield single.bit_length()-1
            bits ^= single
    generated=[mask(w for y in free for w in (x&y,x|y) if eligible(w)) for x in range(size)]
    first=0
    for x in free: first |= generated[x]
    # An eligible final operand that can produce the target with x.
    partners=[mask(y for y in range(size) if eligible(y) and (x&y==target or x|y==target)) for x in range(size)]
    free_partners=0
    for x in free:free_partners |= partners[x]
    assert target not in free and not (first>>target)&1
    pairs=0
    for a in members(first):
        second=first | generated[a]
        assert not (second>>target)&1
        for b in members(second & ~(1<<a)):
            third=second | generated[b]
            for w in (a&b,a|b):
                if eligible(w):third |= 1<<w
            final_ok=free_partners | partners[a] | partners[b]
            if (third>>target)&1 or third & final_ok: return ('witness',a,b,next(members(third & final_ok),None))
            pairs+=1
    return ('excluded',len(free),first.bit_count(),pairs)



if __name__ == "__main__":
    check_product()
    check_encodings()
    result = local_check()
    assert result == ("excluded", 161, 186, 34698), result
    print("Four eligible gates excluded by checking 34698 ordered pairs of initial gates.")
