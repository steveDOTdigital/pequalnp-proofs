"""Verify the majority restriction, suffix gate minima and endpoint slices for L-meta-2768."""
from itertools import combinations, product
from pathlib import Path
import runpy


data = runpy.run_path(str(Path(__file__).with_name("check-petersen-cofactors.py")))
F = data["target"]
E = tuple((1 << a) | (1 << b) for a, b in data["EDGES"])
ROWS = range(512)
NEG = tuple(r for r in ROWS if not F(r) and all(F(r | (1 << j)) for j in range(9) if not r >> j & 1))


def merge(e, i, a, b):
    return (e & i) | (e if a else 0) | (i if b else 0)


def min_majority(has_and, has_or):
    # A wire depending only on the two rising blocks has one of six monotone
    # truth tables. Dominated choices, duplicates and constants cost no gates.
    a, b, t = (sum(1 << i for i in range(8) if i >> j & 1) for j in range(3))
    target = (a & b) | ((a | b) & t)
    raw = {0, 255, a, b, t}
    if has_and:
        raw.add(a & b)
    if has_or:
        raw.add(a | b)
    layer = {frozenset(raw)}
    for depth in range(5):
        if any(target in wires for wires in layer):
            return depth
        following = set()
        for wires in layer:
            for x, y in combinations(wires, 2):
                for z in (x & y, x | y):
                    if z not in wires:
                        following.add(wires | {z})
        layer = following
    raise AssertionError("Explicit four-gate majority construction was missed")


def boundary(h):
    # With a fixed NOT operand, the monotone circuit receives (x, ¬h(x)).
    # Comparable raw assignments with different h values become incomparable.
    pos, neg = [], []
    for r in ROWS:
        value = F(r)
        if any(F(s) == value and h(s) == h(r) for j in range(9)
               if bool(r >> j & 1) == value for s in [r ^ (1 << j)]):
            continue
        (pos if value else neg).append(r)
    for r in ROWS:
        assert (any(p & r == p and h(p) == h(r) for p in pos)) == F(r)
        assert (any(n & r == r and h(n) == h(r) for n in neg)) != F(r)
    return pos, neg


def main():
    q = lambda x: bool(x & 9)
    costs = {(a,b):min_majority(a,b) for a,b in product((False,True),repeat=2)}
    assert all(v == 4 - a - b for (a,b),v in costs.items())
    print("Minimum majority suffix gates with no mixed wire, one, or both:", 4,3,2)
    x_or = 0
    crossing = 0
    for e, i in product(E, NEG):
        assert e & i != e and e & i != i
        signature = tuple(q(merge(e,i,a,b)) for a,b in product((0,1),repeat=2))
        x_or += signature == (False,True,True,True)
        if not q(e) and q(i):
            crossing += 1
            # Independent NOT input in the circuit M(x,t)=majority(F(x),q(x),t).
            for a,b,t in product((0,1),repeat=3):
                x = merge(e,i,a,b)
                assert F(x) == bool(a) and q(x) == bool(b)
                y = (F(x) and q(x)) or ((F(x) or q(x)) and t)
                assert y == (a+b+t >= 2)
    print(len(E), "minimal positives,",len(NEG),"maximal negatives,",len(E)*len(NEG),
          "diamonds;",x_or,"with the prescribed first OR supplying the union of blocks.")
    print("NOT of the prescribed OR admits",crossing,"edge/independent-set witness pairs.")
    for j in list(range(9)) + ["first OR"]:
        h = (lambda x,j=j:bool(x >> j & 1)) if isinstance(j,int) else q
        p,n = boundary(h)
        print("Forced NOT operand",j,":",len(p),"minimal positives,",len(n),"maximal negatives.")
    outside = [1,2,4,5,6,7,8]
    for a,b in product((0,1),repeat=2):
        vals = [F(data["embed"](r,outside) | a | (b << 3)) for r in range(128)]
        def bit(r,v):return bool(r >> outside.index(v) & 1)
        def explicit(r):
            v = lambda i:bit(r,i)
            if a and b:return any(v(i) for i in (1,2,4,5,8))
            if a:return any(v(i) for i in (1,4,5)) or (v(2) and v(7)) or (v(6) and v(8))
            if b:return any(v(i) for i in (2,4,8)) or (v(1) and v(6)) or (v(5) and v(7))
            ring=(1,2,7,5,8,6)
            return any(v(i) and v(j) for i,j in zip(ring,ring[1:]+ring[:1]))
        assert vals == [bool(explicit(r)) for r in range(128)]
    print("Four explicit endpoint formulas verified on all 512 inputs.")


if __name__ == "__main__":
    main()
