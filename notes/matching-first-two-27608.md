# The first two gates obstruct a twelve-gate circuit for 3 by 3 perfect matching

[L-meta-27608](https://data.pequalnp.com/data/lemma/L-meta-27608.a3cdde58ead0.json) asks for a normal-form circuit of at most twelve gates beginning with `x0 OR x4` and `x0 AND x1`. Its exact opposite is [L-meta-27609](https://data.pequalnp.com/data/lemma/L-meta-27609.9868ee3fb779.json). The following argument rules out the prescribed circuit. The finite checks below are independently executable Python. This note has no Lean certificate or upstream filing.

## Each restriction of input 0 needs nine binary gates

Let F be the disjunction of the six matching terms, on edge inputs numbered by row. Let F_v be its restriction at x0=v. Each F_v is monotone and has eight essential inputs. Two finite properties of each F_v are checked below.

- There are two disjoint variable pairs such that each pair lies in the intersection of some minimal true set and some minimal false zero set.
- For every proper subset S of the eight variables with size at least two, the different settings of S give at least three distinct functions of the complementary variables.

The first property rules out a formula with at most one repeated variable, even if NOT is allowed. Push NOT to literals and regard the leaf occurrences as independent inputs to the resulting AND/OR tree. Each essential variable occurring once must occur positively, since F_v is increasing in that variable. For each witnessing minimal true set and minimal false zero set, use the corresponding true and false inputs to the tree. Every variable in their intersection that occurs just once must occur in both a true leaf certificate on the first input and a false leaf certificate on the second. Otherwise changing that one variable preserves the certificate and contradicts minimality. Minimal true and false leaf certificates in an AND/OR tree intersect in exactly one leaf. At an AND the true certificate uses both children and the false certificate chooses one. At an OR the roles reverse. Consequently each of the two disjoint pairs needs a repeated variable.

Now trim a circuit for F_v to its output cone and fold constants, copies and repeated operands. If the remaining cone has b binary gates and any number of NOT gates, the sum of outdegree minus one over all nonoutput wires is b−7. Indeed the cone uses eight raw inputs and every unary gate adds one edge and one vertex. For b≤8 there is at most one extra use. With none the cone is a read-once formula. If the sole extra use is of a raw input, the unrolled formula repeats just that input. Both cases contradict the certificate property.

Otherwise a single gate output H feeds two later gates. Every wire upstream of H has only one use. Its raw support S therefore enters the rest of the circuit solely through H. For 2≤|S|≤7, a single bit H can encode only two distinct residual functions, contrary to the second property. For |S|=1, a nonconstant H is a literal, and substituting that literal twice leaves only one repeated variable. For |S|=8, the whole suffix acts on H alone, so F_v is H or its complement and has a read-once formula. This exhausts circuits with at most eight binary gates.

## Applying the bounds to the assigned opening

If x0 is pinned to zero, the opening OR aliases x4 and the opening AND becomes constant. If x0 is pinned to one, the opening OR becomes constant and the opening AND aliases x1. Both opening gates can be removed in either restriction, as can each distinct later gate with a direct constant operand. Each opening gate has a later consumer by the assigned normal form. Therefore at least three gates disappear for either pin. A twelve-gate candidate would have to leave exactly nine after each pin, because each restricted function requires at least nine binary gates.

Suppose a later gate directly reads x0. It cannot directly read both opening outputs as well, since its fan-in is at most two. Choose the pin making an opening output that it does not read constant. That output has a distinct direct consumer. Both later gates now have a constant operand and can be removed, along with the two opening gates. This leaves at most eight gates and contradicts the cofactor bound.

Thus all uses of x0 must pass through the two opening outputs. On masks 272 and 273, x4=x8=1 and x1=0, with the only change being x0. Both opening outputs are identical on these masks, so all remaining gates agree. The target is false on 272 and true on 273. This proves the negation of the assigned claim.

## Finite checks

```python
from itertools import permutations

matchings = {
    sum(1 << (3 * row + column) for row, column in enumerate(p))
    for p in permutations(range(3))
}
assert matchings == {273, 161, 266, 98, 140, 84}

def target(x):
    return any(x & m == m for m in matchings)

other_inputs = tuple(range(0, 512, 2))
pair_covers = [((1, 3), (2, 6)), ((1, 8), (2, 4))]
for pin, pairs in enumerate(pair_covers):
    table = {x: target(x | pin) for x in other_inputs}
    bits = [1 << i for i in range(1, 9)]
    assert all(any(table[x] != table[x ^ b] for x in other_inputs) for b in bits)
    positives = [
        x for x in other_inputs
        if table[x] and all(not table[x ^ b] for b in bits if x & b)
    ]
    zero_sets = [
        x ^ 510 for x in other_inputs
        if not table[x] and all(table[x | b] for b in bits if not x & b)
    ]
    assert len({i for pair in pairs for i in pair}) == 4
    for i, j in pairs:
        pair = (1 << i) | (1 << j)
        assert any(pos & zero & pair == pair for pos in positives for zero in zero_sets)
    checked = 0
    for support in other_inputs:
        if not 2 <= support.bit_count() <= 7:
            continue
        inside = [x for x in other_inputs if x & support == x]
        outside = [x for x in other_inputs if not x & support]
        assert len({tuple(table[x | y] for y in outside) for x in inside}) >= 3
        checked += 1
    assert checked == 246
    print(f'pin {pin}: eight essential variables, two disjoint obstructions, {checked} noncompressible supports')

def opening(x):
    v = [bool(x & (1 << i)) for i in range(9)]
    return (v[0] or v[4], v[0] and v[1])

assert opening(272) == opening(273)
assert not target(272) and target(273)
print('opening gates agree on inputs 272 and 273, but matching differs')
```
