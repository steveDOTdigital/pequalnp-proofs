"""Petersen binary-gate lower bounds by first-gate elimination, with free NOTs.

Use a smallest circuit and represent OR by an AND with signed wires and signed
output. Its first gate G reads distinct essential inputs p,q. Write a,b for
their respective values which force G to zero. For three or more essential
inputs, G necessarily has a consumer. Fixing p removes G; fixing p=a also removes
a consumer because its operand from G becomes constant.

If p is essential on the q=b slice, p has another reader R bypassing G.
Setting p removes R too. At p=a we can count G, R and a consumer of G as
three distinct gates: if this were impossible, the only consumer of G and
the only other reader of p would be the same gate. This gate combines a
literal of p with a literal of G. Their composition is a constant, a literal,
or one signed AND of p and q (split on p at its controlling value to see
this). It would replace two gates by at most one, violating minimality.
The same argument holds with p and q exchanged.

Take the maximum of the four restriction bounds for each first gate, then
the minimum over all possible first gates. A connected circuit on n essential
inputs needs at least n-1 binary gates.
The recurrence gives lower bounds and need not give exact circuit sizes.

For the full graph it gives 12, and for the deletion of vertex 0 it gives 10.
Any circuit beginning with AND(0,2) needs at least 13 binary gates. Indeed, a
circuit of at most 12 would attain the unrestricted lower bound and be globally
minimal. Input 0 remains essential with input 2 zero, so setting input 0 to
zero eliminates at least three binary gates, leaving at most nine for a
function requiring ten. Consequently a 15-gate witness with at least two NOTs
must have exactly two NOTs. This lower bound leaves existence with two open.
"""
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import runpy


checks = runpy.run_path(str(Path(__file__).with_name("check-petersen-cofactors.py")))


@lru_cache(None)
def restrict(values, column, bit):
    return tuple(value for row, value in enumerate(values) if (row >> column) & 1 == bit)


@lru_cache(None)
def lower(values):
    width = len(values).bit_length() - 1
    essential = checks["support"](values, width)
    if len(essential) < width:
        reduced = tuple(values[checks["embed"](row, essential)]
                        for row in range(1 << len(essential)))
        return lower(reduced)
    if width <= 2:
        return max(0, width - 1)

    bounds = []
    for p, q in combinations(range(width), 2):
        for a, b in product((0, 1), repeat=2):
            fixed_q = restrict(values, q, b)
            fixed_p = restrict(values, p, a)
            reads_p = restrict(fixed_q, p, 0) != restrict(fixed_q, p, 1)
            # The earlier column p was removed, so q now has index q-1.
            reads_q = restrict(fixed_p, q-1, 0) != restrict(fixed_p, q-1, 1)
            bounds.append(max(lower(fixed_p) + 2 + reads_p,
                              lower(restrict(values, p, 1-a)) + 1 + reads_p,
                              lower(fixed_q) + 2 + reads_q,
                              lower(restrict(values, q, 1-b)) + 1 + reads_q))
    return max(width - 1, min(bounds))


if __name__ == "__main__":
    full = tuple(checks["target"](row) for row in range(512))
    assert lower((False, False, False, True)) == 1
    nine = lower(full)
    eight = lower(restrict(full, 0, 0))
    seven = lower(restrict(restrict(full, 2, 0), 0, 0))
    assert (nine, eight, seven) == (12, 10, 8)
    # If the prescribed circuit is globally nonminimal, it exceeds the universal
    # bound by at least one. Otherwise setting input 0 to zero deletes three
    # gates, since input 0 is essential even on the input-2-zero slice.
    fixed_two = restrict(full, 2, 0)
    assert restrict(fixed_two, 0, 0) != restrict(fixed_two, 0, 1)
    prescribed = min(nine + 1, eight + 3)
    assert prescribed == 13
    print("Binary-gate lower bounds with free inversions:")
    print("Nine-input Petersen edge function:", nine)
    print("With input 0 set to zero:", eight)
    print("With inputs 0 and 2 set to zero:", seven)
    print("Nine-input function, first gate AND(0,2):", prescribed)
