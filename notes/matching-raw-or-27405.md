# No twelve-gate normal-form matching circuit starts with a raw OR

This refutes [L-meta-27405](https://data.pequalnp.com/data/lemma/L-meta-27405.4443364fbfe9.json), whose second gate is OR of raw inputs 1 and 5. The opposite is [L-meta-27406](https://data.pequalnp.com/data/lemma/L-meta-27406.5efaa3443ef0.json). It also strengthens the [previous fixed-opening argument](matching-first-two-27608.md). The proof is a written graph argument plus finite truth-table checks. It has no Lean certificate or upstream filing.

## The cofactor with one edge present requires ten binary gates

The previous argument establishes eight essential variables, no formula with only one repeated variable, and no proper block of two or more variables that can be summarized by a single bit. Apply those facts to the cofactor F_1 with x0=1. Row and column permutations take any other chosen edge to edge 0.

Choose a circuit minimizing binary gate count for F_1, allowing complemented edges for free. Absorb each NOT into the signs on edges and on the output. Fold constants, repeated operands and gates computing raw literals, then trim the output cone. Its excess uses, the sum of outdegree minus one over all nonoutput vertices, equal b−7 for b binary gates and eight raw inputs. The prior bound gives b≥9. If b=9 there are exactly two excess uses.

If only raw inputs are shared, the resulting formula repeats at most two distinct variables. Four disjoint pairs pass the minterm and maxterm intersection test from the previous note, requiring at least four repeated variables. Therefore choose the first shared internal wire H in topological order. Its predecessors can contain no shared internal wire. Its support S has at least two variables, since a constant or literal can be eliminated. If all of S reaches the rest of the circuit through H alone, every proper such S is excluded by the earlier one-bit block test. For S equal to all eight variables the suffix reads H alone. Then the output is H or its complement. Its prefix is a formula with at most one repeated raw variable, also excluded.

Otherwise there is a raw variable x in S reaching the suffix along a path avoiding H. It must have at least two uses. This exhausts the second excess use and makes x the only such variable. Inside the cone of H each raw variable occurs exactly once, so H is a read-once signed formula on S. Once x is fixed, changing the other variables of S can reach the suffix only through one bit H. Three cases remain.

- If 2≤|S minus {x}|≤6, the finite check shows that for one setting of x there are at least three different functions of the complementary variables, from varying S minus {x}.
- If S is just x and y, the finite check verifies that y is essential for both settings of x in F_1. The read-once signed formula H on two inputs is a single AND or OR with possible complements, so one setting of x makes its output constant in y. The suffix has no other path from y.
- If S is all eight variables, fixing x leaves the suffix with only H. For each x the finite check exhibits a setting for which the restricted function fails the read-once minterm and maxterm test. In that setting the suffix could only give a constant, H, or its complement, and H restricted to the remaining variables is read-once after simplifying.

Thus no case with nine binary gates is possible, even with free complements.

## Excluding a raw OR

Suppose a normal-form circuit for perfect matching with at most twelve gates has g=x OR y for two raw inputs. The target can distinguish x=0 from x=1 when y=1, as checked for all thirty-six pairs below. Therefore some gate other than g must read x. The gate g is not the output because the target depends on every input, so it too has a consumer. No gate can read both g and x. An AND of those signals duplicates x, and an OR duplicates g. Both would violate normal form.

Pin x to one. This removes g, a direct consumer of g and a distinct direct reader of x, since all three simplify on a constant operand. At most nine gates remain. The cofactor requires ten binary gates, a contradiction that excludes the assigned opening regardless of its first gate.

The same bound rules out a NOT of a raw input x in a twelve-gate normal-form circuit. Pinning x=1 removes the NOT and at least one consumer. A direct reader of x other than that NOT cannot share a gate with the negated signal, since their AND or OR is constant. Any such distinct direct reader would make three removed gates. For the same reason the NOT has a single consumer, which must be binary because double negation would duplicate x. As ten binary gates must survive the pin, all other gates in the original circuit must be binary. The output can depend on x only through its negation and hence is decreasing in x, contrary to positive essentiality.

## Finite checks

```python
from itertools import permutations, combinations
M=[sum(1<<(3*i+r) for i,r in enumerate(s)) for s in permutations(range(3))]
def f(a):return any(a&m==m for m in M)
rows=tuple(range(0,512,2))
bits=[1<<i for i in range(1,9)]
obstructions=((1,8),(2,4),(3,7),(5,6))
def overlap(table, allowed, pair):
 pos = [r for r in table if table[r] and all(not table[r^b] for b in allowed if r&b)]
 neg = [r for r in table if not table[r] and all(table[r|b] for b in allowed if not r&b)]
 return any((p & ~n & pair) == pair for p in pos for n in neg)
table={x:f(x|1) for x in rows}
assert all(overlap(table,bits,(1<<i)|(1<<j)) for i,j in obstructions)
assert len({i for pair in obstructions for i in pair})==8
blocks=pairchecks=fullchecks=0
for shared in bits:
 other=[b for b in bits if b!=shared]
 rest=[x for x in rows if not x&shared]
 for y in other:
  assert all(any(f(x|s|1)!=f((x^y)|s|1) for x in rest) for s in [0,shared])
  pairchecks+=1
 for support in rest:
  if not 2<=support.bit_count()<=6: continue
  ins=[x for x in rest if x&support==x]
  outs=[x for x in rest if not x&support]
  assert any(len({tuple(f(x|y|s|1) for y in outs) for x in ins})>=3 for s in [0,shared])
  blocks+=1
 assert any(overlap({x:f(x|s|1) for x in rest},other,a|b)
            for s in [0,shared] for a,b in combinations(other,2))
 fullchecks+=1
print('four disjoint pairs,',pairchecks,'essential pairs,',blocks,'proper blocks,',fullchecks,'full blocks')
# All raw OR pairs need a separate reader of the pinned operand.
for i,j in combinations(range(9),2):
 a,b=1<<i,1<<j
 assert any(f(x) and not f(x^a) and x&a and x&b for x in range(512))
print('all 36 raw OR pairs tested')
```
