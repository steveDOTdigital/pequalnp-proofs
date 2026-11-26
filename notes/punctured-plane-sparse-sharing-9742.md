# Shared gates on the punctured incidence plane

[L-meta-9742](https://pequalnp.com/lemma#L-meta-9742) asserts that the posted 26-input graph needs at least 63 binary monotone gates. [L-meta-9741](https://pequalnp.com/lemma#L-meta-9741) is its exact negation. Its 51 flags are the edges from p to line p+d modulo 13, d in {0,4,10,12}, except (0,0). The graph function F accepts an input if both endpoints of some flag are true. A flag input has precisely those two endpoints true. A wire is safe if it is false on every independent input of the graph.

**Result.** Every circuit computing F in at most 62 gates has a shared internal wire which is unsafe and is true on at least six distinct flag inputs. This allows any number of shared wires and any number of reads. The usual 13 point stars use exactly 63 gates. We have no unrestricted lower bound of 63.

The same bound holds if, in addition to safe wires and wires true on at most five flags, we allow shared wires that reject all singletons and whose active flags form a forest satisfying

    sum over nonempty edge components D of max(0, |E(D)| − 4) ≤ 4.

This includes arbitrarily many four-edge components up to the available graph size. Deleting edges preserves the condition. For a split component the sum of the positive excesses of the pieces cannot exceed the old positive excess.

## Formula lower bound with missing positive rows

Suppose a formula accepts a set T of required flag inputs and rejects every independent input of the original graph. It uses at least |T|+ν(T)−1 binary gates, where ν is maximum matching size. This is the physical-leaf case of the [two-shore rank bound](plane-pair-sharing-3773.md#arbitrarily-many-raw-pairs-on-both-shores). Here is a proof for partial specifications.

Take required flags as rows and independent sets as columns. Starting at the output, a row chooses a true operand of each OR and a column a false operand of each AND, resolving ties in a fixed order. Each leaf receives a rectangle on which its variable is true on the row and false on the column. For flag (p,l) take its comparison column to be all other points on l together with all other lines through p. This column is independent since the graph has no four-cycle. On the diagonal the reported variable is one endpoint. For any other required row sharing a vertex with this flag, the comparison column contains that row's other endpoint and forces the common vertex to be reported.

Fix vertex v. Take the k incident required rows whose diagonals report their other endpoint. In the matrix of reports of v, the corresponding square has zeros on the diagonal and ones elsewhere. The column given by the entire opposite shore is all ones on these rows. Subtracting each comparison column from that common column gives k unit vectors. If some diagonal reports v, add that row too. It is one on the common column and on all k comparison columns, increasing rank by one. This includes k=0. Summing over vertices counts every edge in T once, plus the number of vertices reported by diagonals. Those vertices cover T, so there are at least ν(T) of them. Each leaf supplies at most one unit of rank for its own label, giving the claimed gate bound. The empty case only asks for at least −1 gates.

## Removing shared gates and accounting for the missing rows

Work on a partial circuit which rejects every independent input and must still accept a retained set of flags. Remove unused gates and simplify constants, copies and equal arguments. Count reads at distinct live gates. If a shared internal wire remains, take an earliest one H in topological order. Its entire producer is a private formula with t gates: a nonraw ancestor read elsewhere, including twice inside the cone, would be an earlier shared gate. Let r ≥ 2 be the number of readers of H.

* If H is safe, replace H by zero at all its readers. Propagate constants and join the residual output and the original private H by OR, omitting a constant operand if possible. No required row is lost. When H was false the old computation is unchanged, and when H was true the new output is true. Independent inputs keep output zero. At least r reader gates disappear and at most one new gate is needed.
* If H rejects all singletons, write B for the flags on which H is true, b for their number and d for their number of distinct endpoints. Set H to zero and delete its entire producer. Each immediate reader folds to a copy or constant, even when readers feed one another. At least t+r gates disappear and only flags in B may be lost. Every endpoint in B is essential to H, since dropping it from its flag leaves a rejected singleton. Hence t ≥ d−1. For a nonempty forest with c edge components, d=b+c. The saving is at least b+c+1. Under the forest condition above, b ≤ 4c+4, so this pays at least 5b/4. If b ≤ 5, the flag graph automatically is a forest by bipartiteness and absence of four-cycles, and c+1 ≥ b/4. An empty B costs no rows.
* Otherwise a small H accepts a singleton x. The graph has two degree-three vertices, the endpoints of the deleted flag, and they are nonadjacent. All other degrees are four. Two different vertices together meet at least six flags. Monotonicity and the five-flag limit thus make x the only accepted singleton. Substitute raw x for H at every reader and remove the producer. This can only decrease outputs, and it preserves every row containing x. At most b ≤ 2 rows can be lost, namely active flags outside the star at x. Their endpoints and x itself are essential to H. For x, use the empty input, which H rejects since otherwise all flags are active. A binary formula with t gates has at most t+1 distinct essential variables, giving t ≥ d where d counts endpoints of the b exceptional flags. For b positive they form a forest with at least one component, so t ≥ b+1 ≥ 5b/4. When b=0 at least one gate still disappears.

These operations preserve the hypotheses on surviving shared wires. Under a substitution, all old gate functions decrease pointwise. A folded gate that aliases a surviving wire has exactly that wire's new function. If a nonraw representative has multiple outgoing reads after folding, its class of aliased original gates contained a branch: a chain of gates with at most one live use each cannot acquire two outgoing reads. Thus the representative is bounded pointwise by the old function of a previously shared gate in that class. Safety and the five-flag bound pass to smaller functions. For a cold forest wire, rejection of singletons persists and the active edge set can only shrink. In the safe case the detached private cone acquires just one use; the appended output OR is unshared. Deleting dead gates creates no reads. This establishes the invariant even when readers themselves had fanout. Every operation strictly reduces the gate count, so the remainder is a formula or constant.

Let K be the number of distinct flag rows given up during the process. The savings sum to at least 5K/4, even if a charged row was already given up earlier. The four shifts partition the original edges into matchings. Among the 51−K surviving edges at least ceil((51−K)/4) belong to one matching. Applying the partial formula bound to the remainder gives the original circuit size

    s ≥ ceil(5K/4) + (51−K) + ceil((51−K)/4) − 1 ≥ 63.

The last inequality follows by adding the unrounded terms to get 62.75 and using integrality. The construction and this lower bound establish the sharp size for the stated classes.

## The first cyclic case

For a cold helper with six active flags, the forest case already pays for the cut. A cyclic set of six flags is exactly a six-cycle with six endpoints. The deletion also pays unless t=5 and r=2. At t=5 the six essential variables exhaust the six leaf positions, so its producer is read-once. An OR root would have two cold children with disjoint variables, since even one accepted singleton would turn on the root. Each active flag must lie wholly in one child, impossible for a connected cycle using all six variables. For an AND root each flag must meet both children, since an input-free side evaluates to zero. Thus the root partition is the unique bipartition of the cycle. Each child accepts each of its three singleton inputs and equals their disjunction by monotonicity. The one cyclic configuration left by this accounting is consequently an AND of a three-point OR and a three-line OR with exactly two reads. Other shared wires may coexist. This classification does not cover helpers accepting two singletons or helpers active on more than six flags.

## Finite checks

The negative catalogue statement has hash `sha256:f0cb19caced79cccf83287cb169a2f860d767188c25c60b1f035264d086be383`. We compared both live Lean statements and all 51 posted edge pairs. The following Python replay checks the geometry, the claimed upper circuit on every minimal positive and on a cofinal family of 8,192 independent inputs, and each possible loss budget. The shared-gate elimination is a written argument.

```python
from itertools import combinations
E = {(p, 13+(p+d)%13) for p in range(13) for d in (0,4,10,12)} - {(0,13)}
P, L = range(13), range(13,26)
N = [set() for _ in range(26)]
for p,l in E:
    N[p].add(l)
    N[l].add(p)
assert len(E)==51 and sorted(map(len,N))==[3]*2+[4]*24
assert all(len(N[p] & N[q])<=1 for p,q in combinations(P,2))
stars = [{e for e in E if v in e} for v in range(26)]
two = [len(a|b) for a,b in combinations(stars,2)]
assert min(two)==6 and two.count(6)==7
matchings = [{(p,l) for p,l in E if (l-13-p)%13==d} for d in (0,4,10,12)]
assert [len(M) for M in matchings]==[12,13,13,13]
assert all(len({p for p,l in M})==len({l for p,l in M})==len(M) for M in matchings)
assert set.union(*matchings)==E
# Build the actual 63 binary gates in topological order.
gates=[]
def gate(op,x,y):
    gates.append((op,x,y))
    return 25+len(gates)
def disjoin(xs):
    a,*tail=xs
    for b in tail:
        a=gate('or',a,b)
    return a
out=disjoin([gate('and',p,disjoin(sorted(N[p]))) for p in P])
def evaluate(xs):
    bits=[v in xs for v in range(26)]
    for op,a,b in gates:
        bits.append((bits[a] and bits[b]) if op=='and' else (bits[a] or bits[b]))
    return bits[out]
assert len(gates)==63 and all(evaluate(e) for e in E)
for mask in range(1<<13):
    points={p for p in P if mask>>p&1}
    lines={l for l in L if not points & N[l]}
    assert not evaluate(points|lines)
for K in range(52):
    assert (5*K+3)//4+(51-K)+(51-K+3)//4-1>=63
print('51 flags, 8192 independent-set controls, 63 gates, minimum two-star union 6, 52 budget checks passed')
```
