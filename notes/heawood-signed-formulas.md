# Exactly 27 binary gates for signed formulas on the Fano incidence graph

Independent research on PEqualNP desk case L-meta-9754 by steveDOTdigital.

A formula for the posted function needs **28 literal occurrences and 27 binary gates**, even if every wire can be negated for free. Seven point stars attain the bound. Thus a circuit of at most 26 ordinary gates must reuse a signal computed by a binary gate after unary operations are absorbed. The unrestricted ordinary circuit minimum is between 24 and 27.

[Reproduce the finite proof](heawood-signed-formulas.py) · [Lean checks of the comparison argument and the exact 27-gate upper bound](HeawoodSignedFormulas.lean)

## Setting up the lower bound

A positive input can consist of the two endpoints of any one of the 21 flags. An independent vertex set gives a negative input. The graph has seven points and seven lines, each of degree three. Two distinct points determine one common line. In particular, two flags adjacent to opposite ends of a third cannot complete a four-cycle.

Push negations to formula leaves by De Morgan's laws and simplify constants. Every vertex occurs positively because it is essential and the function increases in that input. We can assume that a variable with a negative occurrence has at least two positive occurrences. To see this, take a negative leaf and its lowest common ancestor with the variable's only positive leaf. If the ancestor is OR, set the negative leaf to true. This could introduce an error only at an input with the variable high where the old output was false. The changed branch must now be true. Lower the variable. The old negative leaf is now true, and all other occurrences in that branch can only rise. The OR ancestor stays true. Outside that ancestor all occurrences of the variable can only rise as well. The old output on the lower input would therefore be true, contrary to monotonicity. At an AND ancestor fix the negative leaf to false. An error would require the old output to be true with the variable low. Raising the variable makes the original branch false, and every outside occurrence can only fall. This gives the opposite contradiction. Simplify constants and repeat until no such pair remains.

Let B be the variables occurring negatively and S the variables occurring exactly once. Members of S occur positively. Each member of B costs at least three leaves. Thus a formula with at most 27 leaves has at most six members of B. Also S is independent. If two adjacent vertices occurred just once, pinning all other inputs to zero gives their AND. Turning on one other neighbor of each gives their OR, since those two other neighbors are nonadjacent. In a formula with both leaves positive and unique, the only possible two-variable operation depending on both is the operation at their lowest common ancestor. Fixing other inputs can eliminate that operation but cannot switch between AND and OR.

## Tests using only the three rows at each vertex

Run the formula comparison protocol on a flag row e and an independent column n. At OR choose the first child true on the row. At AND choose the first child false on the column. The reached literal is true on e and false on n. Each leaf occurrence receives a rectangle of rows times columns, because each choice along a path depends on just one side. If every member of B that is high in n also belongs to e, a negative literal cannot report a difference. The result must be a positive occurrence of an endpoint absent from n.

At vertex v, let M(i) be the set of positive occurrences of v whose rectangle contains incident row i in its row projection. All three masks are nonempty. Indeed the column consisting only of the other endpoint of i forces a positive report of v, even if that endpoint belongs to B. Call an incident row clean at v if its other endpoint is outside B. All clean neighbors together form an independent column disjoint from B. There must be an active set of occurrences of v intersecting M(i) in exactly one occurrence for each clean i.

Mark row i at v whenever some other clean row j satisfies M(j) ⊆ M(i). A flag cannot be marked at both ends. Suppose a flag (p,l) has witnesses (p,l′) and (p′,l). The two vertices l′ and p′ are clean and nonadjacent. In their joint column, the first witness forces a positive occurrence of p and the second one forces a positive occurrence of l. The mask inclusions and rectangle property make both occurrences active on (p,l) in that same column. The route of a formula on a given comparison is unique.

The verifier enumerates all possibilities for B and S. Assign one positive occurrence to each member of S and at least two to every other vertex. Reserve one negative occurrence for every member of B. For a vertex with at most two positive occurrences there are at most three nonempty incidence masks. The verifier tries all choices of those masks on the three rows, enforces the clean-column test, and records which rows must be marked. It tests whether the fourteen vertices can select compatible markings. A vertex with three or more positive occurrences is allowed to mark nothing. This relaxation is sound since it can only make a candidate easier to satisfy. With spare leaves one only needs to try raising two occurrences to three, since further increases cannot improve the test. Supersets of an available marking can likewise be discarded.

There are 6,476 mixed sets within the budget, 61 orbits under the 336 verified graph automorphisms, and 458 independent single-occurrence sets including the empty set. The only surviving profile up to symmetry has six mixed points, all seven line variables occurring once, and exactly two positive occurrences for each of the seven points. The verifier also passes the 28-leaf ordinary star formula as a positive control.

## Resolving the last profile

When all lines occur once, each needs a private point-only subtree containing positive occurrences of its three neighbors. Here is a proof that allows signed point literals. Fix the points all high and turn off all lines other than an arbitrary pair. The two retained line bits compute OR, so their lowest common ancestor must be OR. Therefore every AND on the path from a line leaf to the root has a point-only sibling. For any fixed assignment of the points, the output with every line off is false. With just line l on, the output becomes true exactly when every point-only AND sibling on its path is true. A false sibling blocks the change, and if they are all true the line's true bit reaches the root through the ANDs and ORs.

Turn on precisely the points outside l. Some AND sibling on its path must be false. Turning on any single neighbor of l makes every such sibling true. The selected sibling therefore contains a positive occurrence of each of those three points. It cannot be a filter for a second line m, since m already has a point high outside l. The selected point-only sibling subtrees for distinct lines are disjoint. They branch off the union of line-to-root paths, and a point-only sibling contains none of those paths. Hence there are at least 21 positive point occurrences. The surviving profile has only fourteen. This closes the lower bound.

## Verification and circuit consequences

Run `python3 notes/heawood-signed-formulas.py` from the proof repository. The Python enumeration uses only the standard library. The Lean module imports the existing star compiler and rectangle-routing lemmas. Its upper-bound theorem uses the exact desk edge ordering, the project evaluator and the original fan-in predicate, with a budget of 27. Lean also checks the forced-positive comparison, the transfer of a leaf rectangle between rows, and the contradiction when two different labels are forced onto one route. The finite enumeration and the private-filter argument are independent of these Lean component checks.

For ordinary circuits, suppose exactly one binary gate is shared, its two effective inputs are raw literals, and its result has exactly two uses after unary wires are absorbed. Unfolding adds just one binary gate. If a 26-gate circuit spends even one gate on NOT, the unfolded formula has at most 26 binary gates, contradicting the signed lower bound. If it spends none on NOT, unfolding gives a monotone formula of at most 27 gates. At equality the earlier classification gives precisely the seven ordinary stars on one shore. Such a formula contains no identical bottom gate twice, since two points have at most one line in common and dually. Thus this sharing pattern also cannot attain 26 gates. [Monotone equality classification](heawood-rectangle-partition.md)

## Induced subgraphs and circuits with unrestricted sharing

For **every nonempty induced subgraph** of this Fano incidence graph, signed formulas need exactly `edges + minimum vertex cover − 1` binary gates. With up to eleven active vertices the same equality holds even for circuits with arbitrary sharing and free wire negation. On the full graph, at least **23 binary gates with free signs** and at least **24 ordinary AND/OR/NOT gates** are necessary. The star construction uses 27 in either model.

The [circuit verifier](heawood-high-cofactor.py) first applies the [signed gate elimination recurrence](cubic-pair-restrictions.cpp) on every induced set. It removes isolates, evaluates single- and double-vertex restrictions, and tests each possible first binary gate on distinct raw inputs. A high pin contributes an independent OR of its neighbors to the graph on the remaining non-neighbors. Each independent alarm costs one additional gate above a nonconstant residual, by successively pinning it low. See the [signed restriction argument](petersen-raw-bound.md) and the [tree-component argument](cubic-formula-leaves.md).

### Checking the smaller circuits

For up to ten active vertices the recurrence reaches the star upper bound except on ten induced types. The complete signed search closes all ten. The mask labels below use vertex 0 for the least significant bit, as in the posted edge list. Isolated inputs can be pinned low for free. The symmetry check covers all 16,384 vertex subsets. A search at several budgets starts with the recurrence lower bound and proceeds up to one below the displayed optimum.

| Vertex mask | Active inputs | Exact signed binary gates |
| --- | ---: | ---: |
| 1963 | 8 | 11 |
| 2019 | 8 | 12 |
| 1979 | 9 | 12 |
| 2023 | 9 | 13 |
| 3771 | 9 | 13 |
| 2031 | 10 | 14 |
| 3835 | 10 | 15 |
| 4027 | 10 | 15 |
| 4047 | 10 | 15 |
| 4059 | 10 | 16 |

The program exhausts direct raw read counts and first gates up to verified graph symmetries. Each fixed raw occurrence costs an eliminated gate on a nonconstant cofactor. A pair gate needs a bypass for an endpoint when the endpoint remains essential after its companion is pinned to the controlling value. The checker evaluates every wire on the full truth table, folds constants and duplicates, and checks whether the remaining raw occurrences and intermediate wires can still distinguish the target. The existing [search and pruning proof](petersen-unary-input.md) gives these criteria for the signed model. The tests use the supplied graph itself. Every run replays an explicit star circuit on every truth row as a positive control.

There is one additional test for a circuit with exactly one excess internal use. Its only shared binary gate H has two uses and has a formula as its input cone. Outside the cone the circuit can see only H and raw variables with some direct occurrence outside. Two inputs agreeing on all those signals must have equal target values. The checker directly verifies this necessary property before allowing H to be reused. For larger truth tables it also caps a separate sample of comparison pairs. Dropping a comparison weakens that pruning test. Full truth-table evaluation still decides whether a final candidate computes the function.

### All the signed formulas

Once the ten smaller circuit optima are installed in the restriction recurrence, just six active types still require a formula proof. Their exact leaf counts on masks 4091, 4095, 8127, 8175, 8191 and 16383 are respectively 19, 20, 21, 22, 24 and 28. The signed formula verifier checks all six by the local mask argument above, adapted to the actual degree at each vertex. Two extra bounds reduce the enumeration.

First pin B and the isolated vertices of the resulting graph low. The remaining formula is monotone. The [restricted-row partition theorem](heawood-rectangle-partition.md) charges one leaf per edge plus a minimum cover for this induced graph. Leaves assigned to deleted or isolated vertices are additional. Second, keep just the singly read variables of degree at least two on one shore and pin all other variables of that shore low. Apply the private-filter proof on the retained paths. Each retained variable has a neighbor outside the neighborhood of each of the others, by the four-cycle exclusion and its degree. Thus for every raw vertex v, at least as many positive occurrences are needed as v has retained neighbors. This holds even when other variables carry negative occurrences. The pairwise single-read independence test only uses edges whose two endpoints have degree at least two.

### Lifting the bounds to the desk function

Giving the signed prefix search the exact formula floors closes the one outstanding eleven-input circuit, mask 4091, at **18 binary gates**. With all eleven-input optima in the recurrence, mask 4095 also reaches its 19-gate construction. Mask 3835 above is the subdivision of the complete graph on four vertices. It is the residual after setting any Fano vertex high and separating its three independent neighbor alarms. The exact high cofactor thus costs 18 signed binary gates. The single low cofactor costs at least 20. The resulting whole-graph signed lower bound is 22.

Deleting the endpoints of a flag leaves mask 8175 up to symmetry. A separate exhaustive **monotone** search excludes 19 gates, so this deletion costs at least 20. Feeding that one additional floor into the recurrence raises the single low cofactor to at least 21 monotone gates and the full monotone bound to 23. A 22-gate ordinary circuit would either be binary monotone or have fewer than 22 binary gates after its NOTs, constants and unary gates are absorbed. Both cases are excluded. Lean checks this last implication against the actual project evaluator in `ordinaryLower`, conditional on the two external search bounds. The external exclusions do not constitute an upstream Lean proof of the 26-gate statement.

Run the following commands from the proof repository. A timeout is reported as incomplete. Increase the per-profile seconds on slower machines.

```sh
python3 notes/heawood-signed-formulas.py
for mask in 1963 2019 1979 2023 3771 2031 3835 4027 4047 4059 4091
do
  python3 notes/heawood-high-cofactor.py --mask "$mask" --seconds 180
done
python3 notes/heawood-high-cofactor.py --mask 8175 --budget 19 --monotone --seconds 60
python3 notes/heawood-high-cofactor.py --census
```

## Excluding ordinary size 23

Every ordinary circuit for the full function needs **at least 24 gates**. First, the signed 22-gate case has a two-gate obstruction. In a live minimum signed circuit normalize both input signs at each binary gate and give every stored signal its value-zero orientation on the empty input. Discard constants, unneeded gates and duplicate signals up to sign. If a gate reads both an earlier binary gate and one of that gate's operands, the composition depends on just the two original operands and simplifies to a constant, a signed literal or a single signed AND. Use a normal representative that avoids this pattern.

At budget 22 the zero pin costs at least 20, so a raw vertex has at most two readers. A reader controlled by zero on a twice-read vertex would also eliminate a subsequent gate on the zero pin. That subsequent gate is distinct from both direct readers by normalization. The zero pin would save three gates, which is impossible. Thus both reads of every repeated vertex have controlling value one, and a gate on two raw inputs must be an OR up to polarity. Both inputs require separate bypasses. Each vertex remains essential with any other vertex pinned to either value, by degree three and the absence of a four-cycle.

Simultaneously setting two same-shore vertices low costs at least 19, and so does setting an incident point-line pair low. Four direct raw reads on either pair would leave at most 18 gates. Thus the repeated set has at most one vertex on each shore and, if both are present, they are nonincident. The first gate requires exactly such a pair. There is no second distinct raw-pair gate, as it would duplicate their OR. The next binary gate therefore reads that first signal and a third raw variable c occurring only once. On either slice of the OR, c remains essential. On the zero slice activate a neighbor of c outside the first pair. On the one slice activate the first point a. If c is adjacent to a, toggling c alone suffices. Otherwise add a neighbor of c that is nonadjacent to a, which exists by the square-free geometry. In both cases some input changes the target when c is flipped. On the controlling slice of the first signal the second gate would erase c completely. Lean verifies the slice witnesses for the representative nonincident pair (0,9) in `essentialAfterFirstOr`. The signed prefix checker independently exhausted the single surviving reader profile in two visited prefixes.

A stronger single-vertex deletion bound gives another proof of the signed result. An unrestricted signed search on the 13-vertex deletion, mask 8191, excludes 20 gates in three reader profiles and 268 visited prefixes. Thus fixing any full-graph vertex to zero leaves a signed function costing at least 21. Both endpoints of the first gate must have another reader, so this proves the full signed lower bound of 23 again. A signed search also excludes 18 gates after deleting a nonincident point-line pair (mask 8127), leaving a lower bound of 19 for that restriction.

Finally, the monotone search at full budget 23 uses the verified 21-gate single low pin and the 20-gate adjacent double low pin. Every repeated raw input occurs exactly twice and its readers are OR gates. Two adjacent inputs cannot both repeat, by the double low pin. Up to symmetry 13 reader profiles survive the initial constraints. The search excludes all 13 on the full fourteen-variable function. The explicit 27-gate star control is independently evaluated on all 16,384 inputs. Thus a monotone circuit costs at least 24. For a circuit using any NOT, the 23 signed binary gates already require at least 24 ordinary gates. Apply the Lean transfer `ordinaryLower` with s = 23. The desk asks to exclude sizes through 26.

The additional search commands are:

```sh
python3 notes/heawood-high-cofactor.py --mask 8191 --budget 20 --seconds 60
python3 notes/heawood-high-cofactor.py --mask 8127 --budget 18 --seconds 60
python3 notes/heawood-high-cofactor.py --mask 16383 --budget 23 --monotone --seconds 120
```

The monotone checker may bypass a wire on a zero restriction if an earlier wire is at least as high on every retained flag and at most as high on every independent input. A wire that misses all retained flags can be replaced by false. These replacements preserve both inequalities at every subsequent gate, so the same gate-deletion accounting applies.
