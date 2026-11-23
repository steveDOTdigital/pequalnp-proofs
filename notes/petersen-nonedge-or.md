# A necessary first OR on a Petersen nonedge uses seven endpoint-dependent gates

For L-meta-651 shard 2, put u = x₀, v = x₂, and let the first gate be q = u OR v. Count a gate if it is reachable from either endpoint and reaches the circuit output. In a minimum unrestricted circuit with this first gate, **at least seven gates are counted**, including q. A nineteen-gate minimum of this kind can therefore have at most twelve gates that process only the other inputs. The seven-gate bound is sharp when arbitrary signals computed from those other inputs are available for free.

## Cutting the circuit at the outside signals

Discard unused gates. If q has no path to the output it can be deleted. Otherwise remove q temporarily and make its output a separate input to the suffix. Only u, v, q, and signals independent of both endpoints can now enter the remaining counted gates. These last signals may be raw outside inputs or wires computed entirely outside.

Fixing the outside variables gives five distinct output functions of u and v. With all outside bits zero the output is zero. Turning on just vertex 4 selects u, just vertex 3 selects v, and just their common neighbor 1 selects u OR v. Turning on vertices 3 and 4 selects constant one. More generally the output is K OR (u AND A) OR (v AND B), where K detects edges entirely outside and A,B detect an active neighbor of u,v respectively.

The suffix must read u and v separately. Without u it could not compute the projection u on the two settings where v = 1 and q = 1, and the symmetric argument applies to v. It must also receive at least three distinct outside signals, since two bits could distinguish at most four functions of the endpoints. Thus its output cone connects at least six sources including q.

Suppose at most six gates were counted originally. The suffix has at most five gates. A connected circuit with six sources requires five binary gates, even if unary gates are allowed: the underlying undirected graph is connected, and each binary gate adds at most two edges. Equality forces six sources, five binary gates, no unary gate and a single use of every non-output wire. The suffix is therefore a read-once AND/OR tree on u,v,q and three outside signals. One can test its three outside signals on all eight combinations, even when some combinations do not occur in the original circuit.

## Checking every possible tree

Enumerate unordered binary root partitions of each subset of the six labeled leaves. Pair each tree from the left half with each tree from the right half, and try AND and OR at the root. For each formula keep two 32-bit tables, one using q = u OR v and the other q = true. Each block of four bits ranges over u,v at a fixed outside setting.

There are 30,240 labeled formulas. Exactly 162 can produce all five required four-bit rows when q = u OR v. For **all 162** the two full 32-bit tables are equal. This gives pointwise replacement for the actual outside signals of the original circuit. Setting q to true removes the first gate and allows its consumers to simplify. The output remains a nonconstant function, so propagation yields a smaller circuit without requiring a constant gate. This proves the seven-gate bound. Lean checks the finite classification by kernel reduction. [Lean enumeration and sharp construction](../lean/PEqualNP/Outside/PetersenNonedgeOr.lean)

## A construction attaining seven

Supply K, A, B and T = A OR B from outside. The seven endpoint-dependent gates, in order, compute

    q = u OR v
    r = u OR B
    s = v OR A
    d = r AND s
    e = q AND T
    h = e AND d
    output = K OR h

When exactly u is active the result is K OR A, when exactly v is active it is K OR B, when both are active it is K OR T, and when neither is active it is K. If only vertex 1 is active, setting q to true changes the output from zero to one. The first OR is indispensable in the pointwise sense used above. Lean verifies both claims for the posted Petersen graph.

## All possibilities with seven counted gates

With precisely seven counted gates and an OR that cannot be replaced by true, the cut receives three or four distinct outside signals. For fixed values of these signals, record the four-bit output row on u,v. The five target rows are 0, 10, 12, 14, 15. Mark other rows as forbidden since they cannot occur on the graph. This gives a small table specifying how the exterior circuit must encode its inputs.

The [complete enumeration](check-petersen-seven-gates.py) reduces these tables to 34 classes. With four outside signals the six gates after q form a read-once binary tree on seven sources. With three outside signals, there are six sources. Either the suffix has five binary gates and one NOT in a read-once tree, or all six gates are binary and exactly one signal is used twice. This follows by counting operand slots after assigning one use to each non-output signal. In the latter case the subcircuit of the repeated signal is a read-once tree on some subset of the leaves. After cutting it out, the outside tree contains two copies of its value and every remaining source once. This also covers a raw source being used twice.

| Suffix | Distinct eligible tables in the given coordinates | Classes |
| --- | ---: | ---: |
| Three outside signals, one NOT | 36 | 2 |
| Three outside signals, one repeated signal | 102 | 10 |
| Four outside signals, read-once | 864 | 22 |

The enumeration requires all five rows to occur, and requires at least one setting with a target row where replacing q by true changes an answer. The program prints every representative. The two three-signal lists are disjoint after reduction. Equivalence permutes the outside signals, optionally complements their coordinates, and exchanges u and v. A search using one representative must allow both phases of the outside outputs or account for the cost of producing their complements. These tables constrain the subcase with seven counted gates; a bound on the number of exterior gates still has to charge for the signals supplying each table.

### The sole NOT disappears from the minimum-circuit case

In a minimum circuit, replacing q by **either** constant must change an answer. This rules out both classes in the one-NOT row. Thus only **32 classes** remain for a minimum circuit with seven counted gates, and all seven gates are binary ANDs or ORs. NOT gates may still occur in the outside computation. The enumeration checks both constant replacements independently. There is also a direct proof.

More generally, suppose the suffix is a formula in which each of u,v,q occurs only once. Move negations to the leaves by De Morgan's laws. Both endpoint leaves have positive sign: with v fixed true, q is fixed true, and the required projection u increases strictly with u. The symmetric test applies to v. If the q leaf has negative sign, write w = NOT q and regard the formula H(u,v,w) as increasing in all three leaves after fixing the outside inputs.

If replacing q by true ever changes an answer, the change must occur at u = v = 0, the only setting with q false. At those fixed outside inputs, H(0,0,1) = 1 and H(0,0,0) = 0. The original target is monotone in the endpoints and true at (0,0), so it is also true at (1,0) and (0,1). Thus H(1,0,0) = H(0,1,0) = 1. Monotonicity now forces H to equal the three-way OR for this outside setting. Consequently the least common ancestor of every pair of these three leaves in the formula must be an OR: pinning the third leaf to zero still gives the OR of the pair, and a binary least common ancestor has its fixed operation when both children remain essential.

For *any* outside setting, constant propagation in this same tree can therefore leave only a constant or a disjunction of a subset of u,v,w. Each remaining branching gate is the least common ancestor of two surviving leaves. If w survives, the original target is true at (0,0) and hence identically true for these outside inputs. Replacing q by false makes w true and preserves that answer. If w does not survive, the replacement has no effect. Therefore a negative q leaf always admits a constant replacement.

In the seven-gate case with one NOT, the suffix is a read-once tree. Its sole NOT must lie on a path from at least one of u,v,q because only endpoint-dependent gates were counted. It cannot negate either endpoint leaf. It must therefore negate q, which the preceding argument excludes.

### Shorter replacement formulas leave eleven tables

For each remaining table, search for a formula on u,v and the same outside signals that computes its specified answers directly. A binary formula with at most seven leaf occurrences uses at most six gates overall. It can replace all seven endpoint-dependent gates, leaving the outside wires and their phases unchanged. An unspecified row is unreachable in a circuit for the graph, so a replacement may take either value at its four entries.

Enumerating formulas that use every available source at least once and repeat raw leaves up to the seven-leaf limit is already enough to eliminate 84 of the 102 three-signal tables and 528 of the 864 four-signal tables. The remaining 18 and 336 tables have respectively **two and nine representatives under ordinary permutations** of outside signals and exchange of endpoints. No free complements are needed for this reduction.

For each of these eleven representatives, exact synthesis rules out **every** circuit of at most six gates that computes all its specified rows on the same source signals, including circuits with NOT, arbitrary sharing or unused sources. The SAT query fixes the required output at every legal row, leaves other rows free, allows repeated gate operands, and pads a smaller solution by copying its output. The original seven-gate topology attains the table on those rows. Thus the eleven representatives have exact local cost seven. A particular exterior circuit may reach only part of the legal table; its cost and reachable contexts still matter for the full Petersen question. The [enumerator and exact checks](check-petersen-seven-gates.py) print all eleven representatives and verify the lower bounds when passed `--solver` with a CaDiCaL executable.

The two three-signal cases have a common explicit form. Call the outside wires a,b,c, and write U = K OR A and V = K OR B for the graph's outputs when just u or just v is on. Up to exchanging the endpoints and naming the three wires, both cases require

    U = b OR c,     V = a OR c.

The first case requires K = b AND c; the second requires K = b AND a. Conversely these identities suffice. Put t = c or t = a respectively. The seven gates compute q, then

    (b AND (u OR t)) OR ((v AND a) OR (q AND c)).

Expanding gives K OR (u AND U) OR (v AND V), the required function. Thus the entire three-signal subcase reduces to finding a circuit of at most twelve gates for one of two precisely specified factorizations on the eight outside inputs.

Four of the eleven representatives require a nonmonotone outside signal, even with unlimited outside gates. These are the second three-signal table and the second, fourth and sixth four-signal tables in the printed order. For the other seven, all outside signals can be monotone. To check this, assign a codeword to each of the 256 outside assignments, constrain its row to the required graph cofactor, and require each monotone coordinate to increase weakly on each cover relation of the eight-dimensional cube. The checker validates every satisfying assignment directly. For each of the four exceptions, relaxing monotonicity on one coordinate suffices. For the second three-signal table there is also a direct obstruction: vertex 4 alone forces b true and vertex 7 alone forces a true. Their union is independent. Monotonicity of both signals would force a AND b true there, contrary to K = 0.

## Charging for the outside signals

Any circuit computing the four displayed outside signals simultaneously needs at least **thirteen outside gates**, allowing arbitrary AND, OR and NOT gates and unrestricted sharing. In particular these seven endpoint-dependent gates with those four supplied wires cannot give a nineteen-gate circuit.

Set the common neighbor x₁ to true. Each of A, B and T becomes constant true. They are three distinct functions and none is a raw input, so their three distinct gates can all be deleted. Some further gate outside these three must read x₁ directly. To see this, turn on just vertices 3, 5 and 6 among the remaining inputs. Then A,B,T are already true regardless of x₁, while K changes exactly with x₁ because the only possible edge is 1–6. Without a further direct reader the two evaluations would agree on every signal other than x₁. Pinning x₁ to true simplifies that additional reader as well.

The remaining K equals x₆ OR the edge function of the six-cycle in order 3,4,9,7,5,8. Pinning x₆ to false saves at least one more gate, since it is essential and the residual function is nonconstant. The six-cycle requires eight unrestricted gates. Seven are excluded by exact synthesis on all 64 inputs, and three two-edge stars plus two output ORs give eight. Adding the five eliminated gates gives the stated thirteen. [Six-cycle check](check-petersen-or-outside.py)

There is a stronger charge if the outside circuit also computes the two pair ORs R = x₄ OR x₅ and S = x₃ OR x₇, as in A = x₁ OR R and B = x₁ OR S. These are two antipodal pairs of the residual six-cycle. Keeping them as designated outputs through both restrictions preserves their values, even if simplification redirects their wires. Computing the six-cycle and both pair ORs simultaneously needs exactly ten unrestricted gates. The exact nine-gate synthesis query was UNSAT. Three stars, two output ORs and the two pair ORs attain ten. Thus each retained pair OR costs one more gate: a saving with just one would also save a gate for both by appending the other. With h of these pair ORs present, the outside lower bound is 13+h and the displayed construction costs at least 20+h, for h = 0,1,2.

The [unrestricted search](search-petersen-first-or.py) fixes only the first OR and allows AND, OR or NOT at every subsequent gate. It starts with 40 boundary assignments from the two OR slices and tests every candidate against all 1,024 inputs, adding counterexamples when needed. A ten-minute run rejected a candidate from the first 40 inputs, increased the test set to 52, and timed out without a verdict. A known twenty-gate construction with this first OR passed all 1,024 inputs and satisfied the SAT encoding. The nineteen-gate assignment remains open.
