# The first AND of two nonadjacent Petersen vertices

Let E be the Petersen graph edge function, and write q = x₀ AND x₂. Vertices 0 and 2 are nonadjacent in the desk's numbering. The graph's automorphisms carry any ordered nonadjacent pair to this case. [Checked symmetry](../lean/PEqualNP/Outside/L_meta_651.lean)

## When the first gate can be deleted

Write H(x,w) for the circuit after its first gate, with that gate's wire supplied independently as w. Assume the circuit computes E when w = q. The following conditions suffice to delete the first gate.

- With w fixed to false, turning on either endpoint cannot change the output from true to false.
- When both endpoints are on, changing w from false to true cannot change the output from true to false.

When q is false, H(x,false) already equals E(x). When q is true and E(x) is true, some active edge survives turning off at least one endpoint, since the pair itself is a nonedge. At that modified input H returns true with w false. The first condition carries that answer back to x. When q is true and E(x) is false, the second condition forces H(x,false) to be false. Thus replacing q by false preserves the output. Both conditions refer only to the indicated wires. Other inputs may enter NOT gates.

Lean checks this argument and constructs a circuit with exactly the remaining number of gates. It redirects reads of the deleted wire to a permanently out-of-range wire, which the evaluator reads as false. Any new false positive must contain both endpoints and be independent. There are exactly five such supports: {0,2}, {0,2,6}, {0,2,8}, {0,2,9}, and {0,2,8,9}. [Lean proofs](../lean/PEqualNP/Outside/PetersenNonedge.lean)

## A guarded construction needs exactly 23 gates

Consider circuits of the following form, counting all AND, OR, and NOT gates and using binary fan-in for AND and OR.

    q = x₀ AND x₂
    output = A OR ((NOT q) AND B)

A and B are ORs of products, where a product is one AND of two ORs of raw vertex inputs. A single input is also an allowed factor. The A and B circuits may share input OR gates, products and upper OR gates. The displayed q, NOT and guard AND are distinct gates, with q used only in the guard through its NOT. This class has exact minimum size 23.

Each product corresponds to a rectangle L × R of pairs of vertices. Its two sides must be disjoint, since on every singleton input the guard is on and E is false. Testing two-vertex inputs shows that every A rectangle contains only genuine edges, and that a B rectangle can contain just one artificial pair, {0,2}. Every genuine edge must occur in A or B.

Let u = 0, v = 2. If b is adjacent to u and not to v, the triple {u,v,b} has exactly one edge and the guard is off. Therefore A must contain ub. The corresponding statement holds for neighbors exclusive to v. The pair has just one common neighbor.

Consider a B rectangle containing the artificial pair, oriented with u on the left and v on the right. If one side is a singleton, all its genuine edges except possibly the edge to the common neighbor already occur in A. If both sides have another vertex, each side has exactly two vertices. Indeed, two further vertices on either side, together with two vertices on the other, would form a genuine four-cycle. Write the rectangle as {u,a} × {v,b}. The Petersen graph is triangle-free, so a cannot be adjacent to u and b cannot be adjacent to v. The edges av and ub already occur in A. Only ab may still be needed. For this labelled pair, direct enumeration gives 384 subgraphs A agreeing with E whenever both endpoints are on, and 17 rectangles containing the artificial pair. The maximum number of genuine rectangle edges outside A across all 6,528 combinations is one.

Replace each rectangle containing the artificial pair by the single raw AND for its remaining edge, or by false if none remains. This costs at most its original product gate, and preserves shared OR wires used elsewhere. Such a product cannot feed A. Now the union of A and the modified B contains exactly the genuine edges. Removing q, its NOT and the guard AND leaves a circuit with at most the original size minus three. Every path in this circuit uses at most one AND.

Here is the lower bound on that remaining circuit. Let k be the number of products reaching the output after deleting empty products and simplifying constants. Each rectangle is a star because the graph has no four-cycle. Choose a center for each product, either endpoint for a single edge. Their centers cover all edges, so k is at least six. At least k − 1 OR gates connect the k products to the output.

Assign each edge to one covering star. For a center c let e_c be the number of assigned edges and k_c the number of its stars. Their opposite-side inputs collectively include at least e_c distinct raw neighbor variables. Building k_c such signals takes at least e_c − k_c input OR gates: starting from the k_c outputs and following the circuit backwards, expanding a binary gate increases the number of distinct frontier wires by at most one. Contract gates whose support is a singleton before counting. No counted OR gate can be shared by different centers, because two common neighbors would give a four-cycle. Summing gives at least 15 − k input OR gates. Along with the k products and k − 1 output gates, the total is at least 14 + k ≥ 20. The six-center minimum cover is checked in the [Petersen lemmas](../lean/PEqualNP/Outside/L_meta_651.lean). The guarded circuit therefore needs at least 23.

For equality use the six stars below. Give A the stars at centers 0, 2 and 6 and give B the stars at centers 3, 5 and 9.

| Center | Leaves |
| --- | --- |
| 0 | 1, 4, 5 |
| 2 | 1, 3, 7 |
| 6 | 1, 9, 8 |
| 3 | 4, 8 |
| 5 | 7, 8 |
| 9 | 4, 7 |

When the guard is off, A already detects every possible active edge. Its first two stars cover the neighbors of the fixed endpoints. The only edges among the other vertices are 6–8 and 6–9, both in its third star. The guard is redundant in this upper-bound example, as the stated syntax permits. The unrestricted 19-gate problem remains open. [Checked 23-gate circuit](../lean/PEqualNP/Outside/PetersenNonedge.lean)

## The wider single-NOT search has 39 boundary inputs

With q first and NOT q second, allow the remaining 17 gates in a 19-gate candidate to be arbitrary ANDs and ORs with sharing. Split the inputs according to q. Within a slice, both special wires are constant and the remaining circuit is monotone in the original inputs. Its values on the minimal true and maximal false assignments determine whether it computes E throughout that slice.

| Value of q | Minimal true | Maximal false |
| --- | ---: | ---: |
| False | 15 | 15 |
| True | 7 | 2 |

These 39 inputs are also necessary for any test set that must distinguish E from every monotone remainder with unrestricted size. Each minimal true input can individually be changed to false, and each maximal false input can individually be changed to true, without violating monotonicity on its slice. The two slices are incomparable in the extended input coordinates (x,q,NOT q). Any such modified function extends to a monotone Boolean function on the full extended cube by taking the upward closure of its true inputs.

The [bounded synthesis search](search-petersen-nonedge.py) imposes all 39 tests and checks any returned circuit on all 1,024 original inputs. It permits equal operands to pad shorter circuits. CaDiCaL returned UNKNOWN after 120 seconds on the 17-gate remainder (3,170 variables and 74,301 clauses). The wider family remains unresolved.
