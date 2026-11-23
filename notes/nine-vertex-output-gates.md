# Five gates with at most one internal gate do not suffice for L-meta-908

The graph in L-meta-908 has 16 maximal independent sets. Adding one missing vertex in every possible way gives 96 additions and 67 distinct positive inputs. A circuit must be false on the 16 sets and true on all 67 positive inputs.

Every raw vertex belongs to a maximal independent set, so the final OR cannot read a raw variable. A gate whose value enters the final OR can be removed from the inputs of all later gates. On any input where that gate is true the output is already true, and where it is false removing the wire has no effect. This holds for all output gates together by induction in gate order whenever every original output gate is false. In the other direction, if any original output gate is true, the earliest such gate retains its value.

With five parallel gates each output term is a conjunction of two raw ORs. For the term to be false on every negative input, the sets of vertices on the two sides must be disjoint and every cross-pair must be an edge. Indeed, an independent pair extends to a maximal independent set. The graph has no four-cycle, so any nonempty such term is contained in a star. Trying all subsets of the nine possible star centers gives a minimum of six centers even for the partial function.

With one internal gate, call its signal H. Each of the four output gates has two ORs over ten signals, the nine raw variables and H. Two signals are compatible across the sides precisely when they never occur together on a negative input. H is compatible with itself exactly when it is false on every negative input. For any left side, take all its common compatible neighbors as the right side, then all common neighbors of that right side as the left. This produces a safe gate containing the original gate. Trying every left side therefore tests a set of gates sufficient to cover all possibilities.

Enumerating all unordered pairs of raw ORs for H gives 139 distinct compatibility relations. For a fixed relation, every safe output term is monotone in H. An H whose positive truth table is contained in another table for that same relation can be discarded. This leaves 532 maximal positive tables across the relations. For each table the program branches on an uncovered positive input and tries every maximal output gate that covers it. None of the 532 cases covers all positives with four gates.

Thus any five-gate solution must use at least two internal gates and have at most three gates feeding the final OR after normalization.

Run `python3.11 notes/check-nine-vertex-output-gates.py` from the repository root to reproduce the enumeration.

## The unrestricted five-gate lower bound by SAT

The companion encoder checks the five possible counts of internal gates. CaDiCaL returned UNSAT for all five formulas with its internal proof checking enabled. Six stars centered at vertices 0, 2, 3, 4, 6 and 7 realize the partial function. Lean verified that this circuit computes the full edge function and satisfies the posted partial specification. Together these results give the exact value six. An official Lean proof of the lower bound remains to be supplied. [Six-star witness](NineVertexSixStars.lean)

To see why the cases cover every candidate, take any circuit with at most five gates. Remove reads from output gates as above, and put the remaining internal gates first in topological order. Prune unused gates and gates with an empty side, which compute zero. For an internal gate with overlapping signal sets on its two sides, write the common OR as R and the two exclusive ORs as A and B. Its value is R OR (A AND B). Pass the signals of R directly to every later side that used this gate, leaving A AND B at the gate. Process in topological order; this also handles overlaps introduced at later gates. Delete any newly unused or constant-zero gates. Since there are positive points and no raw output variable, at least one terminal gate survives. Duplicate a terminal as needed to obtain exactly five gates. The gate sides may be sorted lexicographically, as may the terminal gates, since all terminal gates now depend only on earlier internal gates and raw inputs.

For each internal count, the CNF chooses the wires of both sides, with the above ordering and disjointness on internal sides. Every internal output has a later reader. On each of the 83 distinct defined inputs, exact Boolean equivalences evaluate every chosen side and gate. On a negative input every terminal must be false. On a positive input at least one terminal must be true.

| Internal gates | Terminal gates | CNF variables | Clauses | Result |
| ---: | ---: | ---: | ---: | --- |
| 0 | 5 | 1,461 | 5,752 | UNSAT |
| 1 | 4 | 2,124 | 8,377 | UNSAT |
| 2 | 3 | 2,614 | 10,324 | UNSAT |
| 3 | 2 | 2,931 | 11,593 | UNSAT |
| 4 | 1 | 3,075 | 12,184 | UNSAT |

Run `python3.11 notes/check-nine-vertex-internal-gates.py /path/to/cadical 0 1 2 3 4 --seconds 180`. The program prints the SHA-256 of each deterministic DIMACS formula. Before each case it checks a fixed six-star realization with the same number of internal gates, each connected to a terminal. All five positive controls returned SAT. Each control includes extra gates when its internal count is positive.

## Independent verification by reachable sides

Choose a side at each AND gate and replace that gate by its chosen side. The output becomes an OR over the bare variables of the sides reachable from the output. This OR dominates the original circuit. At a fixed negative input I, choose a false side at every false gate. The resulting OR is false on I and, by domination, true at every one-vertex extension of I. Its variables are therefore exactly the complement of I. The 16 different maximal independent sets require 16 distinct reachable-side sets.

The direct search first takes a candidate with as few internal gates as possible. At a terminal gate, any parent shared by its two sides can be promoted to the final OR by distributivity. Clear its outgoing wires as above. This reduces the internal count. A common bare input at a terminal is impossible since a maximal independent set contains that vertex. A never-reached internal gate can be dropped. An always-reached internal gate can be promoted as well. To see this, cut its inputs and set its signal to true. Every choice of sides above it still reaches that true signal. An output of false would permit a choice of false sides with a false linearized OR, a contradiction. Thus the original output is true whenever this gate is true. Promotion preserves the function.

For each remaining topology, encode a reachable-side set by ten bits. A vertex can belong to any subset of the ten bare sides. Its candidate profile is the collection of corners whose reachable sides avoid that subset. Assign a profile to each of the nine vertices. After any partial assignment, group the 16 target rows and the available corners by their assigned membership bits. A group needs at least as many available corners as target rows. The search rejects a profile as soon as it violates that count. It prunes symmetric choices only under permutations which preserve the actual reachable-side family and fix all previously assigned profiles.

| Internal gates | Distinct families searched | Search states | Matching families |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 14 | 0 |
| 1 | 4 | 1,074 | 0 |
| 2 | 53 | 23,874 | 0 |
| 3 | 503 | 44,930 | 0 |
| 4 | 102 | 596 | 0 |

Run `python3.11 notes/check-nine-vertex-corners.py`. This verification uses no SAT solver.

## Checking all circuits backwards

Starting from the singleton empty row, process gates from the final output towards the inputs. At each gate, select any subset of the already processed sides that read it. A row splits into its two choices precisely when it hits one of these sides or the gate is itself an output. Otherwise it stays unchanged. Unused gates, shared parents, and reads of output gates are all allowed. Families too small to reach 16 rows even by doubling at every subsequent stage are discarded. Renaming gate and side labels preserves the test.

Lean verified that every correct circuit of size at most five yields an accepting family in this backwards recursion. The independent checker found 2, 3, 8, 33 and 397 families after the five successive stages. No final family realizes the required rows. The numerical exclusion in Lean remains open. [Formal reduction](NineVertexCornerReduction.lean) · [Reproduce the search](check-nine-vertex-backwards.py)

## Formal lower bound of five

Four gates could produce at most 16 reachable-side sets. To realize the 16 distinct negative rows, every one of the four stages would have to double the number of sets. The result is the full set of 16 side choices. Vertex 1 occurs in exactly five negative rows. No choice of its bare sides places it in exactly five of those 16 rows. Lean checks these counts and proves that every circuit meeting the desk conditions has at least five gates. The six-gate example leaves only the five-gate case for the full formal lower bound.
