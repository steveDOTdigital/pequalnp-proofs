# Seventeen signed binary gates for the raw Petersen edge function

For L-meta-1888, any circuit computing the ten-input Petersen edge function from raw inputs needs at least **17 binary gates**, even with free negation on every input, intermediate wire and output. Giving the circuit the extra input $x_0 \lor x_2$ therefore still requires **16 binary gates**. A circuit of at most 18 ordinary gates with the desk's extra input could use at most two NOT gates. A 19-gate circuit with the extra input is known. The cases with zero, one or two NOT gates remain open in this calculation.

The [independent finite certificate](petersen-free-or-certificate.py) exhausts the small remaining search on all 1,024 truth rows. The [Lean companion](PetersenFreeOr.lean) checks the transfer from a raw signed lower bound to the actual desk evaluator, including arbitrary wiring, repeated pins, default reads and gates with fewer than two operands. The raw signed exclusion itself combines the following argument and Python calculation.

## Restricting the direct readers

A signed binary gate takes the AND of two earlier wires, independently choosing the sign of each. Either sign of the result can be used. Work in the live output cone of a minimum circuit. Constants, equal or complementary operands, and duplicate signals up to sign can be folded. The [deletion bounds](petersen-raw-bound.md) give 14 gates after pinning one vertex to zero, 13 after pinning two adjacent vertices to zero and 12 after pinning two nonadjacent vertices to zero. The automorphism check covers both orbits of pairs. In the cited nine-vertex bounds, deleting a degree-two vertex corresponds to the adjacent pair in the full Petersen graph.

Each raw variable remains essential under either value of every other raw variable. The certificate verifies this directly. Thus a gate reading two raw variables requires each variable to have another reader. Otherwise setting its companion to the gate's controlling value would make the function independent of that variable. Losing at least two readers on the zero pin implies a raw lower bound of 16, so only a minimum of exactly 16 needs testing.

Every vertex has at most two direct readers since pinning it to zero eliminates them all. Choose a minimum circuit minimizing the sum of operand indices over its listings. A gate reading both a predecessor and one of that predecessor's operands can be replaced by a constant, a literal or one signed binary gate on the original operands. Fix the common operand to the value making the predecessor constant. The composition then becomes constant and on the other slice it is unary in the other operand. The replacement reduces the number of gates or the operand-index sum. This is the [direct-reader normalization](petersen-signed-deletion.md).

For a twice-read variable neither reader can be forced constant at zero. Such a forced reader needs a consumer because the zero cofactor is nonconstant. By normalization that consumer differs from both direct readers. Three gates would disappear, leaving at most 13. Hence all raw-pair gates are ORs up to output polarity, and every read of a twice-read raw variable must have controlling value one.

No raw-pair OR can connect adjacent vertices. If it connected $p,q$, each has a second reader and these two readers differ, since another raw OR of the same pair would duplicate the first. A consumer of the first OR reads neither raw input by normalization. Pinning both inputs removes those four distinct gates, leaving at most 12 instead of the required 13. Likewise, if two adjacent vertices each had two readers, their four readers would be distinct because they cannot share a raw-pair gate. Pinning both would again remove four. The set of twice-read vertices is therefore independent. The first OR can be taken as $x_0 \lor x_2$ by nonedge transitivity. This is a choice of coordinates for the **raw** lower bound, independent of the extra pin in the assignment.

## Checking the remaining prefixes

The graph has 120 automorphisms and the setwise stabilizer of the first pair has order four. There are five independent supersets of that pair and four orbits. Each raw input must be read once or twice according to the chosen set. The program tries all pairs of distinct earlier operands and all four choices of signs in arbitrary topological order. Truth tables are identified with their complements by choosing the representative false at the empty input.

Three bounds prune a prefix.

* If two rows differing only in one variable disagree on the target and agree on every prefix gate, a further direct read of that variable is necessary.
* Every prefix gate without a consumer needs a path to the output. If there are $u$ such gates and $r$ raw input positions still owed to the exact reader counts, at least $r+u-1$ suffix gates are necessary. The suffix has two input positions per gate, and each suffix gate other than a possible output also needs a consumer.
* On a zero restriction, each constant prefix gate and each prefix gate equal up to sign to an earlier restricted signal can be eliminated in order. Future direct readers of pinned raw inputs also disappear. Two pinned vertices can share at most one such future reader, their OR, and only when that pair is eligible and its OR has not appeared already. The total removals may not exceed the budget minus the established bound for that restriction.

| Twice-read vertex mask | Orbit size | Prefixes including empty | Largest depth |
| --- | ---: | ---: | ---: |
| 5 | 1 | 2 | 1 |
| 69 | 1 | 18 | 4 |
| 261 | 2 | 6 | 3 |
| 773 | 1 | 437 | 7 |

No prefix reaches the target. A positive control checks the known six-star construction with 19 gates and the free OR, or 20 when its OR is paid, on all input rows. Run `python3 -B notes/petersen-free-or-certificate.py` from the proof repository. The Lean file imports the earlier [signed circuit compiler](PetersenSignedSlice.lean).

## Formula consequence

A signed formula for the raw graph has at least **20 leaves**. Suppose it had at most 19. Every one-vertex deletion needs [17 signed formula leaves](petersen-formula-size.md). Fixing any variable to zero eliminates all its occurrences, so every variable occurs at most twice. The [polarity elimination lemma](cubic-formula-leaves.md) turns a signed read-twice formula for an increasing function into a monotone formula without adding leaves. The monotone minimum for this cubic graph of girth five is $15+6=21$ leaves, a contradiction. Thus a raw formula containing a paid NOT costs at least 19 binary gates plus that NOT. A monotone formula costs at least 20 binary gates, and the star formula attains 20. The ordinary raw AND/OR/NOT **formula** size is therefore exactly 20. The upper bound for raw formulas is 21 leaves when negations are free.
