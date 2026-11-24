# A fifteen-gate lower bound for the nine-input Petersen edge function

For L-meta-3283, any fan-in-two AND, OR, NOT circuit computing the displayed edge function has at least fifteen gates. The result holds without prescribing its first gate. This is a computer-assisted proof. Lean checks the circuit normalization and parallel evaluation lemmas. The exhaustive lower bounds below use a separate C++ checker. The ordinary fifteen-gate statement also follows from the project's previously merged [L-meta-2012](https://github.com/brilliant-hq/pequalnp-proofs/blob/048b39bb2c5b2c21da06d44218d16366086a68d9/lean/PEqualNP/Outside/L_meta_2012.lean). The calculation here independently establishes stronger bounds for signed vertex deletions and a 24-row monotone obstruction.

Let G be the nine-vertex graph in the desk statement. A signed gate computes the AND of two independently complemented earlier signals. Both signs of every signal are available, including at the output. Thus a NOT costs zero in this model. An OR costs one signed gate by De Morgan's law.

## Signed lower bound

Let T be the theta graph on vertices 1,2,3,5,6,7,8. Its three paths between vertices 2 and 8 have lengths 2,3,3. Our [earlier deletion proof](petersen-signed-deletion.md) gives a signed lower bound of ten. The signed prefix search excludes ten in 2,776,621 visited prefixes. A vertex-cover star formula attains eleven.

Deleting any cubic vertex of G gives a graph isomorphic to G minus vertex 0. Deleting its pendant vertex 4 gives T. Setting that essential input to zero removes a direct binary reader. Thus a cubic deletion costs at least twelve signed gates. An explicit monotone star circuit attains twelve. Deleting any degree-two vertex gives a graph isomorphic to G minus vertex 6. Our earlier proof gives twelve for this deletion. Using the stronger eleven-gate theta bound, the signed checker now excludes twelve in 32,772,611 prefixes. Its star formula uses thirteen.

Every first signed gate of a minimum circuit for G reads two different raw variables p and q. Variable p remains essential with q fixed to either value. With q zero select another neighbor of p. With q one, use q itself when they are adjacent. For nonadjacent p and q, p has a neighbor not adjacent to q since the minimum degree is two and G contains no four-cycle. Hence p needs another reader that bypasses the first gate. Fixing p to zero loses at least two binary gates. Every single-vertex deletion costs at least twelve, which proves the signed lower bound of fourteen.

## Circuits with and without a paid NOT

If a desk circuit of size at most fourteen contains a NOT, it has at most thirteen binary gates. Absorbing gate signs and folding constants and unary gates produces a signed circuit with at most thirteen gates, contrary to the preceding bound. The [Lean normalization](PetersenRawNormal.lean) proves a slightly sharper disjunction. A candidate either uses exactly two operands at every gate, all AND/OR, or compiles to fewer signed gates than its original gate count. This covers default reads, unused gates and the allowed nonbinary arities.

For monotone circuits, a minimum candidate of size below fourteen is excluded by the signed bound. At fourteen the zero-cofactor bounds are twelve on cubic vertices and thirteen on degree-two vertices. The first-gate test leaves three orbits, all ORs, represented by (0,1), (0,2) and (0,3). The monotone prefix checker excludes them together in 76,089 prefixes. This completes the fifteen-gate lower bound.

It suffices to test monotone circuits on the twelve edge pairs and twelve maximal independent sets. Each positive assignment contains one of the edge pairs. Every negative assignment is contained in a maximal independent set. The [packed evaluation lemma](PetersenPackedBoundary.lean) checks all these rows in parallel by wordwise AND and OR. The least significant twelve bits correspond to edges. The target word on the 24 rows is 4095.

## Why the exhaustive checks cover minimum circuits

The [driver](petersen-raw-prefix.py) computes every truth row, automorphism and single-pin restriction. The [enumerator](petersen-raw-prefix.cpp) visits distinct earlier operands in a topological order sorted by larger operand then smaller operand. A newly ready gate depends on the newest wire. The lexicographically smallest first pair across all automorphisms and valid schedules represents its orbit. Both orders of signs on the representative are tested when the restriction bounds permit them.

The [first-gate elimination argument](petersen-gate-elimination.py) supplies the four single-pin tests. The signed lower bounds used on small graphs come from the [six- and seven-vertex checks](petersen-signed-deletion.md). The monotone bounds through seven vertices also follow from the [verified edge-plus-cover formula](seven-vertex-cover.md). Pinning a vertex true adds the OR of its neighbors to the remaining induced graph. Setting these distinct extra singleton inputs false one by one costs at least one gate each whenever an edge remains. A disjunction of k inputs alone costs k minus one.

In the signed search a wire is stored with value zero on the empty assignment. A gate that is constant or agrees with an earlier wire up to polarity on a restriction can be deleted on that restriction. These replacements preserve exact values when performed in order. In a minimum signed circuit, among circuits with the smallest sum of operand indices, no gate reads both a predecessor and one of that predecessor's operands. The composition is a constant, a literal or a signed binary gate on the two original operands. Replacing it either saves a gate or lowers that sum.

The monotone search uses domination on each restricted boundary. An earlier wire can replace a gate when it is at least as high on every minimal positive and at most as high on every maximal negative. After earlier replacements the same inequalities persist by monotonicity. Each known cofactor lower bound limits the number of removable gates.

The checker also keeps all pairs of assignments that differ on one raw input, disagree on the target and agree on every computed prefix wire. Such an input requires a further reader, so pinning it removes an additional suffix gate. Each unused prefix gate also needs a path to the output. Combining k separately required sources takes at least k minus one binary gates. An explicit witness is evaluated again on the full truth table. A timeout gives no lower bound.

## Reproduction

From the proof repository root, run the earlier signed deletion checks followed by these commands. The driver builds in a temporary directory. Budgets refer to possible globally minimal circuits, so exclusions are applied in increasing order.

```sh
python3 notes/petersen-raw-prefix.py 235678 7,8 --signed
python3 notes/petersen-raw-prefix.py 1235678 10 --signed
python3 notes/petersen-raw-prefix.py 01234578 12 --signed --seconds 300
python3 notes/petersen-raw-prefix.py 12345678 11,12
python3 notes/petersen-raw-prefix.py 01234578 12
python3 notes/petersen-raw-prefix.py 012345678 13 --signed
python3 notes/petersen-raw-prefix.py 012345678 14
```
