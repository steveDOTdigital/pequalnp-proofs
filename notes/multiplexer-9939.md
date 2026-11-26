# The eight-way multiplexer at 23 gates

[L-meta-9939](https://pequalnp.com/lemma#L-meta-9939) asks whether the multiplexer on three address bits and eight data bits has an AND/OR/NOT circuit with at most 23 gates. The usual circuit uses 24. The [verifier](multiplexer-9939.cjs) evaluated it on all 2,048 inputs, using the first address bit as the least significant bit exactly as in the posted expression. The unrestricted 23-gate question remains open.

**The exact minimum is 24 gates if each data bit occurs once in the circuit unfolded from its output.** The address subcircuit may use arbitrary AND, OR and NOT gates with unrestricted sharing. NOT may also be applied anywhere on a data path. Thus any 23-gate circuit for the posted function must reuse a data input or share an intermediate signal that depends on data. The 24-gate control attains this restricted minimum.

## Counting the address circuits

Represent each function of the address by its eight-bit truth table. Starting with the three address variables, add one new table at a time by AND or OR of two available tables, or NOT of one table. The enumeration deduplicates equal sets of available tables. Constants and copies can be removed by propagation or folding. Gates unused by the data tree may likewise be omitted.

For each pair of different addresses i and j, some available signal must be true at i and false at j. Otherwise when only data bit i is true, monotonicity in the available address signals would force the circuit's output at i to be at most its output at j. Of 202,322 different libraries generated through six address gates, 5,340 satisfy this condition. Address-coordinate permutations preserve the cost. Complementing all address bits and all signals simultaneously also preserves it: dualize AND and OR throughout, complement the data assignments and relabel which data bit is selected. The three source predicates map to source predicates.

## Computing the exact tree cost

Apart from gates with an address operand, a tree joining eight distinct data leaves has exactly seven binary gates. To find the least possible number of gates with an address operand, solve each subtree for three disjoint collections of addresses. On the first collection U, the subtree must return the data bit named by the address; these are precisely its leaves. The other two collections specify rows where it must be constantly one or constantly zero. All remaining rows are unconstrained.

An AND with an address predicate can discharge required zeros where that predicate is false. It must stay true at every required projection and one. An OR can discharge ones by the dual rule. For an OR joining two subtrees, split U into their two nonempty leaf sets. Each child must be zero on all rows where its sibling supplies the requested bit. On a required zero both children must be zero. On a required one at least one must be constantly one, since the children's data sets are disjoint and assignments falsifying both could otherwise be combined. Try every allocation of these ones. The AND recurrence interchanges zero and one. A single data leaf needs no further gate when it has no constant requirements. These operations exhaust the possible roots, and every transition corresponds to a circuit.

| Useful address gates | Libraries passing the address test | Minimum gates with an address operand | Minimum total with that many address gates |
| ---: | ---: | ---: | ---: |
| 0–2 | 0 | | |
| 3 | 1 | 14 | 24 |
| 4 | 24 | 14 | 25 |
| 5 | 375 | 12 | 24 |
| 6 | 4,940 | 12 | 25 |

For example, the 24-gate control pays for three address negations and then uses the usual three-gate selector at each of seven internal nodes. Run `node notes/multiplexer-9939.cjs` from the proof fork for this count and the 2,048-row control.

## All read-once data paths

The [full verifier](multiplexer-tree-9939.cjs) extends the lower bound to any number of address gates and allows NOT anywhere in the data tree. Remove unused gates and constant or repeated address predicates before counting. Write h for the number of address gates that remain. There are always seven joins of two data subtrees. In addition, each of the eight leaves needs at least one AND or OR with an address operand before its first join with a different data leaf. At an address selecting a leaf from that sibling, the first leaf's operand must take the neutral value of the join. A bare bit or a sequence of NOTs cannot be constant on that row. The eight paths before their first joins are disjoint. Consequently h at least nine already costs at least 24 gates.

With no data-dependent NOT and seven address gates, a 23-gate attempt can use at most nine address operands on the data tree. None of the 59,689 address libraries passing the antichain test works. There are 5,286 representatives under the symmetries above. With eight address gates, only eight such operands are available, and none of the 58,828 address-library representatives works. The enumeration reached every useful library of up to seven gates before extending to eight. When two rows are still comparable after seven gates, adding one AND or OR of existing signals cannot make them incomparable. In that case only a NOT need be tried as the last address gate.

To check many libraries without repeating the same tree search, the verifier compiles the bounded recurrence above into tests for the existence of an address predicate with prescribed zeros and ones. For an AND operand, enumerate the subset of required zeros left for the child; the predicate must pass those zeros, all projections and all required ones, and discharge the other zeros. The OR rule is dual. At a join try every split of the remaining gate budget. Batching these Boolean tests in a machine word gives an independent result for each library. Supplying all eight singleton address predicates is a positive control: eight data operands then suffice.

If any NOT acts on data, at least two do. Each data leaf has a unique path to the output, and the parity of the NOTs on that path must be even: at its own address the output is its positive, nonconstant bit. Push all data-path NOTs to the leaves by De Morgan's laws for a lower bound. They cancel on data leaves and can complement address operands. Grant all those address complements for free. The resulting positive-data tree must fit within 14−h address operands after paying for seven joins and at least two original NOTs. This is impossible immediately for h at least seven. For h from zero through six, test **all** address libraries, including those that fail the antichain condition before the free complements. Their respective symmetry-class counts are 1, 2, 10, 54, 324, 2,149 and 15,298. Only three classes survive: one with h=0 and two with h=2.

For those three, the verifier uses the original address library and charges for actual data NOT gates. The subtree state also records whether each selected projection must be the data bit or its complement. The polarity is uniform within a subtree because the path above its root is shared. A root NOT swaps constant zero and one requirements and flips the polarity. Two consecutive NOTs cancel, so the child of a root NOT may be required to have a different root operation. The exact minima for address operands plus data NOTs in these three classes are 22, 18 and 19, respectively. Adding their seven joins and address gates gives 29, 27 and 28 gates. None reaches 23.

Run `node --max-old-space-size=640 notes/multiplexer-tree-9939.cjs` for the full read-once check. The unrestricted posted statement and its negation remain undecided by this calculation.
