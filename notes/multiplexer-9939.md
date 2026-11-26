# The eight-way multiplexer at 23 gates

[L-meta-9939](https://pequalnp.com/lemma#L-meta-9939) asks whether the multiplexer on three address bits and eight data bits has an AND/OR/NOT circuit with at most 23 gates. The usual circuit uses 24. The [verifier](multiplexer-9939.cjs) evaluated it on all 2,048 inputs, using the first address bit as the least significant bit exactly as in the posted expression. The unrestricted 23-gate question remains open.

**A data tree using at most six gates to process the address requires at least 24 gates.** In this result, every data bit occurs once, every gate depending on data has one consumer or is the output, and these gates use AND or OR. Their siblings can be other data subtrees or any address signal. The separate address circuit can use AND, OR and NOT with fan-in at most two, sharing any of its signals without limit. The standard 24-gate control belongs to this class.

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

For example, the 24-gate control pays for three address negations and then uses the usual three-gate selector at each of seven internal nodes. Run `node notes/multiplexer-9939.cjs` from the proof fork for the control and the restricted lower bound. Sharing a data-dependent gate, applying NOT to one, or using a larger address circuit falls outside this calculation.
