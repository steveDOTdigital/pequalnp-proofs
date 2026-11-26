# A ten-gate circuit for the 5 by 5 promise graph

[L-meta-19636](https://pequalnp.com/lemma#L-meta-19636) asks whether nine gates suffice for the graph mask 8130428. The evaluator receives five row indicators followed by five column indicators, exactly one of each set true. In increasing column order the target rows are `00111`, `11011`, `11000`, `00011` and `11100`. We have a circuit with **ten gates**. The completed searches through size eight put the minimum at **nine or ten**. The size-nine search is in progress.

Let A report column 0 or 1, and C report column 3 or 4. Write r0 through r4 for the row indicators. Set U = r4 OR A and V = r0 OR C. The output is

    (U OR V) AND NOT ((r2 OR U) AND (r3 OR V)).

Computing A and C costs two gates, U and V two more, and the displayed expression six more because it reuses U and V. Direct evaluation of the ten single gates reproduced all 25 posted entries. Row 1 and column 2 require no input pin of their own in this construction.

## Lower bound and exact search

The five row signatures are different. At most one row indicator can go unread, since two unread rows would look identical at a fixed column. The three column classes have sizes two, one and two, so at most two column indicators can go unread. At least seven distinct raw signals must therefore feed the output cone. A connected binary cone fed by seven distinct signals needs six binary gates, even with free unary gates.

We searched irredundant AND/OR/NOT circuits directly against all 25 assignments. A bounded synthesis run excluded sizes seven and eight. Six gates with seven raw inputs must be a read-once formula. A separate enumeration excluded formulas through size nine; the support-partitioned replay has also excluded each of the five feasible support representatives at size six. A size-nine circuit cannot be ruled out by a timeout or an unfinished case.

The [replay](promise-graph-19636.py) includes the ten-gate witness and a SAT formulation. Each gate chooses one operation and two preceding wires, with repeated selectors denoting the single effective input of NOT. Its value on each promise input is constrained by the gate truth table. AND and OR need two distinct operands. Unknown wires evaluate to false in the project evaluator. Missing inputs, invalid references, unary copies, repeated binary operands and constant wires can all be folded from a least circuit for this nonconstant target: constants propagate, neutral arguments disappear, and downstream uses and the output selector can be redirected. An irredundant circuit has every internal gate used and its output last under a topological ordering. A lexicographically least order by smaller input index cannot contain two adjacent independent gates with that index descending, since swapping them lowers the first changed index.

The replay groups possible raw-input supports under exchanges of the identical columns in each pair and the simultaneous exchanges of the outer column classes and corresponding rows. It checks each permutation against the actual target. A binary cone with s gates uses at most s+1 distinct raw inputs. These conditions determine the support representatives at each size. Each satisfying circuit is decoded and independently evaluated on the original truth table. Run `python promise-graph-19636.py` with the Python-SAT package installed, or select a single size and support with `--size` and `--case`.

## The remaining nine-gate cases

The public checker has separately established [a ten-gate upper bound with NOT](https://pequalnp.com/lemma#L-meta-19446) and [the impossibility of even ten gates without NOT](https://pequalnp.com/lemma#L-meta-10195) for the identical mask. We developed and tested the ten-gate construction above before consulting those verdicts.

An independent formula search rules out every nine-gate tree, even allowing the same raw signal at several leaves. Its smaller binary subtree has at most four gates. The replay enumerates every distinct small truth table by increasing formula cost. At an OR root the smaller operand must reject every required zero; the other operand must meet the remaining required ones and all required zeros. The AND rule is dual, and NOT exchanges the required ones and zeros. A branch doing no work for the partial requirement can be removed. This recursion accounts for highly unbalanced trees and can be repeated with `--formulas`.

Let r be the number of distinct raw inputs read by a hypothetical least nine-gate circuit. A live connected circuit with b binary gates and k unary NOTs has 2b+k input edges and r+b+k vertices. If b=r−1 the underlying graph is a tree, so the circuit is a formula. Thus b≥r. Together with r≥7, b+k=9 and the checked monotone exclusion, the only possibilities are r=7 with one or two NOTs, or r=8 with one NOT. These leave 19 combinations of NOT count and inequivalent raw-input support. The unrestricted search and the separate search of these 19 cases are in progress. The latter can be replayed with `--nine-cases --backend glucose4`.
