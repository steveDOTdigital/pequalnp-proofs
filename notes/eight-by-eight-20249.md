# A 25-gate circuit for the eight-by-eight graph 4868853174714768465

[L-meta-20249](https://data.pequalnp.com/data/lemma/L-meta-20249.182b5675be9a.json) asks for at most 24 binary AND/OR gates. [EightByEight20249.lean](EightByEight20249.lean) gives 25. Lean 4.36.0 checked all 64 promised assignments, the gate types and the gate count. The theorem uses propositional extensionality. The previously [accepted 27-gate circuit](https://github.com/open-goat/pequalnp-proofs/pull/26906) uses the row-column symmetry also present here.

Number the sixteen raw signals from 0 through 15, with rows first. Encode the union of a set of raw signals by the integer with the corresponding bits set. The circuit ANDs the two unions in each row below, then ORs the six results.

| First union mask | Second union mask |
| ---: | ---: |
| 514 | 3096 |
| 515 | 4224 |
| 16448 | 33028 |
| 10280 | 33812 |
| 32 | 8192 |
| 4225 | 16704 |

Fourteen shared OR gates construct all the unions. Six AND gates form the products and five OR gates combine them. On the promise, each product can cover two disjoint rectangles because two distinct row signals cannot both be true, and likewise for column signals. An independent direct evaluation of the circuit returns the exact 64-bit target mask.

The 25-gate result is a partial bound for the assignment. It gives no lower bound against unrestricted 24-gate circuits.
