# A cofactor proof for the complemented input and its OR in L-meta-3180

An AND, OR, NOT circuit with at most thirteen gates cannot compute the displayed nine-vertex Petersen edge function from the nine raw bits, the free bit B = NOT x₀, and the prescribed second OR signal. This independent argument uses two [signed circuit lower bounds](petersen-raw-bound.md). The full raw graph G needs at least fourteen signed gates, and deleting its cubic vertex 0 gives a graph U needing twelve. Those numerical bounds have computer-assisted proofs.

The desk's ordered selector list has length two, contains index 9 and has another index outside {0,9}. Consequently the extra OR is D = B OR xⱼ for one of the eight nonzero raw indices j. The [Lean companion](PetersenImplicationPin.lean) proves this for both operand orders and checks the Boolean replacements used below.

## Pinning vertex 0

Set x₀ to zero. The three physical pins A = x₀, B and D become false, true and true, respectively. The restricted target is U. The unrestricted target changes from false at the selected set {1} to true at {0,1}. Every other raw pin is unchanged on that pair.

Count only two-operand AND and OR gates as binary gates. The [strict signed projection lemma](PetersenSignedSlice.lean) gives a signed program for U with strictly fewer gates than this count. Its hypotheses hold because A, B and D are constant on the restricted domain, all other raw pins agree on the witness pair, and U is nonconstant. The lemma handles missing references, complements and constant folding.

Since U requires twelve signed gates, the supposed circuit must have thirteen binary gates. Its entire budget is thirteen. Every gate is therefore a two-operand AND or OR. This also rules out a paid NOT, a unary gate, or an empty gate anywhere in the list.

## Counting original-pin readers

Call a gate a reader if at least one of its two operands is the original pin A, B or D. Two distinct readers disappear under x₀ = 0. Each reads a constant and hence becomes either a copy or a constant. Replacing both in the original order, with earlier values retained or aliased, gives at most eleven signed gates for U. Thus there is at most one such reader.

The circuit output cannot be an original pin or an invalid reference. Under x₀ = 0 such an output is a literal or a constant, whereas U needs twelve signed gates. The output must therefore be a computed gate.

At least one gate must read the original positive pin A. Otherwise, when going from {1} to {0,1}, the only changing physical pins accessible to the gates are B and D, which can only fall. The gate list is entirely monotone, so no computed output can rise. The target does rise. The unique reader must therefore read A.

If the reader's other operand is an ordinary raw input, an earlier computed wire, another copy of A, or an unavailable reference, neither B nor D is ever read and the circuit already computes G from the raw inputs alone. If the other operand is B, the gate result is a constant, false for AND and true for OR. If it is D, the results are A AND xⱼ for AND and true for OR. In every case the entire gate list can be simulated on the raw inputs by a signed circuit with at most thirteen binary gates. Constants are free and the one nonconstant replacement uses one gate. This contradicts the fourteen-gate signed lower bound for G.

All eight added inputs are covered by the same argument. The finite graph lower bounds and the reader-count argument are distinct from the formally checked selector normalization.

## A stronger exclusion when all inversions are free

In fact thirteen further binary gates do not suffice even if every wire can be complemented for free. Begin a raw signed program with the single gate H = x₀ AND (NOT xⱼ). Its two output signs are H and D. The raw signs already include B. Appending a hypothetical thirteen-gate suffix gives at most fourteen raw signed gates. A smaller raw program would contradict the signed lower bound of fourteen for G. The constructed program, if it computes G, therefore has minimum size and uses every gate.

When xⱼ is true, H is constant and G still depends on x₀. For j from 1 through 8, respectively, the masks 2, 20, 10, 16, 32, 80, 130 and 258 have xⱼ high and x₀ low. Adding vertex 0 changes the target from false to true in every case. Hence the program needs a direct reader of x₀ other than H. It also needs a consumer of H. Fix x₀ to zero. H, that consumer, and the additional reader all simplify. If the only possible consumer and additional reader coincide, that gate combines a signed H with a signed x₀. The two-gate composition is a constant, a literal or one signed AND of x₀ and xⱼ, as a two-bit truth table verifies. Replacing it costs at most one gate and contradicts minimality. Thus at least three distinct gates disappear. This would compute U with at most eleven, contradicting its twelve-gate lower bound.

The gate-count argument applies when earlier-wire indices are out of range or an input is duplicated. In a minimum signed program, a constant, literal, copy or unused gate can be removed. A computed output that is H or its complement cannot distinguish the witness pair. The [signed compiler](PetersenSignedInputs.lean) and the [formal first-gate elimination proof](PetersenFirstSignedCut.lean) implement this argument. The latter works at every gate budget, treats an out-of-range read as false, and proves a stronger dichotomy constructively at the program level. Either all extra-signal reads can be replaced by raw gates at the same budget, or pinning vertex 0 saves at least two gates in the suffix. The two numerical bounds for G and U remain computer-assisted. This covers all circuits in the original assignment.

## One seven-vertex bound suffices for both numerical obligations

The [Lean proof](PetersenRawFirstErase.lean) reduces the last two submitted statements to the same signed gate bound. A raw program for G loses at least two gates on some zero restriction. For each of its nine possible deleted vertices we verify an essential second vertex whose removal gives the theta graph with paths of lengths 2, 3 and 3. Pinning that second vertex saves one further gate. A free input relabeling gives exactly the same seven-vertex target in every case. The two unused physical inputs may still be used by the program.

Consequently a signed circuit of size at most thirteen for G, or of size at most eleven with vertex 0 deleted, would give a ten-gate signed circuit for that theta graph. Lean verifies the full transfer, including the exact two emitted child statements. The [exhaustive ten-gate exclusion](petersen-raw-bound.md) is the one remaining numerical premise for this route. The project's merged L-meta-517 proves the ordinary gate bound for the same graph. Its NOT gates count toward the budget.
