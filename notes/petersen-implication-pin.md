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
