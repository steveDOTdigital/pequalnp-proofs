# The 4 by 6 one-a-side matrix with mask 1865323 needs 11 gates

The [posted statement](https://data.pequalnp.com/data/lemma/L-meta-23832.bfba440700d2.json) asserts a circuit of at most ten monotone binary gates. The rows of the matrix, represented as six-bit masks in the posted order, are 43, 25, 7 and 7. A finite exhaustive calculation proves the ten-gate statement false. Lean checks the eleven-gate upper bound on exactly the same promise. [Exhaustive replay](https://github.com/steveDOTdigital/pequalnp-proofs/blob/20f13eaa3c03ed5ab929f106e1270835b0a54f52/notes/one-a-side-exact-1865323.cjs) · [Lean upper bound](https://github.com/steveDOTdigital/pequalnp-proofs/blob/0af3d4fbe6c8fa67290bc17f72849e0d00ef326c/notes/Mask1865323.lean)

## Every input must be read

For each raw input (x), the replay records a positive promised row containing (x) and a negative promised row obtained by using a different vertex on its shore while retaining the opposite vertex. If the circuit ignored (x), we could turn it off on the positive row without affecting the output. The resulting assignment is coordinatewise below the negative row, contrary to monotonicity. Hence all ten distinct raw inputs must reach the output.

## A ten-gate circuit has at most one excess read

Simplify constants, copies and repeated operands in evaluation order, using false for an invalid read, and keep only the output cone. The resulting gates are binary ANDs and ORs. The output cannot be a constant or a raw variable, because all ten raw variables are required. If there are (g) remaining gates, the (2g) operand slots must read each of the ten inputs and each of the (g-1) internal outputs other than the final output at least once. Thus (g\ge9). At nine gates every source is read exactly once. At ten gates there is exactly one additional read.

If that read is of a raw input, the circuit is a formula with that one repeated leaf. If it is of an internal output, the ancestors of the shared gate form a read-once tree on a subset of the raw inputs. Every wire in that tree, except its root, has its sole consumer within the tree. The remaining calculation is a formula on the complementary raw inputs and two occurrences of the shared root. These cases exhaust the allowed circuits, including gates that simplified away.

## Certifying the finite exclusion

Represent each signal as a 24-bit mask, with bit (6a+b) corresponding to the promised row with left input (a) and right input (b). To enumerate formulas on labeled leaf occurrences, work upward over all subsets of leaves. For each subset, combine every truth table from every complementary split by bitwise AND and OR. A single representative per truth table suffices. Duplicate leaves are distinct positions with the same initial mask.

The enumeration prunes intermediate tables using a necessary condition. Put two promised rows in the same class when their bits at all leaves outside the subtree agree. On each class, the final output is a monotone function of the subtree output alone. When a class contains both positive and negative rows, that function must be the identity. The intermediate table must therefore already have the target bits throughout the class. The same implication holds when the subtree is the private input cone of a shared output, since the remaining formula is monotone in both occurrences of that output and both occurrences have the same value.

The replay first excludes read-once formulas and formulas with one repeated raw input. It then checks each of the 162 surviving candidate tables for a shared subtree and excludes every formula that can use that table twice. This proves the eleven-gate minimum with the constructive upper bound. Lean verifies the upper bound. The finite exclusion and topology argument are checked by the replay and written proof.

The lease supplied no negated twin. The live catalogue search for the exact mask returned only the positive claim.
