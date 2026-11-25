# Simultaneous circuit rewrites on the original wire values

Case L-meta-2773 asks for a counterexample to replacing one read of a wire by an earlier, larger wire whose truth implies the whole output. Such a counterexample is impossible. On a positive input the edit can only increase wire values. On a negative input the proposed wire is already false, so the edit cannot increase the output. The earlier-wire and binary-gate requirements survive, and the gate count is unchanged. The project already accepted [nicohabets's proof of the opposite theorem](https://github.com/open-goat/pequalnp-proofs/pull/5024).

The [independent Lean proof](BatchWireRewrite.lean) verifies the actual list edit in `noCounterexample` and proves two extensions. The first certifies a fixed batch of changes. The second gives an exact test for every combination from a family of proposed changes.

## Compare all edits on one original execution

Take two gate lists of equal length and the same output index. All operands read earlier wires, and every proposed new gate is monotone. Fix an input. Evaluate every proposed gate on the **original** register values. If the original output is true, require that whenever an original gate is true its proposed gate is also true. If the output is false, require the reverse implication. These checks suffice even when proposed gates read other gates changed by the same batch. The arity and operation may change.

On a true input, start the old and new circuits with equal registers. At each gate the local test compares the old gate with the proposed gate evaluated on the old registers. Monotonicity compares this value with the actual proposed gate on the new registers. Induction keeps the entire new tape at least as large as the old tape. On a false input, reverse both inequalities. The output is equal in either case. This is `batchCorrect`. For the desk's single-port edit, the two implications in the statement give exactly the required orientation, and `replacementSyntax` checks binary arity and legal backwards reads.

## An exact test for every combination of edits

Give each gate position a nonempty menu of allowed monotone gates and their operand lists. The choices at different positions are independent. A menu can include the original gate, so the test includes any subset of proposed changes. For a fixed input, keep one register tape. At each position evaluate every candidate on the current tape and append the smallest candidate value for a lower bound, or the largest for an upper bound.

Every choice of gates stays between those two tapes by monotonicity. More importantly, **each extremal tape is attained by a single complete choice on that input**, simultaneously on all registers. At each step choose a gate attaining the current extremum, then continue on that same tape. Downstream sharing does not introduce an inconsistency, and the optimizing choice can differ between input rows.

To check that every complete choice computes a specified target, use only the lower tape on true rows and only the upper tape on false rows. The answer is exact: an incorrect extremum supplies a violating choice on that row. For a monotone target it suffices to test all minimal true rows and all maximal false rows, or any positive and negative test families with the same order-cover properties. For a graph edge function these are the edge rows and maximal independent sets. The Lean theorems `attainableTape`, `allChoices` and `frontiers` establish these statements. Runtime per row is linear in the total number of listed candidate operands and gates, rather than the product of the menu sizes.

Checking one edit at a time can miss a failure. Form h = x OR y and use x AND x as the output. Replacing either operand by h still computes x. Replacing both computes x OR y, which differs at x = false, y = true. Lean checks this circuit in `interacting`.

The proof uses [the verified circuit interpreter](TightBinaryCircuit.lean) and the upstream `PEqualNP.Defs.TopForm` definitions at commit `332a18e1`. From the upstream Lean environment, compile `TightBinaryCircuit.lean` into a fresh temporary directory with `lean -R ../notes -o "$tmpdir/TightBinaryCircuit.olean" ../notes/TightBinaryCircuit.lean`. Add that directory to the active Lean search path and check `../notes/BatchWireRewrite.lean`.
