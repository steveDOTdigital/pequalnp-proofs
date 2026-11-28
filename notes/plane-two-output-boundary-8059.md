# The 63-gate boundary for the two-output quadrangle claim

Independent work on L-meta-8059, the second checked child of L-meta-5198. The [live catalogue](https://data.pequalnp.com/data/desk/gaps.json) specifies the earlier and final readout wires and counts AND gates with a direct AND operand.

The [finite replay](plane-two-output-boundary-8059.cjs) verifies a circuit of 63 gates with earlier readout wire 87 and last wire 88. The two outputs jointly accept all 52 flags and both reject all 234 negative quadrangles. The first alone accepts (0,0), and the last alone accepts (0,4). All operands name earlier wires and no AND reads another AND directly. The claimed lower bound, if established, is sharp.

## Detaching the two readouts

Suppose the posted circuit has at most 62 gates. Call its earlier readout g and its final readout h. Replace every read of g that occurs in a later gate by false. Delete that operand from an OR and use constant false for an AND that reads it. The gate g itself is unchanged. The new final value h' agrees with h when g is false, and h' is at most h everywhere. Hence g OR h' has the same value as g OR h. A flag exclusively accepted by either original output stays exclusively accepted by that output. Both outputs still reject every negative.

Neither readout now feeds a gate that must stay in the core. Moving them to the end and detaching both leaves at most 60 core gates. Gate count and backward references are preserved by the renumbering. The [flag-pair symmetry check](plane-or-root-symmetry-17653.md) moves the two exclusive flags into the ordered cases listed in L-meta-17653, allowing the outputs to be exchanged. The resulting circuit would refute L-meta-17653. Thus a proof of the earlier separate-readout exclusion would establish this case even without the direct AND-reader limit.

Appending an OR to the two original output wires also gives a single-output separator of at most 63 gates. The [previous quadrangle formula and constant-sharing bounds](quadrangle-partition.md) show that such a separator must reuse an internal wire that is nonconstant on both test classes. The posted limit of one direct AND-reading-AND gate does not by itself eliminate that remaining sharing case.
