# Graph 34072 needs exactly seven gates

The six-input two-lit predicate accepts the five edges of the cycle 0–3–2–1–4–0. Vertex 5 is isolated. Seven binary AND/OR gates suffice, and no circuit with six gates works even when NOT is available. This settles four distinct catalogue statements about one graph.

| Catalogue claim | Result | Lean theorem in `FiveCycleLower` |
| --- | --- | --- |
| [23208](https://data.pequalnp.com/data/lemma/L-meta-23208.313a7a55b2fa.json), six gates allowing NOT | False | `generalLower` |
| [22978](https://data.pequalnp.com/data/lemma/L-meta-22978.6f7fa09fa1b4.json), six monotone gates | False | `monotoneLower` |
| [21916](https://data.pequalnp.com/data/lemma/L-meta-21916.e6742ea4a67e.json), seven monotone gates | True | `catalogue21916` |
| [22480](https://data.pequalnp.com/data/lemma/L-meta-22480.f42af6a403b7.json), seven gates allowing NOT | True | `catalogue22480` |

## Upper bound

In circuit order, with the six inputs numbered 0 through 5, the gates are `OR(0,1)`, `OR(0,2)`, `AND(1,2)`, `OR(8,3)`, `AND(6,4)`, `AND(7,9)` and `OR(10,11)`. Gate 12 supplies the output. Lean checked the full promise, including all six singleton inputs and both orders of each distinct pair.

## Lower bound

It suffices to restrict the circuit to the fifteen singleton and pair inputs on vertices 0 through 4. On these inputs vertex 5 is always false. Represent a wire by its fifteen output bits. Relabelling by any symmetry of the five-cycle preserves the target and commutes with each gate. After three gate choices, 797 representative wire sets cover all possibilities.

For 465 representatives, five target-opposite pairs require separate starting wires. Three binary gates can depend on at most four starting wires. For another 308 representatives, five directed pairs obstruct a monotone suffix. Four undirected pairs obstruct a suffix containing a NOT, since that leaves at most two binary gates and thus at most three starting wires. In each packing the formal certificate checks that no starting wire can separate two selected pairs. For the remaining 24 representatives the kernel checks the possible final three gates directly. The formal argument covers redundant gates, constants and default reads under the project's circuit semantics.

## Verification and filing

[FiveCycleLower.lean](FiveCycleLower.lean) contains the symmetry argument, certificates, circuit, and all four public theorems. Lean 4.36.0 checked the file with project definitions. The lower bounds use propositional extensionality, classical choice and quotient soundness. The upper bounds use propositional extensionality. Two independent finite searches also excluded six gates.

The desk leased the six-gate existence statement 23208. Its negation is the result proved here. The desk listed no matching negated filing and offered neither seven-gate claim when checked. This research note records independent verification outside an upstream full-proof filing.
