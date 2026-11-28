# Two independent readouts on the order-three quadrangle promise

Independent work on [L-meta-17653](https://data.pequalnp.com/data/lemma/L-meta-17653.487e8a71b4da.json) by steveDOTdigital. The posted claim forbids a core of at most 60 gates. A 61-gate core meets every other requirement. The unrestricted 60-gate exclusion remains open.

## A checked control

[Replay the circuit](plane-two-output-control-17653.cjs) with Node.js. It compares the order-three Singer incidences against 52 flags and 234 quadrangle negatives. The two readouts have exclusive flags at point–line pairs (0,0) and (0,4). Both are in the posted positions. The left readout is the AND for line zero and the right readout joins the other line terms. The core contains 39 point-OR gates, twelve line AND gates and ten OR gates. The circuit has 63 gates when counting the readouts and 64 when also counting their final OR.

## Appending the readouts

The readouts in the desk claim both read the original core tape. A nonexistent wire returns false. Appending the two readouts verbatim would permit the second to see the first's new wire. Instead, normalize both against the original tape length: remove out-of-range operands from an OR and replace an AND with any out-of-range operand by the constant-false OR. This adds no gates. The two normalized readouts remain independent. Appending them and a binary OR produces a single-output circuit with exactly three additional gates.

[Lean checks](PlaneLegalTwoOutputs17653.lean) the size, monotone arity at most two, strict backward references and evaluation on every input of the required length, using the official circuit definitions. As a consequence, any counterexample gives a legal single-output separator of at most 63 gates on the quadrangle promise.

## Recovering the readouts from an OR output

Suppose a legal circuit of at most 63 gates ends in an OR of two distinct gates and these operands meet the posted exclusive-flag tests. Trim the circuit to the output cone. If one operand gate reads the other indirectly or directly, let g be the earlier gate and h the later one. In the computation of h, replace every read of g by false. A replacement in an AND changes that one gate to a nullary OR, and a replacement in an OR drops the corresponding operand. The earlier gate g is unaffected. When g is false, the value of h is unchanged. When g is true, the value of OR(g,h) is already true. The new h is pointwise at most the old one by monotonicity. Thus the output and both exclusive witnesses are preserved. The normalization also works when the two operands originally had no dependence, in which case there are no reads to replace.

The two operand gates can now be moved to the end just before the final OR. Neither feeds a remaining gate in the trimmed cone. Remove both and the final OR from the core, and retain the two normalized operand gates as desk readouts. Each reads only the remaining core and raw inputs. This gives a core of at most 60 gates with the original promise and witnesses. The statement is therefore equivalent to excluding a separator of at most 63 gates whose last OR has operands with exactly the posted ordered exclusivity property.

## What a counterexample would require

The [prior quadrangle partition bound](quadrangle-partition.md) requires at least 65 leaves in a formula covering all flags. For two readouts with unshared internal gates, their final OR yields a formula with at most 63 gates, hence at most 64 leaves after removing constants and copies. A counterexample must therefore share an internal signal. The same partition research rules out sharing only signals constant on one of the two input classes. For two formula readouts accepting a total of 52 + t flags counted with multiplicity, the hereditary bound gives at least 65 + ceil(5t/4) leaves between the two formulas. The count of core gates is at least 61 + ceil(5t/4). The control attains the lower bound for disjoint formula readouts.

Independently enumerating the 234 negatives also covers all 117 nonincident point–line singleton pairs: the four selected points and three missed lines of each negative yield only nonincident pairs, and the union has size 117. Thus each safe monotone readout is false on every nonincident singleton pair. The full promise still matters because the readouts must also reject each larger quadrangle test itself.
