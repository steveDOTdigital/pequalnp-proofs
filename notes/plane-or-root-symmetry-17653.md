# Every exclusive flag pair is covered by L-meta-17653

The [posted statement](https://data.pequalnp.com/data/lemma/L-meta-17653.487e8a71b4da.json) fixes the first exclusive flag at (0,0) and gives four possible second flags. For any ordered pair of distinct flags, a projectivity and an optional exchange of the two readouts put it in one of those forms. The [independent coordinate replay](plane-readout-orbits-17653.cjs) covers all 2,652 ordered pairs.

## Geometric replay

Represent point zero by the vector (1,0,0) over the field with three elements. Generate subsequent point representatives by applying the invertible map (x,y,z) ↦ (−z,x+z,y). The vector cross product of points l and l+1 gives a normal for line l. The script verifies that membership is exactly p−l in {0,1,3,9} modulo 13 for every point and line. Every invertible three-by-three matrix permutes the projective points. Its line permutation comes from the resulting incident point sets. The action preserves flags, collinearity, quadrangles and the missed-line sets.

The four representatives for the second flag are (0,4), (1,0), (1,1) and (2,1). Enumerating the 11,232 invertible matrices and both output orders gives 156, 156, 936 and 1,404 ordered pairs, respectively. The four sets are disjoint and their union contains every ordered pair of distinct flags. Applying the inverse projectivity to the raw-variable indices preserves gate count, backward references and both promise classes.

## Consequence for small single-output circuits

Take a separator of at most 63 gates ending in a binary OR. If one operand has no flag where it alone is true, the other operand by itself separates the promise and the final gate can be removed. Otherwise both operands have exclusive flags. Every raw input is true on at least one negative quadrangle row, so both safe operands must be gate outputs. They are distinct. Apply the geometry above, then [remove the final OR and move the two readouts off the core](plane-two-readouts-17653.md). The result is a counterexample to L-meta-17653.

Conversely, the [Lean-checked join](PlaneLegalTwoOutputs17653.lean) converts any counterexample into such a separator. This makes the posted statement equivalent to the absence of a legal separator of at most 63 gates whose last gate is a binary OR with two operands that each accept some flag the other misses. In particular, a proof of the posted statement would force a minimum separator of at most 63 gates to end with a binary AND.

## Local search result

The [bypass search](plane-two-readout-bypass-17653.cjs) started from both the point-star and line-star 61-core controls. It tried replacing each core gate by each earlier raw or gate wire. It either left all remaining gates unchanged or allowed one remaining core gate or one readout to take a new AND/OR definition. Constant outputs and copies were included. For each location, setting its value to zero and one on the whole promise determines the permitted replacement values. The search examined 6,832 bypasses, 423,584 locations and 357,452,266 replacement definitions across both controls. It found no witness. Run `node notes/plane-two-readout-bypass-17653.cjs --both` to reproduce the search. The unrestricted bound remains open.
