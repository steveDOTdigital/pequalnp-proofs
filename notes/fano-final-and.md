# A final AND for Fano incidence

**L-meta-4874 remains open for unrestricted circuits.** Its negated existence claim rules out 27 binary AND/OR gates with a final AND whose two operands both reject the singleton point 0 and the singleton line 0. A circuit with **28 gates** satisfies every other condition. An AND-root formula satisfying the same tests needs **at least 31 leaves, or 30 gates**. Even arbitrary sharing of disjunctions above a forest of private formulas requires 28 gates, and this last bound is attained.

A point $p$ lies on line $l$ if $p-l$ is 0, 1 or 3 modulo seven. Write $F$ for the edge function on the fourteen Boolean inputs. The desk tests the 21 edges and the maximal independent sets. These determine the value on every input for a monotone circuit.

## The 28-gate circuit

Take point 2, which is off line 0. Let $A$ be the OR of the six full point stars other than point 2, and $B$ the OR of the three lines through point 2. The output is

```
(A OR point2) AND (A OR B).
```

The six stars and their five joining ORs cost 23 gates. Two gates compute $B$, and three more finish the circuit. Each operand rejects both prescribed singletons. [Lean's `witness28`](FanoFinalAnd.lean) verifies legality, distinct operands, the exact final gate, both singleton tests and the required positive and negative inputs. Its `controlCorrect` theorem proves equality with incidence on every input.

## Necessary conditions for either operand

Write the output as $H$ AND $K$. If $H$ ignores a variable $v$, every neighbor of $v$ must make $H$ true as a singleton, because the pair is an edge and removing $v$ leaves the value unchanged. Ignored vertices form an independent set. They avoid the three neighbors of each prescribed singleton. On the other eight vertices the graph is an eight-cycle. Thus an operand depends on at least ten inputs. At exactly ten, its four ignored inputs are either the four points off line 0 or the four lines missing point 0.

If $H$ accepts singleton $a$ and $K$ accepts singleton $b$, the pair must be an edge. Consequently, if $H$ ignores $v$, every singleton accepted by $K$ must be adjacent to all three neighbors of $v$. Only $v$ has that property. Since ignoring any vertex would force $K$ to accept three singletons, $K$ depends on all fourteen inputs. This argument permits arbitrary sharing of gates. The Lean theorem `factorSupports` derives these conclusions directly from monotonicity, incidence, and the two singleton tests. Its supporting lemmas also identify the only possible singleton for the other operand. The neighbor table uses point wires 0 through 6 and line wires 7 through 13.

There is also a canonical choice of function for an operand that ignores a set $O$. Raise all coordinates in $O$ to one and evaluate $F$ on that assignment. Replacing $H$ by this function preserves the product with the original $K$. Indeed, the new value lies between $F$ and $H$ pointwise, by monotonicity of $F$ and independence of $H$ from $O$. The Lean theorem `canonicalFactor` proves this for arbitrary Boolean targets and omitted sets.

## Why a formula needs at least 31 leaves

Suppose first that $H$ accepts a singleton $a$. When $a$ is set to one, $K$ must compute $F$ on every remaining input. This restricted function is the OR of the three neighbors of $a$ and the graph remaining after removing $a$ and those three neighbors. The remaining graph is a subdivision of $K_4$ with twelve edges. Its four vertices of degree three form its unique minimum vertex cover. Each degree-two vertex covers at most two edges, and four vertices covering twelve must all have degree three.

The restricted graph needs sixteen formula leaves by the edge-plus-cover bound. Its equality proof gives exactly one occurrence of each degree-three vertex and two of each degree-two vertex. To see this, split each vertex into its different flag-output patterns in the formula's rectangle partition. Its number of patterns is at most its number of leaves. The split graph is a star forest. With sixteen leaves it has precisely four components, whose centers project to a four-vertex cover. The unique cover and the degree sum force four full three-edge stars. The three neighbors of $a$ contribute at least three additional leaves in the restricted function, since each is an essential singleton. Setting them to zero leaves the subdivision. Hence $K$ with $a$ fixed needs at least nineteen leaves. [Restricted-row bound and splitting argument](heawood-rectangle-partition.md)

If $K$ omits an input, $H$ has full support, giving at least $14+19=33$ leaves. Otherwise $K$ has an occurrence of $a$, which is removed on restriction, and so needs at least twenty leaves. Together with $H$ this gives thirty. Equality would require exactly ten leaves in $H$ and twenty in $K$. Then $H$ omits one of the two four-vertex sets described above and accepts six singletons of the opposite shore. Pick two of these, $a$ and $b$. Restriction at $a$ can remove only its single occurrence, since nineteen leaves are still needed. Setting the three singleton neighbors of $a$ to zero can likewise remove only their three occurrences. The sixteen-leaf equality case forces $b$, which is on the same shore as $a$ and is a degree-two vertex of the subdivision, to occur twice. Restricting at $b$ instead forces it to occur once. This excludes equality. Interchanging the operands gives the same conclusion when $K$ accepts a singleton.

Now suppose neither operand accepts any singleton. Both require all fourteen inputs, as is seen on the incident pairs. Consider the set of variables occurring more than once within at least one operand. It must meet every induced four-vertex path. Otherwise set all inputs outside such a path to zero. Each operand becomes a read-once formula, accepts every path edge, and rejects singletons. Its top gate cannot be OR: an edge crossing the two disjoint child supports could not be accepted, and the path is connected. At an AND the two supports must be the two shores, as an edge inside one support cannot satisfy the other child on empty input. Every vertex must then satisfy its own child as a singleton. Both operands accept the missing corner of this path, contradicting $F$. The same reasoning rules out a constant or a leaf after simplification.

There are 84 induced four-vertex paths. Checking the 16,384 vertex subsets gives minimum hitting size five, attained by fourteen sets. Hence the no-singleton case actually needs at least $14+14+5=33$ leaves. This hitting-set constraint applies to the two unfolded operands of any candidate circuit as well.

## When all sharing is in the top OR gates

Suppose the part before the final AND consists of an arbitrary OR network whose sources are raw wires or the outputs of private formulas with disjoint gate sets. Raw variables may be reused freely inside or between those formulas. Discard unused gates and regard each distinct source wire as an atom. Each of the final operands is the OR of a nonempty atom set, say $S$ and $T$.

If the sets are disjoint, the two OR cones have no gate in common. Replacing each by a tree on its atoms produces an AND-root formula at no increase in gate count. The preceding lower bound applies.

If they overlap, their two cones form a connected graph on $m=|S∪T|$ source wires and $g$ OR gates. This graph has at most $2g$ edges, so $g≥m-1$. Including the final AND gives at least $m$ gates above the source formulas. Factor the intersection as a common disjunct. When both differences are nonempty the resulting expression is the OR of the common part and the product of the two exclusive parts. It uses each of the $m$ atoms once and exactly $m-1$ binary gates. When one set contains the other, use the smaller disjunction alone. Substituting the private formulas now gives a formula at least one gate smaller than the circuit. Every formula for Fano incidence needs 27 gates, so this circuit needs at least 28. The construction above attains equality. [General Fano formula lower bound](heawood-rectangle-partition.md)

Thus a 27-gate witness would require sharing below this OR network. It cannot be obtained by sharing disjunctions of private formula outputs alone.

## Finite search around the witness

The [C++ reproducer](fano-final-and.cpp) checks the 21 positive pairs, the 37 maximal independent sets, and both singleton operands. Starting from the displayed circuit, it removes any non-output gate, redirects its outgoing uses to any one wire that keeps the intermediate graph acyclic, and replaces any surviving gate by either operation on any distinct pair of non-descendant wires. It permits reordering and checks the final operand restrictions. Across 943 acyclic bypasses and 28,640,932 legal replacement choices, none passed.

A second search removes an upward-closed set of three through six gates containing both final operands and the output. It synthesizes an arbitrary new terminal circuit using at most one fewer gate, with every retained wire available. All fourteen such cuts failed (one of size three, two of size four, four of size five, seven of size six). With the original 28-gate allowance the synthesizer reconstructs a legal three-gate ending as a positive control. These searches concern the displayed circuit. They give no verdict on circuits outside those families.
