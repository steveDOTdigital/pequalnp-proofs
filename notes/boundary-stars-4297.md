# Shared circuits with shore-separated boundary gates

For [L-meta-4297](https://pequalnp.com/lemma#L-meta-4297), let the graph have m edges. The desk asks for a list of stars covering exactly those edges whose number of leaves plus number of stars minus one is at most the circuit size. The circuit is binary monotone, the bipartite graph has no four-cycle, and the desk imposes a condition on OR gates. The following argument proves the requested bound for a subclass with arbitrary shared preprocessing.

Call a wire below the output if it can be true only when the output is true. A boundary gate is a below-output gate with no below-output operand. Work in the ancestor graph of the output. It suffices that, at each boundary gate used to cover an edge, its two operand functions depend on opposite shores. This is a semantic condition. Their actual implementations can mix variables, use AND as well as OR, and share gates freely. Boundary gates that accept no two-endpoint edge input need no separation condition.

## Finding the stars

For a nonempty graph, every raw input is true on its singleton while the output is false. The desk's OR condition therefore implies that any OR with a below-output operand has two below-output operands. In fact every below-output OR has two below-output operands, directly from the definition. Every consumer of a below-output wire is itself below the output: this follows from monotonicity for AND and from the desk condition for OR. Thus every boundary gate is an AND. On any edge input, follow true below-output operands backwards until a boundary gate is reached. At an AND every operand is true, and at an OR every operand is below the output. This covers all edges by boundary gates.

On the input consisting of one left and one right vertex a gate with shore-separated operands accepts the Cartesian product of their singleton hits. Every pair in that product is an edge because the gate is below the output. A nonempty product in a four-cycle-free graph has a singleton side. Choose its vertex c as center, resolving a single edge arbitrarily. Assign each graph edge to just one boundary gate that accepts it and discard unused gates. For each of the K retained gates the assigned edges form a nonempty star. Write C for the set of distinct centers, k(c) for the number of retained gates centered at c, and d(c) for their total number of assigned edges. The d(c) leaves assigned at one center are distinct.

Let q be the leaf-side operand of a gate centered at c. It is true on each assigned leaf singleton. It is false on the input that turns on every vertex outside the full neighborhood N(c). Indeed its value there equals its value on the leaf-shore nonneighbors alone. If that value were true, turning on c and those nonneighbors would make both operands true on an independent set.

## Counting the shared gates

Fix c and its assigned leaves D. From its k(c) leaf operands build a backwards graph of wires. Keep a wire only when it is true on some singleton in D. Every retained wire is false with all vertices outside N(c) on. At an OR follow both operands with a hit. At an AND choose one operand false on that outside input and follow it. Such an operand exists and retains every singleton hit of the AND. Stop at any wire with only one hit and replace it by a source named for that leaf. Gates at larger hit sets have at least one and at most two predecessors. For every original hit, a path with that hit reaches its named source. All d(c) sources therefore occur. Merging stops with the same label is allowed.

In the underlying undirected graph there are at most k(c) components, since every vertex reaches an initial operand. If there are t nonsource vertices and j have two distinct predecessors, the graph has at most t+j edges and at least d(c)+t-k(c) edges. Thus j is at least d(c)-k(c). Charge that many distinct physical gates. Each charged gate accepts at least two distinct assigned singleton leaves and rejects the input having all vertices outside N(c) on.

No gate can be charged at two centers. A monotone gate rejecting the outside input of another center must have all its singleton hits in that other neighborhood. Distinct same-shore centers have at most one neighbor in common. Opposite-shore centers have disjoint neighborhoods. A charged gate is also distinct from every below-output gate, since it accepts a singleton.

The K retained boundary gates require at least K-1 additional below-output gates to connect them to the output. Take a path from each to the output, all within below-output gates, and count distinct edges of their connected union. Each retained boundary gate has no incoming edge in the union; every other vertex has at most two. With t other vertices the union has at least K+t-1 edges and at most 2t. This gives the claimed K-1.

In total the circuit size is at least the sum of d(c)-k(c), plus K, plus K-1, which is m+K-1. The K assigned stars are a list of exactly the requested cost. For an empty graph the empty list works by truncated subtraction.

The counting proof also applies when the boundary operands mix shores, provided one can choose these same K stars and leaf operand witnesses with the two test properties: accepting each assigned leaf singleton and rejecting the all-on complement of N(c).

## Why the extra condition matters

Take edges ab and cd with left shore {a,c} and right shore {b,d}. Form the four raw ORs (a OR c), (a OR d), (b OR c), (b OR d). AND the first two together and the last two together, then AND those results. The result is ab OR cd. Each of the two intermediate ANDs accepts a singleton. The final AND is the only boundary gate and accepts both disjoint edges. Every OR has raw operands and meets the desk condition. This example satisfies the desk conclusion with two stars and cost three. It shows why extracting one star per boundary gate needs an additional argument in the general case.

This is a written partial proof. The unrestricted statement and its literal negation remain open in this work.
