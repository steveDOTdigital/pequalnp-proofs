# One nested AND on the plane quadrangle tests

The order-three projective plane has 13 points, 13 lines and 52 incidences. A positive input switches on just the point and line of one incidence. A negative input switches on the four points of a quadrangle and every line avoiding those four points. We consider monotone circuits with binary gates.

**Claim.** Suppose the output is an OR of ordinary products of two raw-input disjunctions and one product of three raw-input disjunctions. All clause disjunctions may share arbitrary OR gates. This circuit needs at least 64 gates. If the three-clause product has its own inner AND and outer AND, the count is at least 65. If it accepts pairs on both arms of a genuine double star, the count is at least 66.

Here a raw-input disjunction is an OR of some of the 26 inputs, including a single input. The OR combining product outputs is binary as well. A later AND that reads an OR of several earlier ANDs is outside this argument.

## What one product can cover

Label each raw input by the set of clauses it belongs to. A product accepts a pair precisely when their labels together cover all clauses. Its output alone must reject all quadrangle inputs. In particular, it rejects every singleton, every pair on one side of the incidence graph, and every nonincident point-line pair. The Lean file certifies this implication with 26 quadrangles that contain all 299 forbidden unordered pairs, counting repeats.

Consider two disjoint accepted edges. Each clause meets both edges, so it can miss at most one of the four pairs obtained by taking one endpoint from each edge. Two of these four pairs are on the same side and must be rejected. With three clauses at least one of the two crossed point-line pairs is accepted. The point neighborhoods of the accepted graph are therefore nested by inclusion. With two clauses both crossed point-line pairs would be accepted, giving a four-cycle. The projective plane has no such cycle. Hence every nonempty ordinary product covers a star of at most four edges.

In a nested family of point neighborhoods, two different points with at least two neighbors would also give a four-cycle. Thus there is at most one such point. The remaining nonempty neighborhoods are singletons and nested, so they are all at the same line. This places the accepted edges on a star or on the union of the stars at an adjacent point and line. The latter has at most seven edges. The bound is sharp. For incident centers $u,v$, take the three clauses consisting of the lines through $u$, the points on $v$, and the two centers together. The product accepts all seven incident edges in their union. On a quadrangle input, an active center disables its opposite-side clause, and with neither center active the third clause is false.

Consequently, if there are $r$ ordinary products and one three-clause product, then $52\le 4r+7$, so $r\ge12$.

## Counting shared OR gates

Every ordinary product with a positive edge has a singleton center clause and a neighbor clause. Indeed, the two clause supports are disjoint because singletons are forbidden, and every pair across the supports must be an incidence. They form a complete bipartite subgraph of a graph without four-cycles. For a single edge either endpoint can serve as center. Charge each neighbor clause to the chosen center.

If the three-clause product covers a star with center $c$, choose a clause missing $c$. It contains every neighbor accepted with $c$. Charge this clause to $c$, even if it contains additional variables. A product with no positive edge needs no charge.

If its graph is a genuine double star with centers $u,v$, select an accepted path $a,u,v,b$, where $a$ is a line and $b$ a point. The fourth edge $b,a$ is forbidden. The three-bit label check in `pure_arms` yields distinct clauses with the following properties.

- The first consists exactly of the lines whose pair with $u$ is accepted.
- The second consists exactly of the points whose pair with $v$ is accepted.
- The third contains both $u$ and $v$.

Charge the first two clauses to their respective centers. Count the central incidence on both arms.

For each center $c$, let $U_c$ be the union of the neighbors on its charged edges and let $k_c$ count its charged clause terminals. These terminals depend collectively on all of $U_c$. Project their raw OR circuits onto inputs in $U_c$. Remove empty branches and bypass an OR if its projected support equals one of its inputs. The resulting directed graph reaches all $|U_c|$ sources from at most $k_c$ terminals. Each surviving binary OR can increase the backward frontier by at most one, so at least $|U_c|-k_c$ distinct OR gates survive. Equivalently, the underlying graph with $s$ sources, $g$ merge gates and at most $k_c$ components has at most $2g$ edges and at least $g+s-k_c$.

These charges count distinct gates across centers. With at most one exceptional star clause, any gate occurring in cones for two centers is in at least one ordinary neighbor cone. Its support there is contained in the neighbors of that center, which intersect the other center's neighbors in at most one vertex. Such a gate cannot survive both projections. In the genuine double-star case the two special arm clauses also consist exclusively of neighbors of their respective centers, so the same reasoning applies to every pair of cones.

In the star or empty case, the charged edges cover the 52 incidences, and there are at most $r+1$ terminals. This requires at least $51-r$ preprocessing ORs. The $r+2$ distinct product ANDs and at least $r$ output ORs give at least $53+r\ge65$ gates.

In the genuine double-star case, at least 53 edges are counted across centers, including the common edge twice, and there are at most $r+2$ terminals. Every charged cone is pure. The third clause needs an additional OR whose support contains both point $u$ and line $v$. That gate belongs to none of the charged cones. The resulting total is at least $53-(r+2)+1+(r+2)+r=54+r\ge66$.

Repeated top terms can be removed. If the inner AND is itself an ordinary term in the output, absorption removes the whole three-clause term. The remaining flat circuit has $t\ge13$ nonempty ordinary terms, at least $52-t$ preprocessing ORs by the same charge, $t$ ANDs and at least $t-1$ output ORs. This gives $51+t\ge64$. The usual circuit with one four-edge star per point attains 64.

## Several nested terms with shared inner AND gates

The same 64-gate lower bound holds for an OR of any number of two- and three-clause products under the following condition. For each three-clause product whose accepted edges form an ordinary star, choose its center. Set aside stars that have a missed clause consisting entirely of neighbors of their center. The centers of the remaining stars must all be points, or all be lines. Three-clause products covering genuine double stars may have arbitrary centers. Both inner ANDs and clause ORs may be shared. If a genuine double star survives absorption, the bound is at least 65. If every surviving three-clause product is a genuine double star, it is at least 66 whenever there is one.

**Choosing terminals.** For any center and two opposite-side vertices outside its neighborhood, a negative quadrangle activates all three. This also holds when the two vertices coincide. The Lean file certifies both orientations using 65 quadrangles. A center with an accepted neighbor misses one or two of its three clauses. It cannot hit all three, since its singleton is forbidden. It cannot miss all three, since then the neighbor would hit all three alone. At least one missed clause has no opposite-side off-neighbor. Otherwise take one off-neighbor from each missed clause. A quadrangle activating these vertices and the center would satisfy the product.

For a star with a missed clause consisting entirely of neighbors, use that pure clause. For each remaining three-clause star, choose the clause just established as its terminal. Its support on the side opposite its center is contained in the neighborhood of that center, and it contains every accepted neighbor. Two such terminals centered on different points cannot share an effective OR charge because their line supports intersect in at most one line. The same holds for different line centers after interchanging the sides. A shared gate with a pure terminal from an ordinary star or a double-star arm also cannot be charged at two centers. Hence the preceding projection count still applies to all terminals under the stated condition.

**Counting terms and centers.** Discard terms that cover no positive pair, drop repeated outputs, and use absorption if an inner AND is already a top-level term. Let $r$ count ordinary products, $e$ count three-clause stars, $k$ count genuine double-star products, and $s$ count distinct inner AND gates used by the surviving three-clause products. Let $d$ count the distinct central incidences of the double stars. Their central edges are counted on both arms, so the sum of the charged neighborhood sizes is at least $52+d$. There are at most $r+e+2k$ terminals. Add $r+e+k+s$ distinct AND gates and at least $r+e+k-1$ output ORs. The resulting bound is $51+d+r+e+s$ gates.

Let $C$ be the set of all charged centers. Each group of genuine double stars sharing an inner AND has a common center. Indeed, at least one of the two operands of that AND is a pure arm clause. It contains at least two neighbors, which uniquely determine their center. Its pure support prevents that operand from serving as the mixed clause in a different double star. Thus every connected component of the graph of central edges uses an inner AND distinct from those in other components. A graph with $d$ edges and at most $s$ nonempty connected components has at most $d+s$ nonisolated vertices. Ordinary and three-clause stars add at most $r+e$ other centers, giving $|C|\le d+s+r+e$.

The centers cover all 52 incidences. The disjoint incidences at offset zero force at least 13 centers. With a center on each side the cover has size at least 14. To see this, a cover of size 13 must use exactly one endpoint of each offset-zero pair. Every omitted point then forces the line of the same index, and the offset-one incidences force the previous line as well. Cycling modulo 13 puts all lines in the cover as soon as there is one omitted point. Lean verifies this in `mixed_cover`.

Consequently a genuine double star forces at least $51+14=65$ gates. If all surviving three-clause products are genuine double stars, all terminals are pure, and one mixed OR is additionally required, giving 66. If only stars survive and at least one has three clauses, then $r+e\ge13$ and $s\ge1$, also giving at least 65. If all surviving products are ordinary, the flat bound of 64 applies.

The unrestricted assignment also allows three-clause stars requiring impure terminals on both sides, deeper products, and AND gates applied to disjunctions of earlier products.

## Verification

[QuadrangleTerms.lean](QuadrangleTerms.lean) verifies the negative test certificate, the star and double-star bounds, the sharp seven-edge example, the twelve-term minimum, the pure-arm clause classification, both triple-extension properties, the existence of the restricted-support clause, and the minimum mixed vertex-cover size. The shared-OR gate count above is a mathematical proof in prose. From the repository's `lean` directory, run `lake env lean ../notes/QuadrangleTerms.lean`.
