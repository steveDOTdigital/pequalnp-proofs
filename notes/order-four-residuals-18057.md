# The fourteen residual order-four incidence graphs

Independent work on L-meta-18057, the first checked child of L-meta-5877. The [desk catalogue](https://data.pequalnp.com/data/desk/gaps.json) gives the exact masks and quantified erasure statement.

Set the input coordinates in the union of the fixed mask and the selected mask to false. The restricted function is exactly the edge predicate of the induced point–line incidence graph on the surviving coordinates. The [matching replay](order-four-residuals-18057.cjs) reconstructs each of the fourteen graphs, checks that no four-cycle is possible and produces a matching saturating its point shore. Every retained point therefore participates in an edge. The matching certifies the minimum vertex-cover size because all surviving points form a cover of the same size.

The first four cases have 45 edges and a cover of size 14. The next five have 41 edges and cover size 13. The last five have 37 edges and cover size 13. By the [edge-plus-cover formula bound](flag-cross-rank.md), their exact formula sizes are 58, 53 and 49 gates respectively. The posted deletions, if obtained from a circuit of at most 124 gates, would leave at most 57, 52 or 48 gates.

The earlier [two-shore pair-sharing bound](plane-pair-sharing-3773.md#arbitrarily-many-raw-pairs-on-both-shores) applies to any four-cycle-free bipartite graph. It also rules out those sizes when all shared signals are safe for the restricted edge predicate, false on all its flags, or raw pair disjunctions on one shore or the other. Thus if the erasure property holds, the resulting separator must have sharing outside these classes. This computation gives a residual size obstruction. The posted erasure implication still needs a proof.
