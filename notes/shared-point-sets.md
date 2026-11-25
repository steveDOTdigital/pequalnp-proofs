# Shared OR gates on one shore of a bipartite graph

For the graph in [case 2872](https://pequalnp.com/lemma#L-meta-2872), let E be the edges and M any matching. Suppose the only shared gate outputs in a binary AND/OR circuit are ORs of point inputs. They can be nested, have arbitrary fanout, and depend on overlapping sets of points. Remove redundant one-point ORs. Let b count shared outputs whose support is contained in no single line. A circuit computing the edge predicate requires at least

    |E| + |M| - 1 + b gates.

The graph can be any finite bipartite graph without a four-cycle. Taking a maximum matching gives the vertex-cover version by König’s theorem. Exchanging the shores gives the same statement for shared ORs of lines. For case 2872 the outstanding issue is arbitrary shared gates, including ANDs and signals that depend on both shores.

## Choosing which edges to keep

Cut the shared outputs to get a final AND/OR formula and one binary OR tree per shared output. Each OR tree can read raw points or earlier shared outputs. Write S for a helper’s entire point support and D for the distinct point inputs read directly by its tree. For each p in D, select a partner q in S other than p. If p has a matched line and a member of S is off that line, choose such a member. Discard the edges at p whose line also contains q.

Two distinct points share at most one line, so each occurrence of p in D costs at most one edge. If it costs a matched edge, all of S lies on its line by the choice of partner. Each S has at least two points, so that line is unique. Its endpoint in the matching is unique as well. Each collinear helper can therefore cost at most one matched edge. The other helpers cost none.

For any point in a helper’s support, follow earlier helper inputs until reaching a tree that reads the point directly. That tree’s partner belongs to the original support. This is why the same partner choices work with nested sharing.

## Charging the gates

For every retained edge, the cross construction from [the formula rank proof](FlagCrossRank.lean) still forces a physical endpoint. In a comparison involving a virtual helper, the selected point or its inherited partner keeps the helper true. The weighted rank bound charges at least one physical input leaf per retained edge and another per retained matching edge.

Each binary OR tree with t gates has t+1 input leaves. The distinct raw points charged to that tree and its occurrences of earlier helper outputs together account for at most t+1 leaves. Each shared output is used at least twice across the final formula and the OR trees. Summing these counts gives the bound above.

[Checked Lean proof](OneShoreSetRank.lean). The theorem `networkBound` takes finite acyclic OR regions, their supports, and the residual formula as input. It verifies partner selection, both deletion bounds, the protocol rank, tracing through earlier regions, and the binary gate count.
