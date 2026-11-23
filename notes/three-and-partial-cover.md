# Three AND gates force a three-vertex cover on the partial graph domain

For L-meta-958, let G be any finite simple graph without a four-cycle. Suppose a monotone circuit with free ORs is false on every maximal independent set I and true on I together with any one vertex outside I. If the circuit has at most three AND gates, **G has a vertex cover of size at most three**. The following finite proof covers all graph sizes. Its final case distinction is executable in [Python](check-three-and-covers.py).

## The eight choices

Pad a smaller circuit with unused ANDs to three and number them in topological order. The bare output OR contains no vertex: every vertex belongs to some maximal independent set, and the output must be false on that set. Each AND has two sides, each an OR of bare variables and earlier gate outputs. Empty sides are allowed.

For each of the eight choices of one side at each AND, replace each AND by that side. The result is a disjunction of bare variables with some support B. Its output dominates the original circuit on every input. At any fixed input, at each false AND choose a false side and at each true AND choose either side. Topological induction shows that this choice keeps every original gate value. Both statements allow multiple uses of an earlier gate.

For any maximal independent set I, select a choice that keeps the output false. Then B avoids I. Adding any vertex v outside I makes the original output true, so the disjunction must become true as well. Thus B is exactly the complement of I. Select one such choice for each distinct maximal independent set. Distinct sets require distinct choices. The resulting nonempty set S of selected choices has at most eight members; the empty graph also has the empty maximal independent set.

Represent each vertex by the subset of S consisting of the maximal independent sets that contain it. Its profile is nonempty. Two vertices are adjacent precisely when their profiles are disjoint: any independent pair extends to a maximal independent set. For the same reason any three pairwise intersecting profiles have a common member, since their three representative vertices are independent.

## Removing equal profiles

Take one representative per distinct profile. Vertices with the same profile are independent and have identical neighborhoods. If there are at least two in one class, its vertices have at most one neighbor in the full graph. Two distinct common neighbors would give a four-cycle. A three-vertex cover of the representatives therefore lifts to a cover of the full graph. For each selected representative from a repeated class, take its unique neighbor if it has one, discarding it if it has none. Keep selected singleton representatives. The neighbor of a nonisolated repeated class is itself in a singleton class: otherwise the two classes contain a four-cycle. Each edge covered in the representative graph is now covered for every corresponding pair of original vertices.

## Listing the finite families of profiles

The output chooses a subset of three gate outputs. The two sides of gate 1 (indices start at zero) each choose a subset of gate 0, and the two sides of gate 2 each choose a subset of gates 0 and 1. Gate 0 has no earlier gate. This gives 8 × 2² × 4² = 512 wiring choices before specifying any bare variables.

For each choice of wiring and each of the eight choices of sides, trace the chosen output gates back to the reached sides. The trace depends only on the wiring. For a particular vertex, assign its membership in each of the six bare-variable sets freely. Its profile before restriction to S consists of precisely the choices that reach none of the sides containing that vertex. Starting with all eight choices, intersect with the complement of each such side's reachability mask to get all possible profiles. Project each resulting family onto each nonempty S and discard the empty profile. This includes every actual vertex profile by the preceding construction.

Families contained in other families on the same coordinates can be discarded: every subfamily of the smaller family is also a subfamily of the larger. Permuting the chosen coordinates preserves all intersections. The checker uses only these inclusions and actual permutations when reducing the list. The 512 wirings give 36 distinct unprojected families. After projection and reduction there are 44 families, the largest with 27 distinct nonempty profiles.

## The finite check

For each family, make a graph with one vertex per profile and edges joining disjoint profiles. Two kinds of vertex sets are forbidden in the selected subfamily:

- The four vertices of any four-cycle, including a cycle with chords.
- A triple of pairwise intersecting profiles with empty triple intersection.

Start with the entire family. If its graph has a cover of size at most three, every subfamily inherits such a cover by intersecting the cover with that subfamily. To check a cover budget, choose an edge and recursively include one of its two endpoints, decreasing the budget by one. If no cover is found, choose a forbidden set still present. Every admissible subfamily must omit at least one member, so recurse after deleting each member in turn. A node with no forbidden set and no three-cover would be a counterexample.

All 44 searches terminated without such a node, visiting 458,027 distinct active subfamilies in total for the published ordering. A second check encoded a counterexample on each nontrivial family as a SAT query. For every triple of vertices it demanded a selected edge avoiding that triple, and independently forbade every four-cycle and incompatible triple. All queries were UNSAT with CaDiCaL's internal proof check enabled. Thus every allowable representative graph has a three-cover. Lifting the cover proves the stated implication and its contrapositive for vertex cover number at least four. This is a computational proof of the assigned statement; the upstream submission requires its formalization in Lean.
