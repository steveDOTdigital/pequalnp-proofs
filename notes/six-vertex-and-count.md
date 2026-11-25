# Six vertices do not separate partial AND count from biclique cover number

L-meta-949 asks for a graph on six vertices and a well-formed circuit using fewer AND gates than the graph's biclique cover number. The circuit must reject every maximal independent set and accept each enlargement of such a set by one vertex. An independent finite search found **no such graph**. Across all 156 isomorphism types the minimum partial AND count equals the biclique cover number.

| Common minimum | Unlabeled graphs | Smaller-size test |
| ---: | ---: | --- |
| 0 | 1 | Empty graph |
| 1 | 9 | 0 gates excluded |
| 2 | 61 | 1 gate excluded |
| 3 | 80 | 2 gates excluded |
| 4 | 5 | 3 gates excluded |

A separate [Lean check of the exact negation](SixVertexAndCount.lean) uses the project's previously accepted [L-meta-950](https://github.com/open-goat/pequalnp-proofs/pull/1995). That theorem and its upstream credit belong to its original contributor. The enumeration here was performed independently before locating the accepted twin.

## Counting and checking the circuits

The [graph and cover program](six-vertex-and-count.py) uses a 15-bit adjacency mask in lexicographic order on the unordered pairs. It partitions all 32,768 labeled graphs under all 720 vertex permutations. On each representative, it enumerates disjoint nonempty shores of every biclique. Empty shores cannot cover an edge, and intersecting shores would require a loop. A dynamic program chooses a still-uncovered edge, tries each biclique covering it and recurses on the remaining edges. The optimum gives both the cover number and an explicit cover. Applying the same recurrence to the positive boundary rows also gives the same optimum for circuits that simply OR together independent biclique gates.

The [circuit synthesis program](six-vertex-and-synthesis.py) checks arbitrary sharing. For gate $j$, each side has one Boolean selector per raw vertex and per gate earlier than $j$. On each tested input, a side is the OR of its selected true sources and the gate is the AND of the two sides. Output selectors can read any gates. An output raw vertex would cause acceptance of a maximal independent set containing that vertex, so none is allowed in a correct circuit. The two sides may overlap or be empty. Gates and reads may be unused. In particular a smaller witness could be padded with unused gates to the tested size.

The negative rows are every maximal independent set. The positive rows are their distinct one-vertex extensions. The program encodes these evaluations by equivalences and calls CaDiCaL with internal proof checking. For every nonempty graph the instance one gate below the cover count was unsatisfiable. A second run for every graph fixes the selectors to a minimum biclique cover. All 156 resulting instances were satisfiable, and the independent decoder checked those circuits on all 64 input sets against the full edge function.

## Reproduction

From the proof repository, run `python3 -B notes/six-vertex-and-count.py` and `python3 -B notes/six-vertex-and-synthesis.py`. The second program uses the CaDiCaL bundled with the project's Lean toolchain. Its final counts are 155 unsatisfiable instances below the cover number, one empty graph, and 156 verified positive controls. A timeout does not establish a lower bound.
