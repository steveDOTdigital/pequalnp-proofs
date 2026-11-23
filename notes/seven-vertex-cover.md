# Exact gate counts through seven nonisolated vertices

For every nonempty graph with at most seven nonisolated vertices and no four-cycle, the minimum size of a monotone binary circuit for its edge function is **the number of edges plus the minimum vertex-cover size minus one**. The seven-vertex extension covers 73 isomorphism classes, representing 117,414 labeled graphs without isolates. Together with the previous 43 classes this gives 116 classes. This is a finite result for L-meta-612. [Previous six-vertex search](check-small-cover-bound.py)

## Two smaller functions at each vertex

Write B for the proposed minimum. Pinning a nonisolated vertex false gives the edge function of its deletion. Pinning it true gives an OR of its neighbors' raw inputs and the edge function on the remaining vertices outside its closed neighborhood. When that graph has an edge, each extra OR input adds exactly one to its minimum circuit size: pinning the extra inputs false successively removes a consuming gate each time. With no remaining edges the answer is just the number of OR inputs minus one, or zero for a constant. Thus the verified six-vertex results give the exact minimum of both restrictions. At least one gate disappears in any pinning of an essential vertex. This proves the desired bound directly for 52 of the seven-vertex classes.

For the remaining 21 classes, test each possible minimum gate count from one plus the largest one-vertex restriction bound through B − 1. In a normalized minimum circuit, each gate has two distinct inputs, every gate reaches the output, and independent gates may be scheduled in order of larger operand index then smaller operand index. The earliest gate can be chosen from one representative of each raw-pair orbit under graph automorphisms: minimize the first operand pair in that order over relabelings and legal schedules. All circuits of a given size are tested up to these reductions; no timeouts occurred in the complete prefix run.

## Why a prefix can be discarded

The minimal true inputs are the individual edges. The maximal false inputs are the maximal independent sets. Monotonicity makes those two sets sufficient to check the whole function. Say that a wire h dominates g on such a boundary if h is at least g on every positive row and at most g on every negative row. In a minimum circuit no gate can be dominated by an earlier wire or by a constant: substituting the earlier value preserves each boundary answer by monotonicity of the remaining circuit.

This rule works simultaneously on a **restricted** boundary. Process gates in their original order. Replace each originally dominated gate by the current representative of its chosen earlier wire or constant. At every step the resulting wire dominates its original value on the restricted boundary, by transitivity for a substitution and monotonicity for a retained gate. After eliminating constants and copies this gives a circuit with at most one gate per undominated original gate. For each pinning we may therefore discard a prefix once its dominated gates leave fewer than the known minimum.

There are two additional counts. If a vertex flip changes the output for some pair of assignments while leaving every computed prefix signal fixed, the suffix must still read that raw vertex. Pinning it then removes at least one *further* gate beyond those removed in the prefix. Also, each unused prefix gate and each such indispensable raw input must reach the output through the suffix. Connecting k distinct sources to one output requires at least k − 1 binary gates.

For the first raw gate, an AND of a nonedge accepts no positive boundary row and is dominated by false. For either gate type, fix one operand to its controlling value. If the output can still depend on the other raw operand, that other operand must have a second reader. Pinning that other operand removes both readers; if its value controls the first gate, a consumer of the first gate also simplifies. This consumer is distinct from the second reader: a gate directly combining x with AND(x,y) or OR(x,y) equals one of its inputs and would have been removed. The first gate cannot itself be the output for any of these seven-variable functions.

The C++ enumerator evaluates each gate on all 128 assignments using unsigned 128-bit arithmetic. It found no smaller circuit. At the proposed minimum, the driver constructs a circuit by assigning every edge to one endpoint in a minimum cover, forming its star and ORing the stars. Each of the 73 explicit circuits passed the same pruning rules and was independently evaluated gate-by-gate on all 128 inputs. An independent labeled enumeration, adding an edge only when doing so closes no three-edge path into a four-cycle, agreed with the orbit total of 117,414.

## Reproduction

From the repository root, run the following with Python 3 and a C++17 compiler supporting unsigned 128-bit integers. The driver compiles in a temporary directory and removes the executable on exit. Each budget prints UNSAT or an explicit witness. UNKNOWN means an incomplete search.

```sh
python3 -B notes/check-seven-vertex-bound.py --prefix --seconds 120
python3 -B notes/check-seven-vertex-bound.py --verify-upper
```

The same driver includes a separate SAT encoding, enabled by passing the path to CaDiCaL and omitting `--prefix`. Some SAT cases timed out; the exhaustive prefix search supplies the full seven-vertex exclusion. Isolated vertices of a larger graph can be fixed false and do not change its minimum. [Driver and restriction bounds](check-seven-vertex-bound.py) · [Prefix enumerator](seven-vertex-prefix.cpp)
