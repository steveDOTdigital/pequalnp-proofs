# Six-label inequality on one-hot pairs

The 6-by-6 matrix in case L-meta-9304 has one missing entry in each row and column. Relabeling the right vertex `j` as `(j+1) mod 6` makes the missing entries the diagonal. Our exhaustive calculation gives an optimum of **19 fan-in-two AND/OR gates**. Lean independently checks the 19-gate upper bound against the posted mask. The exhaustive lower bound below is a C++ result awaiting a Lean certificate.

## Construction

Pair each row input with its matched column input using OR. The six resulting bits name the labels present. A positive pair has two different labels and a diagonal pair has one. On a binary tree of labels, compute whether a subtree contains any label and whether it contains two. At a join, two labels occur when either subtree already has two or both subtrees have one. Omit the final root presence bit. For six labels this uses six initial OR gates and thirteen gates in the tree. [Lean construction and verification of all 36 entries](CrownPromise.lean)

## Exhaustive calculation

Compile the [standalone verifier](crown-promise-search.cpp) with a C++17 compiler. Run the smaller orders first because the later searches reuse their lower bounds. The arguments are the number of labels, the gate budget, and a time limit in seconds. A time or state limit produces `LIMIT` and a nonzero exit status.

```sh
c++ -O3 -std=c++17 notes/crown-promise-search.cpp -o /tmp/crown-promise-search
/tmp/crown-promise-search 2 2 60
/tmp/crown-promise-search 3 6 60
/tmp/crown-promise-search 4 10 60
/tmp/crown-promise-search 5 14 120
/tmp/crown-promise-search 6 17 120
/tmp/crown-promise-search 6 18 600
/tmp/crown-promise-search 6 18 1200 baseline
```

| Labels | Gates excluded | Distinct states expanded | Visits |
| ---: | ---: | ---: | ---: |
| 2 | 2 | 0 | 1 |
| 3 | 6 | 4 | 151 |
| 4 | 10 | 36 | 2,909 |
| 5 | 14 | 656 | 102,510 |
| 6 | 17 | 7 | 1,702 |
| 6 | 18 | 48,022 | 11,227,927 |

The baseline calculation also excludes 18. It expands 243,873 states in 29,745,017 visits with the rectangle cut, antichain cut, and dominance by retired intermediate wires disabled. Both modes share the cofactor lower bounds.

### Live wires and dominance

Represent each wire by the subset of the promised pairs where it is true. In a smallest circuit remove unused gates, propagate constants, and bypass unary gates and repeated operands. An out-of-range reference has the value false and obeys the same simplifications. Every raw wire must be read. For example, the positive pair `(i,j)` and negative pair `(j,j)` force a positively distinguishing dependence on the left raw wire `i`. The column argument is symmetric.

The live pool consists of the wires still needed after a prefix. It initially contains all raw wires. A gate takes two different members of the pool. For each operand, the search allows both possibilities for whether it has another reader. With `k` gates remaining, at most `k+1` live wires can be joined into one output. For each positive and diagonal-negative pair, at least one live wire must be true at the positive and false at the negative. Otherwise monotonicity precludes the correct output.

Say that wire A dominates B if it contains all B's positive hits and none of B's additional negative hits. Substituting A for B anywhere downstream preserves the desired final value on both classes. A new gate dominated by an earlier wire can be omitted. A signal false on all positives or true on all negatives can similarly be replaced by a constant and simplified away. In the faster run, choose a smallest circuit that minimizes the sum of wire-to-reader distances. If a newer wire dominates an older one, no subsequent gate needs to read that older wire. Substitution would either shorten the circuit or decrease the sum of distances. Consequently two such wires cannot both remain live. Simultaneous relabeling and transposition preserve the target. The program compares the full transformed pools for equality when sharing results across prefixes.

### Restrictions to smaller crowns

Keep a set of left labels and a set of right labels. Suppose they have `m` labels in common and `e` labels appear on only one side. The retained rectangle has a lower bound of the smaller crown's cost plus `e`. Each of the extra raw wires is essential by comparing its positive pair with the diagonal of a shared label. Pin the extras low to obtain the smaller crown. Each such raw wire saves at least one gate.

More generally, charging a fixed raw wire once for every direct use remains sound. Give its uses separate constant occurrences. During propagation a binary gate consumes at most two pending constants. If it consumes two, it produces a constant and its cone has at least one later reader. If it consumes one, eliminating the gate costs at most one copy or constant substitution. The nonconstant output leaves no pending constant. Thus at least one gate per initial pending constant occurrence disappears. The calculation uses the known direct uses in the prefix and one future use for each still-live, deleted raw wire.

There is also a bound that depends on the actual projected prefix. Compute each prefix wire on the restricted rectangle. Duplicate projected values can use an earlier implementation. A live wire may be replaced by any dominating projected value, including a raw wire, or by a suitable constant. The recorded prefix dependencies give a concrete upper bound `P` on the gates needed for the chosen replacements. If `c` live wires become constants and `k` gates remain, the restricted computation costs at most `P+k-c`. The restricted output is nonconstant, so constant propagation uses the same counting argument. A value below the smaller lower bound rules out every continuation of that live state. The choice of replacements is greedy. Any choice giving a valid cheaper implementation suffices.

### Tree suffixes

If the number of live wires is exactly one greater than the remaining gate count, the suffix has to be a binary formula using each live wire once. Its monotone communication protocol partitions pairs of positive and negative inputs into disjoint leaf rectangles. At an OR gate the positive player chooses a true child, and at an AND gate the negative player chooses a false child. A leaf must distinguish the pair. If exactly one live wire can distinguish a given pair, that wire's single rectangle must contain both its positive row and its negative column. Forced rectangles for different wires cannot overlap. This cuts down the search at six labels and is unnecessary for the independent baseline run.
