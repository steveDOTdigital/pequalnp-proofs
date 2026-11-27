# Ten gates when the NOT reaches the output

For the graph of L-meta-32384, a fan-in-two AND/OR circuit with a single NOT on a path to the output needs at least ten gates.

## The nine-gate case

Cut the input edge of the NOT and treat its output as a separate variable `z`. The resulting output is monotone in the eight raw bits and in `z`. The original NOT signal can only fall when a raw bit rises. Every graph vertex is incident to an edge. For each raw bit there is consequently a rise of the original output when only that bit is raised. This rise persists with `z` fixed to the value it had before the change. Thus each of the eight raw bits is an essential input of the cut circuit. The stipulated output path from the NOT also places `z` in its dependency cone. [Lean positive-dependence lemma](GraphPositivePaths32384.lean)

There are therefore nine input leaves in the output cone. Each of its non-root wires must be read at least once. With `b` gates there are at most `2b` reads and at least `b+9-1` non-root wires, so `b≥8`. A circuit of at most nine gates, counting the NOT, leaves exactly eight gates in this cone. Equality forces exactly one read of each non-root wire, and two distinct valid inputs at every gate. The cut circuit is a read-once positive formula in the raw inputs and `z`.

If the NOT read the constant false, substitute the resulting constant for `z` and simplify. Otherwise its operand is a raw input or an earlier gate. Every non-NOT gate is already in the cut formula, so that operand appears there as a leaf or subtree `w`. It precedes the NOT and its subtree excludes `z`. Collapse `w` to a single variable `u`. The remaining formula is read-once in `u,z` and the other inputs. Its substitution `z = ¬u` is monotone in `u` for every choice of the other inputs. This follows by changing all leaves of the positive subtree `w` from zero to one.

At the first gate joining the branches containing `u` and `z`, write the operands as `A(u)` and `B(z)`. Their other variables are disjoint. The outer context can be made neutral by setting the disjoint sibling subtrees on its path to zero at ORs and one at ANDs. The same construction inside the second branch makes `B(z)=z` at a fixed choice of its other variables. This transfers the global monotonicity inequality to the first joining gate for every choice of its branch variables.

If the gate is an AND, monotonicity at the pivotal setting of `B` forces `A(0)=0` for all settings of the first branch. In this case setting `z=0` preserves the value at the joining gate for both values of `u`. If the gate is an OR, the analogous monotonicity argument forces `A(1)=1`, and setting `z=1` preserves the value. The checked lemmas give the pointwise equality in each case, so the replacement remains valid when the outer context is no longer set to neutral. Restore `w` and simplify the constant. The result is a read-once monotone formula on the original inputs. [Lean joining-gate lemmas](https://github.com/steveDOTdigital/pequalnp-proofs/blob/8eca42991130f9a5187fd12266a759d3e2e79d29/notes/GraphReadOnceSigns32384.lean)

## The induced path

Vertices `3,0,4,6` induce the path `3–0–4–6`. Fix all other vertices to zero. A read-once positive formula would remain read-once after this restriction, since constants can be propagated without introducing repeated leaves.

For the four-vertex path the minimal true inputs are precisely its three edges. An OR at the root would need to place both endpoints of every edge in one of the two disjoint branches. Otherwise the accepting branch would also accept an input with at most one vertex. Connectivity forces all vertices into one branch. An AND at the root would need to split every edge across the two branches, since each branch rejects its all-zero input. This forces the alternating bipartition of the path. Every vertex must then be accepted on its branch by itself, so the two endpoints of the path would be accepted together. Those endpoints form a nonedge.

The four-variable truth-table replay independently enumerated all 52 distinct read-once monotone functions using every variable. The path truth table was absent. The obstruction excludes nine gates for a circuit whose NOT is used on an output path. It leaves the ten- through fourteen-gate cases open.

## The output cone after the cut needs nine gates

The same obstruction applies when the NOT reads an arbitrary monotone circuit outside the cut output cone. Suppose the cut cone is read-once with the NOT's output as the separate input `z`. The unique path from `z` to the output has disjoint sibling subtrees. On any input the output equals `z` exactly when every sibling is neutral for its gate. A sibling is neutral at one for AND and at zero for OR. If any sibling is off its neutral value, the output is independent of `z`.

Call an assignment pivotal when all its siblings are neutral. Choose an anchor assignment by setting every AND sibling block entirely to one and every OR sibling block entirely to zero. It is pivotal. For any pivotal assignment, set its AND blocks entirely to one and leave its OR blocks unchanged. The resulting assignment is pivotal and above both the original assignment and the anchor in the Boolean product order. On these pivotal rows the actual output is the NOT signal, which is antitone in the raw input. The output is monotone, so its values agree along both comparisons. The sign is therefore constant on all pivotal assignments. Setting `z` to that constant preserves the function everywhere. The Lean lemma checks this order argument independently of the circuit representation. [Lean pivotal-set lemma](https://github.com/steveDOTdigital/pequalnp-proofs/blob/d433ff5457bee0ca470592bdeb378d40f37b57be/notes/GraphPivot32384.lean)

The resulting read-once monotone formula would compute the graph, contradicting the induced path. Thus a circuit with a live NOT must use at least nine AND/OR gates in its cut output cone. In a circuit of total size at most fourteen, at most four other gates can lie outside that cone, apart from the NOT itself.

As a finite control, I combined every one of the 472 read-once functions of four raw inputs and one sign input with the negation of every one of the 168 monotone functions of the four raw inputs. All 43,490 monotone composites, out of 79,296 combinations, agreed with one of the two constant-sign substitutions.
