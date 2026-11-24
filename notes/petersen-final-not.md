# Petersen with a prescribed nonedge AND and an output NOT

L-meta-1916 supplies the signal `x4 AND x6` for free to a list of at most thirteen fan-in-two gates and applies one final NOT. In the original gate count the supplied AND and the final NOT both cost one. A counterexample to this step exists **if and only if the nine-input Petersen edge function has a monotone circuit with at most twelve binary gates**. The equivalence is a written argument. [Lean checks](PetersenFinalNot.lean) the normalization of a single internal NOT for the actual gate-list evaluator. The finite exclusions below rule out the twelve-gate monotone circuit.

## Counting the NOTs

The unrestricted [gate-elimination calculation](petersen-gate-elimination.py) gives at least twelve binary gates for the graph even with free negations. Setting input 4 to zero leaves a function requiring at least ten. To reproduce the latter number, import the script with `runpy.run_path`, form the 512-row tuple of its target, and call `lower(restrict(full, 4, 0))`.

Starting with `x4 AND x6` raises the binary-gate lower bound to thirteen. Otherwise the circuit would be globally minimal at twelve binary gates. With input 6 set to zero and only input 0 selected among the other seven inputs, toggling input 4 changes the answer. Input 4 must be read again outside the prescribed AND. Fixing 4 to zero removes the first gate, a consumer of its constant result, and another reader of input 4. Global minimality permits counting all three separately, as proved in the elimination calculation. This would leave at most nine binary gates for a function requiring ten. This reasoning allows arbitrary complemented wires, so dead gates, short operand lists, constants and out-of-range reads in the desk model do not weaken the bound.

Consequently a fifteen-gate counterexample has at most two NOTs. The wire read by the final NOT must be true at the empty selection and false at the full selection, so that wire computes a nonmonotone function. An empty operand list gives a constant final result. With a nonempty list, Lean's NOT reads the head and ignores any other operand. At least one earlier NOT feeds the selected result, and there is room for exactly one earlier NOT.

## What the single internal NOT must read

Let F be the graph function and G the signal read by the unique earlier NOT. Cutting that NOT's output leaves a monotone function K of the original inputs and a free bit. An out-of-range or ignored operand is a constant under this evaluator. The prescribed first AND is monotone, so monotonicity also holds in the original nine inputs. The selected pre-output wire satisfies K(x,¬G(x)) = ¬F(x).

If F(x)=0 and G(x)=1, then K(x,0)=1. Increasing x to the full selection and the free bit to its value there would force K to remain true, contradicting F(full)=1. If F(x)=1 and G(x)=0, the empty selection, where K is true, can be increased to (x,1), contradicting K(x,1)=0. Hence G=F on every row. The gates before the internal NOT already compute F monotonically, using the free first AND and at most twelve additional binary gates.

Inputs 4 and 6 do not form an edge. On every minimal true row, consisting of the two endpoints of an edge, the free AND is false. Set its output permanently to false. All minimal true rows still compute true, so monotonicity preserves every positive row. The change only decreases values on negative rows, which were already false. Fold away the constant. A monotone circuit of at most twelve binary gates remains.

Conversely, take any twelve-gate monotone circuit for F. Leave the supplied first AND unused, shift references to ordinary gates up one position, complement the output once in the prefix and again at the final gate. This obeys the desk's wire-number and list-length bounds. This direction needs no optimality assumption.

## Restricting a search for twelve monotone gates

At twelve binary gates an unrestricted monotone candidate is globally minimal. For every vertex v, setting v to zero leaves a function requiring at least ten binary gates by the same elimination calculation. Thus v has at most two readers. If it has two, both must be OR gates: setting v to zero would otherwise remove both readers and a consumer of a vanishing AND. Such a consumer cannot be the other reader because absorption would simplify the circuit.

For the degree-two vertices 4, 6 and 7, setting v to one leaves a function requiring at least nine binary gates. Two OR readers are impossible. They would both become true, and their consumers must include at least two further gates. If the readers feed one another, the second is redundant. If both feed only the same gate, factoring v out of their conjunction or disjunction replaces three gates by at most two. Neither reader can be the output because the restricted function is nonconstant. Four removals would leave at most eight gates, contradicting the nine-gate bound.

## A computer-assisted exclusion at twelve monotone gates

The degree-three vertices form the six-cycle 0, 1, 2, 3, 8, 5 in this order. Each degree-two vertex joins a pair of opposite cycle vertices. Rotations act transitively on each of the two degree classes. It suffices to examine deletion of 0 and deletion of 4.

| Induced graph | Binary-gate lower bound with free inversions | Monotone minima excluded by SAT | Resulting monotone lower bound |
| --- | --- | --- | --- |
| Delete 4 | 10 | 10 | 11 |
| Delete 0 and 4 | 8 | 8 and 9 | 10 |
| Delete 0 | 10 | By the preceding row | 11 |

In the third row, vertex 4 is still essential. Setting it to zero removes at least its first reader. A ten-gate or smaller circuit would leave at most nine gates for the seven-vertex graph in the second row.

Now take a smallest monotone circuit for the full graph. Fold constants and delete unary or redundant gates. Its first gate reads two different raw vertices, p and q. Set p to zero. For an AND, the first gate and one of its consumers disappear. For an OR, the gate becomes q and there must be another reader of p. Indeed, with q set to one, p remains essential. If p and q are adjacent, use the singleton q. Otherwise there is a neighbor of p which is not adjacent to q, because the graph has minimum degree two and no four-cycle. Select that neighbor together with q. In either case toggling p changes the answer while the first OR stays true. The second reader of p also simplifies away when p is zero. In all cases at least two binary gates disappear, leaving a graph that needs at least eleven. The full graph therefore needs at least **thirteen monotone binary gates**. By the equivalence above, L-meta-1916 has no counterexample.

### Finite checks and their completeness

Run the following commands from the proof repository's `lean` directory. The [encoder](check-petersen-monotone.py) uses the Python standard library and the CaDiCaL shipped with Lean. All three cases returned UNSAT with its internal proof checker enabled. The eight-input instance has 1,442 variables and 28,595 clauses. The two seven-input instances have 937 variables and 12,535 clauses, and 1,050 variables and 17,136 clauses, respectively.

```sh
python3 ../notes/check-petersen-monotone.py degree-two 10
python3 ../notes/check-petersen-monotone.py theta 8
python3 ../notes/check-petersen-monotone.py theta 9
```

The solver models a smallest circuit of the specified size, one ordered pair of earlier wires and an operation per gate. Every essential input and every nonfinal gate has a reader. Commutativity sorts the inputs of each gate. Gates can be topologically sorted by their larger input index, using the smaller index to break ties. At each step pick the least ready pair; any newly eligible pair contains the wire just produced. The output is last because every gate lies in its cone.

The two graphs have 10 and 8 minimal positive rows and 9 and 7 maximal negative rows, respectively. Monotonicity makes these rows sufficient. In a minimum circuit, every gate is true on at least one minimal positive and false on at least one maximal negative. Otherwise forcing a constant preserves the answer on the boundary and removes that gate. An OR needs both operand patterns 01 and 10 among the positives, since omitting a dominated operand preserves the positives and only decreases the negatives. Dually, an AND needs both patterns among the negatives.

For each vertex, the encoder also restricts its number of direct readers. If there are d readers and k of them are forced to a constant by fixing the vertex, at least d+min(k,2) gates disappear. All d readers simplify. A consumer of a forced reader cannot itself read the same vertex directly: by absorption it would be redundant. Each forced reader has a consumer, since every single-vertex restriction tested here is nonconstant. If two forced readers have only one consumer between them, that consumer reads both. Factoring their common raw literal replaces three gates by at most two, contradicting minimality. These observations account for the additional one or two eliminations. The allowed number is computed from the unrestricted lower bound for each individual restriction.

Positive controls for both graphs also passed with all of these constraints enabled, using star circuits of thirteen and eleven gates. The solver independently synthesized an eleven-gate seven-vertex circuit, whose decoded gates matched all 128 inputs. These are checked SAT results and a written circuit argument. Lean verifies the one-inversion normalization for the project's actual gate-list evaluator. The project is checking [the three-child Lean reduction](https://github.com/brilliant-hq/pequalnp-proofs/pull/4803). Its normalization child has a kernel proof. Formalizing the bounded lower bounds is a separate obligation.
