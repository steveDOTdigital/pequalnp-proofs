# Petersen with a prescribed nonedge AND and an output NOT

L-meta-1916 supplies the signal `x4 AND x6` for free to a list of at most thirteen fan-in-two gates and applies one final NOT. In the original gate count the supplied AND and the final NOT both cost one. A counterexample to this step exists **if and only if the nine-input Petersen edge function has a monotone circuit with at most twelve binary gates**. The equivalence is a written argument. [Lean checks](PetersenFinalNot.lean) its two semantic steps.

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

These leave a twelve-gate monotone synthesis question. The graph has twelve minimal true rows and twelve maximal false rows; together they characterize any monotone candidate. A sixteen-gate control computes the full table. The controls and lower bounds alone do not settle the twelve-gate question.
