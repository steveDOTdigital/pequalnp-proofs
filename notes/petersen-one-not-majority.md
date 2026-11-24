# A majority restriction for a circuit with one NOT

L-meta-2768 asks whether a 15-gate circuit with first gate OR(0,3) and exactly one
NOT can compute the nine-input Petersen edge function. The following restriction
applies to every monotone target computed with one NOT. It gives a necessary test
on the gates after the inversion. The 15-gate Petersen question remains open.

## Cutting the circuit at its NOT gate

Write H(x) for the input to the NOT. Let K(x,t) be the output when the NOT's output
is independently set to t. The prefix computing H is monotone. The suffix K is
monotone in both x and t, including where it reads a shared prefix wire directly.
The original output is F(x)=K(x,¬H(x)).

[The Lean splitting proof](PetersenOneNotSplit.lean) implements this cut for the
project evaluator and its default-false wire reads. After supplying the first
OR as an additional input, the monotone prefix and suffix have a total of 13
gates. The proof preserves every prefix wire as an input to the suffix. It uses
the existing [wire monotonicity lemmas](PetersenFinalNot.lean).

If either choice of a constant t produces F on every raw input, the search
can use that monotone specialization. Otherwise there is an input e witnessing
failure with t=0 and an input i witnessing failure with t=1. Monotonicity in t
gives K(x,0) ≤ F(x) ≤ K(x,1) for every x. Hence at e the target is true and K(e,0)
is false. At i the target is false and K(i,1) is true.

## Eight forced evaluations

At both middle rows e and i, K passes the independent bit t through unchanged.
The inversion is what distinguishes their outputs: H(e)=0 and H(i)=1.
Let the bottom row be the intersection of the true inputs of e and i, and the top
row their union. By monotonicity of F and H, both are false at the bottom and
both are true at the top. The computed identity gives K(bottom,1)=0 and K(top,0)=1,
forcing K(bottom,t)=0 and K(top,t)=1 for either bit t.

Choose rising block variables a and b that select the raw assignment as follows.

| a | b | Raw assignment | H | K with t=0 | K with t=1 |
|---|---|---|---|---|---|
| 0 | 0 | intersection | 0 | 0 | 0 |
| 1 | 0 | e | 0 | 0 | 1 |
| 0 | 1 | i | 1 | 0 | 1 |
| 1 | 1 | union | 1 | 1 | 1 |

Thus H becomes b, and K must compute the majority of a, b and t. [Lean verifies
this implication](PetersenOneNotDiamond.lean) for every finite input width.

One may choose e to be a minimal true row: shrink a failing positive as long as
it stays positive, and K(e,0) remains zero. Likewise i may be a maximal false row,
since enlarging it while it stays negative leaves K(i,1) true. For the nine-vertex
target there are 12 edges and 12 maximal independent sets, giving just 144 potential
pairs. There are 42 pairs with H(e)=0 and H(i)=1 if H is the prescribed first OR.

On these four raw rows every signal from a monotone prefix is one of 0, 1, a,
b, a∧b, a∨b. Even allowing both individual block variables and both constants
for free, the suffix needs four gates if neither mixed signal is available,
three if exactly one is available, and two if both are available. The formula
(a∧b)∨((a∨b)∧t) attains all three bounds, counting any missing mixed signals.
[The eight-row verifier](petersen-majority-restrictions.py) independently
enumerates all smaller AND/OR circuits, allowing arbitrary reuse. The free first
OR provides the union signal on 18 of the 144 pairs.

## What was checked for Petersen

The [independent one-NOT synthesis search](petersen-one-not-first-03.py) first
replayed a 17-gate control with the prescribed first OR and exactly one unused
NOT on all 512 inputs. It tested the 15-gate budget with 39 initial rows and
a 240-second limit. The run timed out. The control uses a five-vertex cover and
does not establish optimality. The [restriction verifier](petersen-majority-restrictions.py)
also checks every assignment for each fixed raw or first-OR NOT argument.
For the first-OR argument, 16 minimal positive and 12 maximal negative tests
suffice because the circuit is monotone within each level of that OR.

Under 00 on inputs 0 and 3, the target is the six-cycle on 1,2,7,5,8,6.
Under 10 and 01 it is the OR of three individual inputs and two disjoint edge
terms. Under 11 it is the OR of five individual inputs. The verifier replays all
four formulas on the full 512-row table. These experiments and the majority
condition leave two open lower bounds: the specialization with a constant NOT
output and the case in which the suffix realizes the displayed majority table.
