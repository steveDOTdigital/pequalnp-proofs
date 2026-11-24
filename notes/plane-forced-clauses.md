# Forced clauses for projective-plane incidence

Independent work for L-meta-2870 by steveDOTdigital. Write $N=q^2+q+1$. The circuit must accept every incident point-line pair and reject every incidence-free assignment with at most $q$ active lines. Gate operands are binary and read earlier wires. The general $Nq/100$ size bound remains open.

## The exact minimum number of clauses

For a set $T$ of at most $q$ lines, let $U(T)$ be their point union. Activate just those lines and all points outside that union. This assignment is required to be false. Every positive clause in a conjunctive normal form (CNF) for the circuit must hit every incident pair, since that pair is a required positive input. A clause falsified on this assignment can contain only points of $U(T)$ and lines outside $T$.

Every point of $U(T)$ is forced into that clause. Choose a selected line containing the point and apply the clause to their incident pair. Every line outside $T$ is forced into it as well. Such a line has $q+1$ points and shares at most one with each selected line, so at least one of its points lies outside $U(T)$. Its incident pair forces the line literal. The unique possible falsified clause is therefore

    M(T) = U(T) on the point side, together with every line outside T.

Distinct sets $T$ give distinct clauses. Consequently every positive CNF for every monotone completion contains at least the sum of the binomial coefficients $\binom{N}{j}$ for $0≤j≤q$. The conjunction of these clauses attains the bound. An incidence hits every clause. An incidence-free input with selected line set $T$ of size at most $q$ misses $M(T)$. An input with more than $q$ lines hits every clause using a line literal. This gives the exact minimum over allowed completions. The [Lean proof](PlaneClauseGeometry.lean) checks the geometric classification and the injection of the small line sets into the output family.

## Separate lower bounds for AND and OR gates

**At least $2q^2+1$ OR gates.** Every point lies on $q+1$ lines. Indeed, the lines through a point partition the other $N-1$ points into blocks of $q$. Select $q$ of the lines through one point. Their union has $1+q^2$ points. The forced clause then contains $1+q^2+N-q=2q^2+2$ variables. On the corresponding false input, changing any one of those zeros to one turns the circuit true. For a point this creates an incidence with a selected line. For a line there is an active point outside the selected union incident with it. These conclusions use monotonicity even if the new row has $q+1$ active lines.

Trace a certificate of falsity backwards from the output. At a false AND choose one false operand, making the same choice every time that gate is reached. At a false OR keep both operands. Fixing the reached raw zeros to zero suffices for falsity, by induction on the gates. Every individually pivotal zero must therefore be reached. In the connected trace with $a$ one-operand ANDs, $b$ two-operand ORs, and $r$ distinct raw leaves there are $a+2b$ operand edges and $a+b+r$ vertices. Connectedness gives $b≥r-1$, including shared wires. This counts OR gates that are simultaneously false on one specified input.

**At least $\lceil N/2\rceil$ AND gates.** For each operand of each AND, trace back through OR gates only. The operand is the OR of its directly reached raw variables and previously computed AND outputs. The final output's analogous disjunction contains no raw variable, because every singleton input must be false. Hold a line $ℓ$ true, all other lines false, and exactly the points outside $ℓ$ true. Adding any point $p$ on $ℓ$ forces acceptance. At the first AND whose value changes, one operand changes from false to true while all earlier ANDs keep their values. Its directly reached raw point set contains $p$ and is contained in $ℓ$.

There are $N(q+1)$ incident flags to witness this way. A singleton raw point set can witness at most the $q+1$ flags through that point. A raw point set with two or more members can lie in at most one line, and on that line covers at most $q+1$ flags. The empty set covers none. Since there are two operand positions per AND, twice the number of ANDs is at least $N$.

Together the bounds give $2s≥4q^2+2+N$ for circuit size $s$. For $q≤249$, subtracting $Nq$ from $50(4q^2+2+N)$ gives $(249-q)q^2+49q+150≥0$. This proves the assigned inequality through order 249, including the prime-power orders 211, 223, 227, 229, 233, 239, 241 and 243. The [earlier upstream reduction](https://github.com/brilliant-hq/pequalnp-proofs/pull/5313) uses a different total-size argument for small orders. The gate-type bounds here hold at all orders. Their circuit arguments above are written proofs.

## What remains to be proved in Lean

Give each raw input a register containing one singleton clause. An AND takes the union of two families of clauses. An OR forms every union of a clause from its first family with one from its second. The identity for OR follows by choosing a false clause from each failed side. One register per gate suffices, even with unrestricted fanout. The resource being bounded is the number of register operations. Lean proves the gate recurrence and verifies each register against its wire on every input of the declared length. [Lean compiler](PlaneClauseCompiler.lean)

For orders at least 250 the remaining problem is a finite-set circuit bound. Every output clause must hit every flag, and every $M(T)$ for $|T|≤q$ must occur. The assigned nonempty marked-AND hypothesis supplies a union gate for which both operand families can change truth when the same shore of the input changes. The two operands may have different witnesses. In any counterexample of size less than $Nq/100$, the upper bound on the number of marked gates holds automatically because it is at most the total number of gates. The number of output clauses alone does not establish the large-order operation bound.

For comparison, ordinary CNFs require at least one distinct clause terminal for every $M(T)$. In a shared circuit, choosing a predecessor at each AND turns the output into a disjunction of raw inputs that dominates the circuit. For any canonical negative input, choosing a false predecessor wherever the AND is false preserves that row throughout the circuit. The resulting output disjunction is exactly $M(T)$, by the classification above. Thus a circuit with $a$ AND gates also satisfies $2^a ≥ \sum_{j=0}^q \binom{N}{j}$. This reasoning uses coherent choices at shared gates.

The finite control found 29 forced clauses for the Fano plane, checked their conjunction on all 16,384 assignments, and found 378 forced clauses for order three. It flipped each zero on every canonical negative in both planes. It also verified the lower bound on the number of simultaneously false OR gates in the usual circuit that builds a star for each line. The largest forced clauses contain 10 and 20 literals respectively. [Reproducible checks](plane-forced-clauses.py)
