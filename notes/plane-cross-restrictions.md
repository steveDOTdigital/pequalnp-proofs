# Lower bounds from shared controls in projective-plane incidence circuits

L-meta-2008 asks for $100s\ge Nq$ for a monotone binary circuit with $s$ gates on the points and lines of a projective plane, where $q>100$, $d=q+1$ and $N=q^2+q+1$. It accepts the input consisting of each incident point and line (a flag). It rejects every incidence-free input with at most $q$ active lines. There are $E=Nd$ flags. Each point has degree $d$ because its incident lines partition the $N-1$ other points into classes of $q$. Distinct points have one common line, and distinct lines have at most one common point.

Call an AND marked if both of its operands semantically depend on points or both semantically depend on lines. Extra marks are allowed. A control is an original monotone Boolean signal. Suppose we can select $h$ controls such that at every marked AND, one operand is a function of the selected bits. Individual operands can be selected, a signal can serve many ANDs, and the functions need not be the same. Then the desk bound holds whenever $100h\le49q$, with arbitrary nesting and reuse. A different bound below permits arbitrarily many marked ANDs if their singleton supports are sufficiently dense. A one-sided argument allows arbitrary point-dependent ANDs when only a small number of ANDs combine two line-dependent operands. The full desk hypothesis permits marking every AND of a putative circuit with $100s<Nq$. That case is open here.

## Choosing one restriction for the whole circuit

Start with an empty set $U$ of inputs pinned high. As long as a control currently zero can become one by adding at most two vertices while keeping $U$ incidence-free, add such a witness. No control switches back to zero. At most $h$ additions suffice, so $|U|\le2h$. At termination every control has precisely its value at $U$ on every incidence-free extension by at most two vertices. This condition must be tested again after every addition: on three independent inputs, a triple conjunction initially has no two-element witness but can acquire one after another control fixes the first input.

Pin to zero all neighbors of $U$. Remove the pinned vertices, leaving a bipartite graph of available points and lines. A vertex in $U$ costs at most $d^2$ flags: every affected flag meets one of its $d$ neighbors. Thus at least $E-|U|d^2$ remain. Extra raw vertices pinned low in advance cost at most $d$ each. When $|U\cap L|+2\le q$, each incidence-free test on at most two remaining inputs, with $U$ high, is a desk negative. A surviving flag still makes the original circuit accept by monotonicity.

## Keeping the point and line projections separate

Before simplifying anything, use three copies of every original wire function $f$. Write $U=P_0\cup L_0$. On updated point and line sets $P\supseteq P_0$ and $L\supseteq L_0$, the copies have values
$$
 f(P,L),\qquad f(P,L_0),\qquad f(P_0,L).
$$
OR acts coordinatewise. Marked AND initially acts coordinatewise too. The operands of an unmarked AND are point-only and line-only, up to exchanging them. Indeed the failure of semantic dependence on a shore is equality at the two extremes for every choice on the other shore, hence independence by monotonicity. Each original wire is zero at the empty input and one at the full input, by induction using the strict binary gates. Thus neither operand can be independent of both shores; the definition of an unmarked gate forces the opposite pure roles.

Write the pure operands as $a,b$ in point, line order. In the full copy of an unmarked AND, take the point copy of $a$ and the line copy of $b$. In its point copy take the point copy of $a$ times the fixed bit $b(P_0,L_0)$. In its line copy use the fixed bit $a(P_0,L_0)$ times the line copy of $b$. These three instructions give exact values even when a base bit is one.

Now simplify every marked AND simultaneously in topological order. Its controlled operand has a fixed bit on the base and on every required small negative extension. Select its other operand when the bit is one and select the controlled operand itself when the bit is zero. Use the same choice on all three copies. On a small negative input its two projections are also incidence-free extensions by at most two vertices. Hence every copy agrees with the original on its required negative rows by induction. On every other input all copies can only increase, since an operand dominates an AND, all remaining operations are monotone, and fixed base scalars in the unmarked copies retain their original values. Every surviving positive is still accepted. This construction handles arbitrary reuse of a marked signal before another marked gate.

The point and line copies now consist only of raw disjunctions, scalars and copies. In the full circuit only the unmarked ANDs remain as binary products; each is fed from the two pure copies. Simplifying constants, the output is an OR of rectangles of point and line singletons, with no live linear term, since it rejects every singleton and the empty test. Each nonempty rectangle is inside the surviving incidence relation by the two-input negative tests. Consequently it is a star, as a $2\times2$ rectangle would give two distinct points on two common lines.

Assign each surviving flag to one of the stars containing it. Fix a center owning $m$ distinct neighbors across $t$ terminal products. The union of the raw OR cones feeding their neighbor inputs requires at least $m-t$ binary merges: project the cones onto the owned inputs, discard empty branches and contract copies or redundant merges. A binary DAG connecting $m$ raw inputs to at most $t$ roots needs at least $m-t$ internal nodes by its edge and component counts. Each charged merge originally has at least two literals on the neighbor shore and its support is entirely inside that center's neighborhood. Two such literals determine the center, so another center cannot charge that gate in that pure copy. Assign each one-edge star just one orientation. The $t$ products supply the remaining charges. Altogether the surviving flags use at most two pure copies of each original OR and one terminal per original AND. With $z$ additional raw vertices pinned low,
$$
 E \le 2s + zd + |U|d^2 .
$$
For $z=0$ and $100h\le49q$ we have $2h+2\le q$ and $2h d^2\le .98q d^2=.98(N-1)d$. The inequality implies $100s\ge Nq$. A particular restriction with fewer pins or fewer line pins may be used directly.

## When many marked gates have dense singleton supports

Assume for contradiction $100s<Nq$. For each actually marked gate suppose one operand accepts either at least $D=80d\ln d$ distinct singleton points or at least $D$ distinct singleton lines. There are fewer than $d^3$ such operands to satisfy. Draw $b=\lfloor q/8\rfloor$ lines independently with replacement, then draw $b$ points independently and uniformly from those off all drawn lines. The latter pool is nonempty since $bd<N$. The sampled vertices form an incidence-free set of at most $q/4$ pins.

For a line support of size $u\ge D$, the miss probability is at most $\exp(-bu/N)\le\exp(-u/(10d))$, since $b\ge q/9$ and $N\le (10/9)qd$ for $q>100$. For a point support $S$ of size $u$, write $X_j=|S\cap l_j|/d$. Each $X_j\in[0,1]$ has expectation $u/N$. By $2^x\le1+x$ on this interval and independence,
$$
 \Pr\left[\sum_j dX_j\ge u/2\right]
 \le \exp\left(bu/N-(\ln2)u/(2d)\right)\le \exp(-u/(5d)).
$$
Otherwise at least $u/2$ points of $S$ remain available, and the point samples miss them with probability at most $\exp(-u/(20d))$. A union bound gives total failure probability at most $3d^3d^{-4}<1$. On a successful draw every selected operand is genuinely pinned true on all extensions. The same gate count gives $E\le 2s+(q/4)d^2$ and yields the requested contradiction. The condition is useful at orders where the stated supports fit in a shore.

## Paying only for flags requiring both endpoints

At the empty base, let $S_g$ be the raw singleton inputs that make marked gate $g$ true. Replace its three copies by the raw OR of $S_g$ and its point and line projections, respectively. Monotonicity makes these lower bounds on all inputs. They are exact on singletons. Write
$$
 B_g=\{(p,l)\text{ incident}:g(\{p,l\})=1,\ g(\{p\})=g(\{l\})=0\}.
$$
Every flag outside $\bigcup_g B_g$ agrees with the original in all three copies by induction. The output can only decrease, so the negative rows remain correct. Full-copy raw ORs at marked replacements can only reach the output along OR or copy paths, because unmarked full products read exclusively the pure copies. Every nonempty such path would accept a singleton. Thus only the two projected ORs need to be included in the bound. If $b$ raw OR gates suffice to supply all these projections, the preceding charge gives
$$
 E\le 2s+b+\left|\bigcup_g B_g\right|.
$$
One may share their OR gates arbitrarily; a crude price is the sum of $(|S_g\cap P|-1)_++(|S_g\cap L|-1)_+$ over the marks. Hence a union plus preparation price of at most $98s$ proves the claim. Replacing the marked gates by zero instead gives $E\le2s+|\bigcup_g\{e:g(e)=1\}|$ without any preparation.

## A shared control that cannot be removed by simple absorption

Let $W$ be the OR of the points on one line $l_0$. For every other line $l$, let $A_l$ be the OR of its points and $B_l$ the OR of those outside $l_0$. Use the star $l\wedge((W\wedge A_l)\vee B_l)$, together with the ordinary star at $l_0$, and OR the stars. The inner disjunction equals $A_l$ on every assignment: the unique point of $l\cap l_0$ forces $W$, and each other point of $l$ forces $B_l$. Neither operand of $W\wedge A_l$ implies the other. All $N-1$ marked gates lie on output paths and share $W$. One pinned point on $l_0$ suffices, leaving exactly $Nd-d^2$ flags. Each marked gate accepts at least $d$ flags from its common point alone, whose support is already a single raw literal. The [executable example](plane-cross-restrictions.py) checks the negative promise on the Fano plane and the transformed circuit on every surviving test of weight at most two at orders two and three.

## Counting flags with one occurrence of their line input

This argument uses the stronger desk tests with one active line and arbitrarily many points. Expand a successful evaluation into a proof tree by taking one true child at each OR and both children at every AND. A flag is counted if it has some successful proof in which its line input occurs just once. Its point may occur arbitrarily many times. Let $H$ be the number of such flags. Then
$$
 H+N\le 4s+1.
$$
In particular the desk conclusion holds if at most $96s$ flags lack such a proof. This bound imposes no condition on circuits evaluated at nonflags beyond the original negative promise.

For each wire $w$ let $a_w(P)$ be its value at point set $P$ with no lines. Build the whole baseline circuit once, in at most $s$ gates. For each raw line $l$, let $D_{w,l}(P)$ mean that a proof with exactly one occurrence of $l$ and no other line exists. The raw line inputs have Kronecker delta coefficients and raw point inputs have zero coefficients. At OR take the OR of the child coefficients. At an AND with children $u,v$ the recurrence is
$$
 D_{w,l}=(a_v\wedge D_{u,l})\vee(a_u\wedge D_{v,l}).
$$
At the root this predicate implies the original output on $(P,\{l\})$. The maximal negative with all points outside $l$ therefore turns it off. At $P=\{p\}$ it is true precisely on the counted flags at $l$.

Compute all root coefficients simultaneously in reverse. Start with a context bit one at the root and propagate context down each edge, unchanged across OR and multiplied by the sibling baseline across AND. OR the contributions at each destination. Distributivity, or induction on eliminating the last remaining gate from a linear expression, shows that the accumulator at each raw line is exactly its root coefficient. Trim to the root cone first. Each of the $2N$ inputs is essential, and the output is an internal gate. If the cone has $s'$ gates, its $2s'$ edges end at exactly $s'-1+2N$ different nonroot vertices when oriented towards inputs. Thus at most $s'+1-2N$ binary ORs combine incoming contributions, and at most $2s'$ products suffice for the edge weights. Including the baseline tape the shared point circuit costs at most $4s'+1-2N$. Constants and copies may be propagated away. Drop empty columns; every retained output is nonconstant.

Apply the project's [checked multioutput lower bound L-meta-1624](https://github.com/open-goat/pequalnp-proofs/blob/82b3b4894f43e862371c48a6d34284edc00792ca/lean/PEqualNP/Outside/L_meta_1624.lean) with the actual point set of each retained line as its allowed support, and the counted points on that line as its required set. The supports have pairwise intersection at most one. The checker theorem charges at least $H-N$ gates. Combining the two inequalities proves the claim.

One can bound the exceptions locally. At a flag $(p,l)$ call an AND a collision if **both** children are false at $(\{p\},\varnothing)$ but true at $(\{p\},\{l\})$. Outside the union of these flag sets, induction shows that every true wire either has a baseline proof or has a one-line proof. At AND, if both children turn true from false simultaneously there is a collision; otherwise use the other child's baseline proof. OR just chooses a true child. The root has no baseline proof. Thus $Nq\le 4s+|\bigcup_g C_g|$, with room of $2N-1$, even if there are arbitrarily many gates depending on both shores. In particular no AND with a line-independent child can collide, however complicated its point behavior is.

## Isolating a bounded number of ANDs that combine line inputs

Let $k$ be the number of ANDs for which both operands semantically depend on lines. No restriction applies to the number of ANDs combining point-dependent operands. The following additional estimate holds:
$$
 Nq\le (2k+2)s+(2k^2+3k+1)N.
$$
It implies the desk bound at every $q>100$ if $k\le11$. More generally, for any $k$ for which $2k+2<100$, the conclusion holds when $(98-2k)q\ge100(2k^2+3k+1)$.

Cut the outputs of the $k$ indicated gates into fresh formal sources $z_1,\ldots,z_k$ in topological order. Raw lines are also formal sources. Every other gate becomes affine over these Boolean sources with point predicates as coefficients. OR adds; an uncut AND with one line-independent child multiplies the other child by that child's exact point predicate, obtained on the original no-line baseline. For two line-independent children use their exact baseline product. These replacements are valid on the actual input for each value of the cuts produced by the original circuit. One forward tape for the actual point baselines suffices. In a target's affine expression the true constant term (all cut sources zero) is at most its actual no-line baseline, since the actual no-line cut values dominate zero. That actual baseline is in turn at most the target on every real singleton-line input. Replacing the affine constant term by this intermediate baseline therefore preserves the value on all inputs used below.

For each child of each cut gate and for the final output, use the preceding reverse traversal for this affine circuit. One sweep costs at most $s$ gates. In the reachable reverse graph expand $i$ internal nodes, including $a$ single-branch ANDs, and let $r\ge1$ be its number of boundary nodes. For a target which is itself a boundary no gates are needed. Otherwise there are $2i-a$ edges arriving at $i-1+r$ distinct vertices, hence at most $i-a$ combining ORs. The AND edges contribute at most $a$ multipliers. The bound also holds when scalar branches are discarded. This computes the coefficients of *all* line inputs and all cut sources for that target, even when the target is a raw input or previous cut source. Its baseline comes from the forward tape. There are at most $2k+1$ targets.

For each raw line $l$, evaluate all these expressions on singleton line $l$, in cut order. Each target uses at most one OR for its constant term and direct coefficient for $l$, plus a product and an OR per earlier cut source. The two children of cut $j$ have at most $j-1$ earlier sources, and the final target has at most $k$, giving exactly $k^2$ as an upper bound for the sum of these counts. Form the $k$ cut ANDs as well. This costs at most $2k^2+3k+1$ gates per line. The resulting $N$ outputs are the original function with one selected line, for every point assignment. They accept the incident singleton points and reject the complementary point set. L-meta-1624 gives the displayed bound.

For $k\le11$ the right side is at most $24s+276N$. When $q>380$ this contradicts $100s<Nq$. At orders $101$ through $380$ the bound already holds with **unrestricted** $k$: the two-stage deletion and moment calculation in [the rectangle argument](plane-rectangle-separation.md#applying-the-deletion-twice) requires only tests on at most two inputs and $19(q+1)\le N$. Substitution of $19$ there gives the required numerical inequality throughout this interval.

## A few gates can account for most line collisions

The cut construction also yields a bound without requiring any uncut operand to be line-independent. Choose any $k$ AND gates as cuts, and let $M$ count the flags on which at least one *uncut* AND has a collision as defined above. The number of chosen gates can be much smaller than the number of gates combining line inputs. Then
$$
 Nq\le (6k+4)s + (2k^2+3k)N + M .
$$

Use the same actual point baseline $a_w$ as above. In each uncut AND propagate both contributions, with the opposite child's baseline as multiplier. In other words represent the full value as its original baseline OR an affine expression in the active sources. At OR add child contributions. At AND use the single-line recurrence, treating a full cut value as an additional source when the corresponding child is a cut. The expansion in these sources contains only weighted single sources, together with the original baseline. If a propagated contribution represents a cut signal already true at baseline, the additional term is redundant. All computed values are lower bounds on the real wire under the actual assignment, by monotonicity and the two possible AND terms. At each cut multiply its two reconstructed child values exactly. At flags outside the exception set, every uncut true AND either already has two baseline-true children, or at least one child has a baseline proof and the other has been reconstructed by induction. Therefore the scheme is exact on all wires at those flags. It is sound on the maximal negatives for each line, which is enough for L-meta-1624.

Each reverse sweep has at most $s$ combining ORs by the reachable edge count, and at most $2s$ products, for at most $3s$ gates. The forward baseline costs $s$. At most $2k+1$ sweeps and the previous per-line calculation suffice. The root baseline is identically zero, saving the root's constant-term OR in every column: $2k^2+3k$ gates per line suffice. In particular, even arbitrarily many line-dependent ANDs outside a chosen set are harmless to this estimate if they collide only on flags already covered by the exception budget. The sharper one-line estimate above applies when $k=0$.

## Verification and scope

The companion [Lean file](PlaneCrossRestrictions.lean) checks finite stabilization, simultaneous agreement under a shared choice, semantic separation, the rebased product identities, prefix agreement and monotonicity, singleton projections, damage arithmetic, the local linearization and transposition identities, and the numerical cut and order bounds. The whole circuit constructions and the gate-charging arguments above are mathematical proofs in this note. The [finite tests](plane-cross-restrictions.py) exercise restrictions on explicit circuits and build the two reverse programs. On the dual Fano example the one-line program captures 15 of 21 flags, one selected cut restores a sixteenth, and the full cut program agrees on all 896 point-set and selected-line combinations. Comparisons include all point sets disjoint from the selected line. No unrestricted Lean solution to L-meta-2008 follows from the current estimates.
