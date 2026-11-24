# Rectangle programs for projective-plane incidence

For every projective plane of order $250\le q\le380$, the rectangle program in L-meta-5086 has at least $Nq/100$ internal nodes, where $N=q^2+q+1$. This allows arbitrary sharing. At every order $q\ge250$ it has the following lower bound for any integer $3\le k\le q$:

$$
s\;\ge\;4N-2k(q+1)-\frac{2q(q-k)}{k+1}.
$$

Taking $k$ near $\sqrt q$ gives $4N-O(q^{3/2})$. For arbitrary $q$ a separate argument proves the desk bound if at least one hundredth of the flags have an accepting proof with exactly two raw leaves in the reconstructed circuit. It also proves the bound at every order for an OR of products of raw clauses, with no bound on the number of clauses and with each internal gate shared by up to 33 term cones. When each term has at most $q$ clauses, raw ORs may be shared without limit and each AND may serve 16 terms. With no bound on the number of clauses, raw ORs can still be shared without limit if each AND serves at most two terms. The general $Nq/100$ bound above order 380 is open.

## Rectangles and the actual testing promise

The left coordinate of a rectangle is a set of ordered point-line pairs, the right coordinate a family of line sets. The required rows are the incident pairs, called flags. The required columns are all line sets $T$ of size at most $q$. Write $Y_e$ for the Boolean input with just the two ends of flag $e$ on. Write $Z_T$ for the input with the lines in $T$ on and the points outside their union on. These are the positive and negative inputs of the corresponding monotone circuit.

Assign each nonempty rectangle $A\times B$ a wire that is true on every $Y_e$ with $e\in A$ and false on every $Z_T$ with $T\in B$. The raw terminal condition gives exactly these two facts for the named raw variable. For an empty row side use constant zero and for an empty column side use constant one, taking zero if both are empty. Suppose a nonempty parent is covered by two children. Either one child already covers it, or both children contain its whole column side and their row sides cover the parent rows, or both contain its whole row side and their column sides cover the parent columns. To see this, test whether each child contains the whole row side. A row missing from one child forces every parent column into the other child. The four possibilities give precisely the cases listed. Copy for containment, OR for a row split, AND for a column split. This builds one shared wire per node, with no expansion into a tree. Copies and constants can be propagated away for a nonconstant root.

Conversely every binary separator gives a rectangle at every wire by taking its true positive rows and false negative columns. At OR, one child suffices on the positive row and both work on the negative column. At AND the roles reverse. Each parent rectangle is therefore covered by its two children. The [Lean file](PlaneRectangleSeparation.lean) constructs the entire forward program in topological order from the actual desk hypotheses and verifies the reverse gate step.

A positive input containing any flag must be accepted by monotonicity. Any incidence-free input with at most $q$ active lines is contained in $Z_T$ for its set $T$ of active lines and must be rejected. Hence the circuit agrees exactly with the incidence graph on all inputs of weight at most two. The unrestricted linear bound below needs only these small tests. Isolated vertices can be pinned to zero. On an induced subgraph take a smallest circuit matching its weight-at-most-two table, allowing arbitrary values above that weight.

## Paying two gates on one shore

In any bipartite graph, take an entire shore of at least two nonisolated vertices whose neighborhoods are pairwise distinct. There is a vertex on this shore whose zero pin saves at least two gates in a minimum binary monotone circuit for the small tests. Pinning leaves another edge, so the residual is nonconstant. Every vertex chosen is essential, witnessed by an incident pair and the singleton at the opposite endpoint. Dead gates, repeated operands and constants can be removed in a minimum circuit.

Two direct readers of a variable both disappear under its zero pin. A single AND reader becomes zero and has a successor, which also disappears. The remaining possibility is that every vertex on the shore is read only once, by OR. Consider the earliest reader of any of these variables. If it joins two raw variables from the shore, their interchange cannot affect the output, despite the two different neighborhoods. Otherwise it reads a raw vertex $p$ and a wire $W$ depending only on the opposite shore. If $W$ is false on every singleton there, it is false on every required positive pair. Replacing this OR by $p$ preserves all required positives and can only lower the output on required negatives, contradicting minimality. Thus $W$ accepts a singleton $z$. Pick any neighbor $y$ of $p$. With just $y,z$ on, the circuit must reject. Turning on $p$ must make it accept, yet $p$'s unique reader is already true. This is a contradiction even if $z=y$. The Lean lemma `no_or_mask` proves the masking step for arbitrary monotone $W$ and downstream decoder.

One essential raw vertex can always be pinned to zero at a cost of at least one gate when the residual stays nonconstant. At each step we may minimize the surviving circuit again. Previously unused raw inputs or gates removed simultaneously cannot invalidate a lower bound for the residual problem.

## Applying the deletion twice

Every point lies on $q+1$ lines. The lines through it partition the $N-1$ other points into classes of $q$ by the desk's unique-join hypothesis. Two different lines share at most one point. In particular, before deleting any lines all point neighborhoods remain distinct as points are deleted.

1. Keep paying two gates per point until exactly $r=k(q+1)$ points remain. Call this set $R$. This has already cost $2(N-r)$.
2. Let $d_l=|R\cap l|$. Drop empty lines. Pin each line with $d_l=1$ to zero for a further gate since its sole edge is still required. At least one remaining line has two points, because $R$ contains two distinct points. All lines with $d_l\ge2$ have pairwise distinct neighborhoods on $R$, by unique join.
3. Pay two per remaining line until just one is left. Its incident star has at least two neighbors, so the residual already needs at least two gates. A one-gate circuit cannot depend on its three essential vertices.

Writing $B_0,B_1$ for the numbers of empty lines and lines meeting $R$ once gives

$$
s\ge 2(N-r)+B_1+2(N-B_0-B_1)=4N-2r-(2B_0+B_1).
$$

There is no assumption about which vertices can be chosen for the two-gate deletions. The moment bound holds for **every** possible remaining set $R$.

Double counting incidences and ordered distinct pairs in $R$ gives $\sum_l d_l=r(q+1)$ and $\sum_l d_l(d_l-1)=r(r-1)$. For integer $d$, $P_k(d)=(d-k)(d-k-1)$ is nonnegative. At zero it equals $k(k+1)$; at one it equals $k(k-1)$, at least half as much for $k\ge3$. Substituting $r=k(q+1)$ gives

$$
(2B_0+B_1)k(k+1)\le 2\sum_l P_k(d_l)=2qk(q-k).
$$

This proves the displayed bound. With $k=19$ it implies $100s\ge Nq$ at every integer from 250 through 380. At $q=380$, $N=144781$ and the integer bound is $s\ge550928$, exceeding the requested $550168$ gates. The [Lean proof](PlaneRectangleSeparation.lean) checks both moments from the desk's incidence axioms, the weighted penalty and all 131 integer orders. The two-stage gate deletion itself is the mathematical argument above.

## A sharp bound for flags with two-leaf proofs

Unfold an accepting circuit computation into a proof of truth on a flag: choose a true child at each OR, take both at each AND, and stop at raw input occurrences. Let $D$ be the flags admitting such a proof with exactly two leaves. Both endpoints must occur. A proof using copies of just one variable would accept a singleton.

Each two-leaf proof has one AND. Above that AND and along both paths to its raw leaves, it uses only ORs. Mark gates reached backwards from the output by ORs, stopping at each first AND. Every marked wire implies the output and thus rejects every singleton. For a raw path below one of the marked AND operands, keep its OR-only expansion, putting zero in place of any further AND. A marked OR has empty raw expansion, since a raw OR-only path to it would make a singleton true at the output. Consequently an OR gate needed for nonzero raw preprocessing can never also be charged for the marked output network. A marked AND used in another operand is given value zero in the raw expansion at that use. This builds a flat separator for $D$ with at most the original number of gates, preserving any existing sharing between raw ORs. Its output on pairs is exactly $D$, by the two-leaf characterization. Replacing the expansions by subsets only removed positives, so it still rejects every forbidden pair.

Each productive AND now takes two disjunctions of raw inputs. Their supports are disjoint, or a singleton would pass. Every cross pair must be an edge, so the two supports form a biclique in the four-cycle-free incidence graph. It is a star with one singleton center and a subset of its neighbors. Assign every edge in $D$ to one term covering it. Remove terms owning none for this count. For a center $c$ let $m_c$ count its assigned distinct neighbors and $t_c$ its terminals. The union of the raw OR cones for the $t_c$ neighbor disjunctions has at least $m_c-t_c$ binary merges: each binary merge can reduce the number of source components by at most one. One may equivalently project these cones to the assigned neighbors and contract empty or unchanged branches. A counted merge there contains at least two neighbors of $c$. A neighbor disjunction at another center cannot contain that gate: different same-shore neighborhoods meet at most once, and opposite-shore neighborhoods are disjoint. The charges are distinct.

Thus for $t$ productive terms the circuit spends at least $|D|-t$ raw ORs, $t$ ANDs and $t-1$ output ORs. The centers cover $D$. For nonempty $D$ this gives $s\ge |D|+\tau(D)-1$. In particular, if $100|D|\ge Nq$ the desk bound follows. When the circuit is multilinear at every AND (its two input cones have disjoint raw variable sets), every flag has a two-leaf proof. No leaf can repeat in such a proof, because two branches can diverge only at an AND. The full incidence graph has cover number $N$: a regular bipartite graph has a perfect matching by Hall's theorem. Therefore these circuits need exactly $N(q+2)-1$ gates in the optimum. One full star per line achieves equality. For a general circuit a flag can force repeated endpoint occurrences, and the argument above gives no unconditional lower bound on how many flags avoid repetition.

## Products of arbitrary numbers of raw clauses, with shared gates

Suppose the output is a binary OR of terms, each a binary AND of disjunctions of raw inputs. Allow arbitrary sharing inside a term. Allow an internal gate to occur in up to 33 distinct term cones, with the final OR network outside those cones. Then the full desk inequality holds for every $q\ge250$. This result applies to the reconstructed separator whenever it has this form.

Consider a live term accepting $e>0$ flags. It rejects all required negatives since it feeds an OR output. Write $H$ for its accepted flag graph, $v$ for the number of its nonisolated vertices, $k$ for its number of distinct raw clause supports, $g$ for its total number of distinct gates, and $x=g+1$. Assume the claimed global bound fails. In particular $k\le s+1<2^q$: for $q\ge250$ even $(q+1)^3<2^q$ by induction. Write $j=\lfloor\log_2 k\rfloor$.

**Induced matching test.** Take $h\le q$ accepted flags forming an induced matching in the *full plane*. A transversal chooses exactly one endpoint from each flag. These $2^h$ inputs are incidence-free and involve at most $q$ lines, so all must be rejected. Every clause hits every matched flag. A clause cannot miss two distinct transversals: at a differing coordinate their union contains both ends of a matched flag. Thus $k\ge2^h$. Since $k<2^q$, any induced matching of accepted flags in the ambient plane has size at most $j$.

**Bounding the ordinary matching number.** Take a maximum matching of $t$ accepted flags. On its $t$ points and $t$ lines let $a$ be the number of *ambient* incidences, including the matching. If the line degrees on those points are $b_i$, the absence of four-cycles gives $\sum b_i(b_i-1)\le t(t-1)$. Cauchy's inequality then gives $2a-t\le t\sqrt{4t-3}$. Form a conflict graph on the matched flags, joining two when a crossed incidence exists. The two crossed incidences cannot both exist. Thus this graph has $a-t$ edges. In a uniformly random ordering, select a vertex when it is earlier than all its neighbors. The selected set is independent and its expected size is $\sum_u1/(1+\deg u)\ge t^2/(2a-t)\ge\sqrt{t}/2$. Such an independent set is an ambient induced matching. The preceding test gives $t\le4j^2$.

**Bounding the flags incident with nonleaves.** A vertex has at most $j$ neighbors of degree at least two in $H$. For each such neighbor, choose an accepted second edge to a vertex other than the original center. The chosen edges form an induced matching in the full plane: a crossed incidence or coincidence would give two distinct common neighbors of the associated vertices through the center. Delete the original degree-one vertices. The remaining graph thus has maximum degree at most $j$ and it inherits a cover of size at most $t$ by König's theorem. If $L$ is the number of deleted leaves, at most $L$ edges had a leaf endpoint. Consequently
$$
2e\le\max(2,j)v,\qquad e\le L+jt\le v+4j^3.
$$

**What the term costs.** Clearly $v\le x$, because its binary cone depends on every endpoint. A star already satisfies $e=v-1$. Otherwise $H$ has a two-edge matching: every clause has at least two inputs and its own OR terminal, and combining $k$ distinct terminals requires at least $k-1$ distinct ANDs. Hence $2k\le x$. There is also the independent bound $v+k\le x+2$. The union of all raw OR cones has at most two connected components, since each clause contains an endpoint of any one fixed accepted flag. These cones collectively use all $v$ essential raw inputs. The elementary binary graph count requires at least $v-2$ distinct ORs. Adding the ANDs gives $g\ge v+k-3$.

Together these inequalities imply $e\le3x$. For $j\le6$ use the degree bound. For $j\ge10$, $j^3\le2^j$ by induction, so $e\le v+4k\le3x$. At $j=7,8,9$ combine $2e\le jv$, $e\le v+4j^3$, $v+k\le x+2$ and $k\ge2^j$. [Lean](PlaneRectangleSeparation.lean) checks these three integer implications, the power inequality and the injection of transversals into clauses.

Discard empty terms and take $r$ surviving terms. Their accepted flags cover all $N(q+1)$ incidences. Their internal gate counts sum to at most $33(s-r+1)$, since at least $r-1$ separate output ORs are needed. Thus $N(q+1)\le 3\sum_i (g_i+1)\le99(s+1)$. Since $N\ge99$, this proves $Nq\le100s$, contrary to the assumption. The unrestricted rectangle program need not compile to an OR of such terms within that sharing limit.

## Unrestricted sharing of raw ORs

There is a second regime with no limit on shared raw disjunctions. Suppose each product has at most $q$ distinct clauses and each AND gate is used by at most 16 term cones. Then the $Nq/100$ bound holds even with arbitrary sharing of raw OR gates. With private ANDs the argument gives $N(q+1)\le 6s$.

For a nonempty term take a minimum cover of its flag graph and assign its edges to cover endpoints. Fix a center $c$ with an assigned edge. Some clause misses $c$, because the singleton at $c$ is forbidden. Among the missed clauses there is one whose literals on the opposite shore are all neighbors of $c$. Otherwise choose one opposite nonneighbor from each missed clause. Turn on $c$ and all the chosen variables. This satisfies every clause, but contains no incidence. When $c$ is a point, there are at most $q$ chosen lines; when it is a line, only that line is active. Both are required negatives by monotonicity. The resulting restricted clause contains every assigned neighbor of $c$, since it misses $c$ and the term accepts those flags. The Lean lemma `projected_terminal` proves the finite selection principle.

Keep one owner for each of the plane's flags across all terms. For each used center, collect its owned neighbors and its chosen clause terminals across all its terms. Project their raw OR cones onto those neighbor inputs and contract branches with identical or empty projected support. As in the flat case, at least the number of distinct owned neighbors minus the number of those terminals are binary merges. A counted gate has at least two raw literals on that center's opposite shore, and **every** opposite-shore literal of the gate lies in the center's neighborhood. Those two literals determine the center, so a gate is charged at most once for point centers and once for line centers.

Let $O$ be the number of preprocessing OR gates, $A$ the number of AND gates, and $t_i$ the cover size of term $i$. We have $N(q+1)\le 2O+\sum_i t_i$. For a term with $k_i$ distinct clauses, the matching argument gives $t_i\le4\lfloor\log_2 k_i\rfloor^2\le6(k_i-1)$. Empty terms can be omitted, and a nonempty safe term cannot consist of a single raw disjunction. Each term uses at least $k_i-1$ ANDs. If each AND lies in at most $b$ term cones, this gives $N(q+1)\le2O+6bA\le6bs$. At $b=16$ the factor is 96. The argument does not charge the output ORs or require the preprocessing ORs to be private.

## Arbitrarily many clauses with free sharing of raw ORs

The same projected-terminal argument covers arbitrary clause counts when each AND appears in at most two term cones. Assume for contradiction $100s<Nq$. For one productive term let $k$ count distinct clauses, $j=\lfloor\log_2 k\rfloor$, and let $t$ be its minimum cover size as above. A line center always has the pure opposite-shore projection, since its blocking assignment uses only one line. A point center with just one assigned flag can be charged directly to its single cover occurrence. Call a remaining point center *exceptional* if no clause missing it has its line literals entirely among its incident lines. An exceptional center has at least two different accepted line neighbors. It can occur only when $k>q$, by the preceding section.

We first bound $j^2\le2q$. Since $k\le s+1\le q^3/64$ for $q\ge250$, write $a=\lfloor\log_2 q\rfloor$ to get $j\le3a-4$. For $a=7$, $17^2\le2q$ directly. For $a\ge8$, $(3a-3)^2\le2^{a+1}$ by induction from $a=8$: the ratio of consecutive squares is at most $(24/21)^2<2$. Thus $t\le4j^2\le8q$. Partition the exceptional centers into batches of at most $\lceil q/2\rceil$ centers. At most 16 batches suffice.

In a batch of size $h$, fix an exceptional center $c$. For each other center $d$ in the batch choose an accepted neighbor line of $d$ avoiding $c$. There is such a line since only one line through $d$ contains $c$. These $h-1$ choices hit every clause missing any such $d$, because the clause must accept the chosen flag at $d$. Consider the clauses missing $c$ and containing **every other center of the batch**. If there were at most $q-h+1$ of these, choose for each one an off-neighbor line of $c$, which exists by exceptionality. Together the two collections use at most $q$ lines, all avoiding $c$. Switching on those lines and $c$ satisfies every clause without making any incidence. This contradicts the negative promise. There are therefore at least $q-h+2$ such clauses for $c$. Their families are disjoint over centers in this batch. Each center owns at most $q+1\le2(q-h+2)$ flags. The exceptional flags cost at most $2k$ per batch, hence at most $32k$ per term, or $33(k-1)$ since an exceptional term has $k>q\ge250$.

All remaining flags cost at most $2O+\sum_i t_i$ by the projected-merge count, including the directly charged single-flag centers. Combining with $t_i\le6(k_i-1)$ gives $N(q+1)\le2O+39\sum_i(k_i-1)$. With each AND shared by at most two terms, this is at most $2O+78A\le78s$. It contradicts the assumed $100s<Nq$. The terminal selection and batching are independent of sharing in the raw OR preprocessing.
