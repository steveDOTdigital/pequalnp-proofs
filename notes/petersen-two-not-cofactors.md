# Four exact binary-gate minima for the fixed-first-gate Petersen case

The circuit in [L-meta-2049](https://data.pequalnp.com/data/lemma/L-meta-2049.81ed303445ee.json) must compute the nine-vertex edge function in exactly fifteen gates. Its first gate computes the conjunction of inputs 0 and 2, and at least two gates are NOTs. This note proves exact costs for four restrictions, counting each binary AND or OR as one gate and allowing unlimited free negations, arbitrary fan-out, and a complemented output.

The table uses `+` for OR and juxtaposition for AND. The variables a, b, c, d, e, f, g represent inputs 1, 3, 4, 5, 6, 7, 8 respectively.

| Input 0 | Input 2 | Edge function after restriction | Minimum binary gates |
| --- | --- | --- | --- |
| 0 | 0 | b(c+g) + d(f+g) + e(a+g) | 8 |
| 1 | 0 | a+c+d+g(b+e) | 5 |
| 0 | 1 | a+b+f+g(d+e) | 5 |
| 1 | 1 | a+b+c+d+f+eg | 6 |

Each displayed expression attains its cost. A circuit depending on k inputs needs at least k−1 binary gates, since its output cone is connected. This proves the last three lower bounds. The first restriction has seven essential inputs and has the graph of a three-armed tree, with each arm consisting of two edges.

## Why the subdivided three-arm star costs eight

Fold constants, absorb negations into wire signs, and keep only the cone of the output. For b binary gates and seven essential inputs the cone has 2b operand edges and b+7 vertices. All vertices except the output have fan-out at least one. The total fan-out beyond one is b−6, counting repeated operand uses separately. Thus with at most seven gates, either the circuit is a read-once formula or there is just one wire that is used twice.

**Internal wire used twice.** Below that wire is a read-once subtree. All its inputs reach the rest of the circuit through its one output bit. If its input set B is proper, it has at least two elements and fixing B can give at most two functions of the remaining variables. But every such B gives at least three. If B contains an edge, use the empty selection, a singleton incident to a crossing edge, and an internal edge. These give three different functions, the last identically true. If B is independent, use the empty selection and two different singletons. The vertices have distinct nonempty neighborhoods outside B, so a single outside vertex distinguishes the singleton functions. If B contains every variable, the suffix only sees the one subtree output and computes a unary function of it. This leaves a read-once formula.

**Read-once obstruction.** The edge function of an induced four-vertex path has no read-once formula, even with free negations. Push inversions down to the leaves. An essential variable appearing once in a monotone function must occur positively. A nontrivial OR root would disconnect the graph. At an AND root the minimal true sets are unions of one minimal true set from each side. They all have size two, so each side can have only singleton minimal true sets. The graph would be complete bipartite. A path on four vertices satisfies neither condition. Fixing all other vertices to zero transfers this obstruction to any graph containing such an induced path, including the subdivided star.

**Raw input used twice.** Expanding the output as a formula now repeats only this input, r. If r is any leaf or any middle vertex, setting r to zero leaves both other arms intact and an induced four-vertex path. The remaining formula is read-once, which is impossible. So r must be the center.

Push negations to the leaves again and split at the root. If both occurrences of the center are on the same side, the root has disjoint variable sets. One side has at least two variables and is a proper one-bit block, which was excluded above. Thus both branches use the center once. Each branch has private variables: if a branch uses only the center, the restricted whole function is nonconstant at both values of the center. Such a branch must always take the neutral value for the root, leaving a read-once formula.

With the center zero, the function is a matching of three edges and all six private variables are essential. An AND root is impossible by the complete-bipartite argument. At an OR root, the two ends of each matched pair must be on the same side. Neither singleton alone is true and a disjunction of separate branches cannot create a crossing edge. One branch therefore contains at least two full arms. Fix all private variables in the other branch to zero. That branch then stays false at either center value, since the whole graph has no true edge with just the center selected. The remaining read-once branch computes a graph containing an induced four-vertex path. This excludes the last case.

## Consequences for the nine-input search

The fifteen-gate budget with at least two NOTs leaves at most thirteen binary gates. Under the joint zero restriction, any simplification of a witness must retain at least eight of those gates.

Fixing just input 0 to zero eliminates at least two binary gates. The prescribed first AND becomes constant. Input 0 must also reach the output along a path bypassing that AND: with input 2 zero and only input 1 selected among the seven remaining inputs, toggling input 0 changes the answer. After absorbing free negations the first binary gate on such a path reads input 0 and also simplifies away. Thus a witness would give a circuit of at most eleven binary gates, with free inversions, for the eight-input induced graph obtained by deleting vertex 0. Swapping inputs 0 and 2 gives the symmetric restriction. These necessary conditions leave the original existence question open.

## Reproducing the finite checks

Run `python3 notes/check-petersen-cofactors.py` from the proof repository. The script checks the four formulas on all 512 original inputs and verifies the 119 possible proper blocks of size two through six. It independently excludes 434 choices of shared raw input, root partition, and root operator. For each slice of the shared input, the true rows at an AND root, or the false rows at an OR root, must form a Cartesian product. Its projections uniquely determine each branch because every slice is nonconstant. The script checks whether both branches can be read-once by applying the same disjoint-partition test recursively.
