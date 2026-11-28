# The eight-input edge detector and one NOT

Independent work on L-meta-34477 and its exact opposite L-meta-34476. The [live catalogue](https://data.pequalnp.com/data/desk/gaps.json) supplies the posted edge list and circuit semantics.

## A checked fourteen-gate circuit

Take the OR of the following four products.

- (5 OR 6) AND (2 OR 7)
- (4 OR 6) AND (1 OR 7)
- 3 AND (6 OR 7)
- 0 AND (4 OR 5 OR 7)

The products use three, three, two and three gates respectively, with three more ORs joining them. [Lean](EightVertexOneNot34477.lean) checks all 256 inputs against the desk's exact list-indexed predicate. It also checks monotone fan-in two, backward references and size. The [biclique replay](biclique-upper-34477.cjs) exhausts all covers of the posted edges by complete bipartite subgraphs and finds a minimum of fourteen gates in that formula construction. Arbitrary gate sharing lies outside this calculation.

## A sufficient seven-input lower bound

Setting input 1 to false leaves the six-vertex path 4–0–5–2–6–3, together with vertex 7 adjacent to every vertex on the path except 2. The graph symmetry swapping 1 with 2 and 4 with 5 gives the same cofactor type under pin 2. The biclique optimum of either cofactor is twelve gates.

The [Lean transfer](EightVertexOneNot34477Slice.lean) applies the signed-slice compiler to the input-1 cofactor. The singleton 4 is negative, and adding 1 makes it positive, so pinning 1 removes at least one paid binary operation. The compiled model permits free negation of each input or intermediate signal and uses a paid binary AND for each new signal. A circuit of at most thirteen gates containing a NOT therefore gives a signed program of at most eleven paid operations for the cofactor. If every signed program for the cofactor needs twelve operations, the checked fourteen-gate control gives the replacement required by L-meta-34476. Lean verifies this implication for the exact graph predicate.

## Search status

The [signed frontier search](34477-signed-frontier.cjs) enumerates available wire truth columns and four normalized signed binary operations per pair. A frontier with k operations left can have at most k+1 live wires, and it must distinguish every positive row from every negative row. The budget-ten and budget-eleven searches reached their time limits before either found a witness or proved exclusion. The biclique calculation and Lean transfer leave the unrestricted signed lower bound open.
