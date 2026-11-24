# Partial-star lower bounds for the quadrangle separator

L-meta-5200 asks whether a circuit with two output wires and exactly two AND gates directly reading an AND gate must have at least 63 gates. Between them the outputs accept all 52 plane incidences. Each rejects all 234 quadrangle inputs and has a positive flag the other rejects. This promise leaves many incidence-free inputs unspecified.

We prove the 63-gate lower bound for ten sufficiently developed line centers, or for nine such centers when the four remaining lines pass through a common point. Each selected line can have several partial stars. The proof permits arbitrary gates and sharing after their computation and uses neither the number of direct AND reads nor the exclusivity of the two outputs. The [65-gate control](QuadrangleStarCores.lean) meets the assignment's structural and testing conditions. The general lower bound remains open.

## Count the selected gates and the sources they leave

Join the two output wires by one OR to work with one output. A line fragment ANDs its raw line bit with an OR tree on a nonempty subset of its four raw incident points. A single point needs no OR. For each chosen line j select fragments on pairwise disjoint subsets, and require their output wires to be read in the live suffix. Let dⱼ count the points covered and tⱼ the fragments. Give the line the score

```
dⱼ + tⱼ + [dⱼ < 4].
```

The dⱼ fragment gates are distinct because the chosen sets on a line are disjoint and different lines meet at most once. Put the selected gates first. Each fragment contributes a suffix source that vanishes when its line bit is set to zero. If the fragments miss a point of the line, the raw line must also be a source. With just that point active all its fragments are zero and varying its line bit changes the required answer. The negative singleton extends to a quadrangle test. Thus the sum W of the scores counts the gates in the prefix plus a lower bound for the number of distinct line channels turned off in the suffix.

**Ten-line result.** Any ten chosen lines with W ≥ 50 force at least 63 original gates. A full ordinary star scores five. So does a star on three neighbors, or two distinct singleton edge products on the same line. These examples may be mixed.

**Nine-line pencil result.** If the four unchosen lines form a pencil, W ≥ 45 on the other nine likewise forces at least 63 gates.

The usual ten-full-star lower bound is valid even if some selected full star output is unused. Each such line must still have at least one live channel, its raw line or its star. The same convention applies to a single full star in the nine-line result.

## When a private point can be absent from the suffix

A private point q lies on only one unfinished line L. Work with just the bit of L active. A negative set of points suffices if it lies inside a quadrangle missing L, by monotonicity. Adding q then enforces a positive flag. A live point OR from the prefix is called a helper. If q is not read raw, every such negative toggle must change some helper. Along one completed line, the helper supports containing q form a nested chain in the one chosen fragment that can contain q.

There are three other lines through q. Take one other point from the smallest live helper containing q on each of these lines where one exists. Every choice saturates every helper depending on q. Any choice with at most two points extends to a quadrangle missing L. Three distinct off-line points extend exactly when they are noncollinear. The [Lean proof](QuadrangleStarCores.lean) certifies the extension direction for the actual Singer lines, using 54 quadrangles avoiding the zero line and translation. The converse follows from the definition of a quadrangle. The [independent enumeration](quadrangle-star-cores.py) finds 468 collinear obstructions among 1,404 three-line transversals.

Consequently, if q is unread, all three lines must provide helpers, and every choice of their partners must be collinear. Two of the choices determine the line of the third, which intersects the remaining line through q at exactly one point. The smallest actual live helper on each line must therefore be the exact two-input OR of q and a single partner. The three partners are collinear. The Lean lemma `forcedPartner` proves uniqueness on each old line from the quadrangle extension and unique-line properties. Each such helper can be charged to at most two unread private points.

When k distinct live suffix sources are fixed to constants and the restricted target stays nonconstant, at least k gates disappear. For a binary cone the undirected cycle rank is g − s + 1 for g gates and s sources. Propagation and deletion produce a connected minor with no more cycle rank and at most s − k sources. This gives the claim. With fan-in at most two, the initial rank is at most g − s + 1 and the reduced circuit can be made binary by contracting copies and removing constants. Other source correlations can be substituted after the specified constants have been propagated. In particular, two retained sources may subsequently receive the same input label.

## Three unfinished lines

For a triangle keep its three intersection points. The six other points on those lines are private. Each read raw is one constant source when we set those six and all points outside the union to zero. For an unread private q at most one of its three partners can be a retained corner. Two corners lie on its own line and cannot occur together with q on an old line. Thus there are at least two constant pair helpers per unread q counted with multiplicity. Each pair can be charged at most twice. At least six distinct sources vanish in total, beyond the completed line channels. Any other surviving helper becomes a constant or a copy of a corner. The remaining six-input projection has all its negative boundary rows. Seven gates cannot compute it and eight suffice.

For a pencil retain its common point and one private representative on each of the three lines. Select each representative independently and uniformly among the three candidates. An unread private q is unselected with probability 2/3. Conditional on this event each of its three partners is unselected with probability at least 2/3, since none is on its own line and points outside the unfinished union are always turned off. Half the expected number of zero pair helpers charged to unread points, plus the expected number of unselected raw reads, is therefore at least six. Some frame loses at least six distinct sources.

The pencil core permits additional negative-row choices. The [exact search](quadrangle-star-cores.py) finds two negative boundary profiles among its 1,404 frames. Relative to the edge function, one has one unspecified input and the other has three. Each still costs eight gates without helpers. This remains true with arbitrary free ORs of retained private points. All seven raw inputs must be read. To force a private point, set the other two private bits to one and activate only its line. The row without the point is a projected negative in both profiles. This saturates every genuine helper containing the point. If at least two helpers are used, nine sources require eight gates. If one helper is used in seven gates, the circuit is a tree. The common point and a line bit then occur only once each. The other variables can give AND (all zero) or OR (enable a different line and the private point of the first line). The helper is constant within either test. The lowest common ancestor of the two variables in a tree has a fixed operation, excluding the two restrictions. This covers every surviving helper, including a retained triple OR.

In both geometries the single output therefore costs at least W + 6 + 8 gates. Subtract the appended OR to obtain W + 13 for the two outputs.

## Four unfinished lines in a pencil

These four lines contain every plane point. The common point c has no completed incident line, so no prefix point OR contains it. A suffix must read c, all four unfinished lines and each of the twelve private points except the h omitted raw inputs. Let r count live point helpers. If the joined circuit has at most 63 gates, its suffix has at most

```
47 − W + h − r
```

operand reads beyond the first use of each non-output wire. This follows by subtracting the mandatory completed channels, the 17 − h private or common raw inputs and unfinished line bits, and the r helpers from the gate budget, then adding one. Lower fan-in can only reduce this number.

Zero excess is impossible. In the suffix tree the raw common point c and any unfinished line bit y occur once. Turn off all completed lines. With no other inputs the restriction to c and y is AND. Enable a private point of y and another unfinished line to obtain OR. The row where both c and y are zero is nonincident and extends to a quadrangle negative. Point helpers stay constant within either test. Therefore W ≥ 45 forces r − h ≤ 1. Every absent private input requires its three pair helpers. Hence 3h ≤ 2r and r ≤ 3. Two helpers cannot conceal even one point. Three cannot conceal two points because two triples of different edges incident to different points share at most their common pair. We conclude that h = 0 and r ≤ 1.

Keep c and one private representative per line. If a helper is used, pick each representative outside it. A completed line meets each pencil line once, leaving at least two choices per line and at least 16 frames. Only nine frames per pencil have the four representatives collinear, one on each of the nine completed lines. We can therefore choose a noncollinear frame while making the helper zero. Without a helper choose any noncollinear frame. Turning the eight other private points off removes at least eight gates in addition to the completed line channels. The remaining core has nine inputs and needs eleven gates, as shown below. The single output costs at least W + 8 + 11 ≥ 64.

## The eleven-gate core certificate

The [calculation](quadrangle-four-pencil.py) projects every quadrangle onto the actual retained variables and audits all 1,053 frames. There are 936 noncollinear frames and 117 collinear frames. In the noncollinear profile, fourteen rows are unspecified after monotone propagation. They give 1,067 monotone completions, or 418 up to simultaneous permutation of the four arms preserving the negative rows. The completion with all unspecified rows zero is the edge function of a tree on nine vertices with eight edges and a four-edge matching. The [formal forest bound](../lean/PEqualNP/MetaComplexity/Helpers/ForestBound.lean) gives eleven gates. The usual four stars and three ORs attain eleven on the partial promise.

For the other completions the [Boolean calculation](plane-small-core-bounds.py) excludes any circuit with two or fewer reads beyond the first, which on nine essential inputs excludes ten gates. Here is the criterion used by the program.

1. Every proper block of at least two variables has more than two distinct cofactors on its complement. Its variables cannot feed the rest exclusively through one bit. The program checks this by the truth table. It also finds pairs of variables admitting both AND and OR restrictions. Every such pair has a repeated variable in the unfolded formula.
2. If there is a repeated wire, a first one in topological order has a tree below it whose source variables feed the rest exclusively through it. A proper block of size at least two was just excluded. A block of all variables would make the function read-once. Thus the first repeated wire is a raw input i. If the only repeated wires are one or two raw inputs, these must meet every switching pair. The checked functions require more than two variables to meet all such pairs.
3. The remaining possibility with two excess uses is a second, internal wire h that branches. If h receives neither or both occurrences of i, the variables below h form an excluded one-bit block, or include all variables and give a function with only i repeated below h. The internal cone cannot be built from just i using two distinct operands. Otherwise h uses one occurrence of i and a nonempty set B of private leaves. Outside B and i, variables occur once. The program considers every i and B meeting all switching pairs.
4. For each fixed value of i, every nonconstant cofactor on B obtained by fixing the outside must be the same function, namely the subtree h with that setting. Two distinct nonconstant cofactors exclude the choice. If both settings determine a cofactor, together they specify h on B and i. This must be a read-once function essential in all its inputs. Read-once recognition contracts a pair with at most two cofactors to one new input and tries all such pairs. The bottom sibling pair of any read-once tree makes this test necessary. No possible i and B survives for the 417 noncanonical completions. The Boolean argument only concerns the normalized minimum circuit, so constant gates, copies and duplicate operands can be removed before applying it.

The collinear profile leaves 23 rows unspecified. Its 87,009 completions form 5,631 classes. Again every noncanonical class fails the same test. Thus either raw frame has minimum eleven.

The same program separately tests a template that bundles each group of three privates by OR before the remaining circuit. Its 291 monotone completions fall into 60 classes. All 59 noncanonical classes fail the two-excess test, giving the same eleven-gate minimum for that template.

## Verification

Run the following from the research repository's Lean directory with its pinned toolchain. The Lean file uses the desk definitions from commit `82b3b4894f43e862371c48a6d34284edc00792ca`.

```sh
python3 ../notes/quadrangle-star-cores.py
python3 ../notes/quadrangle-four-pencil.py --check
lake env lean ../notes/QuadrangleStarCores.lean
```

The 65-gate control separates the flags into two groups of 24 and 28. Its gates numbered 4 and 5 are exactly its two direct AND readers, and both lie in the live cone. The unrestricted case can use fewer or smaller fragments, mix the two shores, or leave four unfinished lines in another configuration.
