# Four is the sharp dimension bound under a four-cycle of the rows

Let F(X) sum the products of entries of J + X over the 120 injections from four rows to five columns, where J is all ones. If a complex linear space L satisfies F(X) = 120 on L and is invariant under any four-cycle of its rows, then **dim L ≤ 4**. Equality occurs. There is no column-symmetry assumption. In particular an L-gct-179 witness of dimension seven must break every four-cycle of the rows.

## The row frequencies

Number rows modulo four and let Aₖ consist of column vectors a for which the matrix with entries i^(kr) aⱼ belongs to L, where i² = −1. The four row-character projections split L as the direct sum of these spaces. Write dₖ = dim Aₖ and eₕ for the elementary symmetric polynomial of degree h.

For a list of k frequencies, the coefficient polarized in k directions factors into a row sum and a column sum. The row sum is the sum of the products of the k characters over ordered distinct rows. The column sum is the corresponding sum over ordered distinct columns of the k amplitudes. To obtain the coefficient, multiply by the common positive number of ways to complete a k-entry matching. Repeated directions only change the factorial if the same scalar variable is used. Every column sum below must vanish because its row factor is nonzero. The [integer check](check-row-cycle-bound.py) evaluates these factors, the two arithmetic certificates below and every coefficient of the extremizer.

For the zero frequency, constancy on a line with all rows equal implies e₁(a) through e₄(a) vanish. Indeed F(ta) in this case is 24 times e₄ of the five entries 1 + taⱼ. The polynomial with roots aⱼ therefore has the form T⁵ + constant. A nonzero solution is a scalar times a permutation of the five fifth roots of unity. This finite union of lines gives d₀ ≤ 1. If d₀ = 1, order and scale its generator as v = (1,ζ,ζ²,ζ³,ζ⁴) for a primitive fifth root ζ.

For each nonzero frequency the fourth-degree condition gives e₄(a) = 0. At frequency two the second-degree condition also gives e₂(a) = 0. Opposite odd frequencies have the quadratic pairing

    M(a,b) = (Σaⱼ)(Σbⱼ) − Σaⱼbⱼ = 0,   a ∈ A₁, b ∈ A₃.

## Planes in e₄ = 0

If any coordinate is identically zero on a subspace in e₄ = 0, the product of the four remaining coordinates vanishes identically. A second coordinate is identically zero. Such a space is supported on at most three coordinates.

Otherwise use the coordinate linear forms ℓⱼ on the subspace. Dividing e₄ by their product gives Σ1/ℓⱼ = 0. Group proportional forms. The reciprocal of each distinct form has a pole on its own hyperplane, so the coefficient of each group is zero. In dimension at least two this follows by choosing a generic point of each hyperplane and clearing its denominator. Each group has at least two members. The forms span the dual, so the dimension is at most two. In dimension two there must be a group of two and a group of three. The pair has opposite entries, and the plane contains a vector supported exactly on that opposite pair. It contains no other two-coordinate direction.

It follows that d₁,d₃ ≤ 3, and every three-dimensional odd space is an entire coordinate three-space. Also d₂ ≤ 1. Indeed e₂ on three coordinates is a nondegenerate quadratic form and has no totally isotropic plane. In the full-support case the opposite pair alone has nonzero e₂.

## Two opposite planes cannot coexist

Suppose A ⊂ A₁ and B ⊂ A₃ both have dimension two. The same argument applies with the odd frequencies interchanged. If A has full support, use its vector eᵢ − eⱼ. The pairing M forces bᵢ = bⱼ for all b ∈ B. The coefficient of frequencies (1,1,3,3) with the first vector used twice gives e₂ of the three remaining b entries equal to zero. Their image has dimension at most one, so B contains eᵢ + eⱼ up to scale. This same-sign pair excludes a full-support plane by the preceding classification. Thus B is supported on at most three coordinates and must be the span of eᵢ + eⱼ and a third coordinate vector eₖ. Pairing the first vector with arbitrary a ∈ A gives 2Σa = aᵢ + aⱼ = 0. Pairing the second gives aₖ = Σa = 0, contrary to full support.

Now both planes are supported on triples S,T, padding a smaller support if necessary. If their intersection has size two or three, the three-by-three restriction of M is invertible. For overlap three it is J − I. For overlap two it has rows (0,1,1), (1,0,1), (1,1,1) after relabeling. Orthogonal planes are impossible in this pairing. For overlap one, write h for the shared coordinate. On these supports M(a,b) = (Σa)(Σb) − aₕbₕ. Neither plane can map to zero under the map to (sum, shared entry), since its kernel on a triple is one-dimensional. Orthogonality in the two-dimensional target then forces both images to have dimension one. Each plane contains the difference of the two unshared coordinate vectors. These differences have disjoint two-element supports. The polarized coefficient (1,1,3,3) using each difference twice is nonzero, a contradiction. Five columns ensure that the triples intersect.

## Three odd dimensions without a fixed direction

If d₀ = 0, the bounds above already give dim L ≤ 4 unless one odd space is a coordinate three-space and both the other odd space and A₂ are nonzero. Relabel so A₁ is supported on the first three axes. Write b ∈ A₂ and c ∈ A₃ for nonzero vectors.

For any two different axes of A₁, frequencies (1,1,2) give zero sum of b outside the pair. Thus b = (h,h,h,d,e) with h+d+e = 0. The identity e₂(b) = 0 gives de = 0. After scaling and interchanging the last columns, b = (1,1,1,−1,0). Pairing with A₁ gives c = (x,x,x,y,z), y+z = −2x. Frequencies (1,1,3,3) give x(y+z)+yz = 0, so yz = 2x². Here x ≠ 0. Scale x to one, so y² + 2y + 2 = 0 and e₂(c) = −1. Frequencies (2,3,3) require Σ bⱼ e₂(c outside j) = 0. Direct substitution gives −2+y−y² = 3y, which is nonzero. This excludes the last case.

## Constraints from a fixed direction

Suppose d₀ = 1. For b in an odd space opposite a coordinate axis eⱼ, frequencies (1,3), (1,3,0) and (1,3,0,0) give

    Σ_{l ≠ j} bₗ vₗʰ = 0    for h = 0,1,2.

In order, the weights on bₗ before using earlier equations are 1, −(vⱼ+vₗ) and vⱼ²+vⱼvₗ+vₗ², up to common factors. They are the elementary symmetric functions of the roots outside j,l. Consequently if an odd space contains two coordinate axes, its opposite is zero. Indeed Σb = bⱼ = bₖ and Σvₗbₗ = vⱼbⱼ = vₖbₖ imply bⱼ = bₖ = 0. The three remaining moment equations form an invertible Vandermonde system on the remaining three coordinates.

Suppose an odd space A has dimension at least two and b ∈ A₂ is nonzero. The plane classification shows that A contains a vector supported on at most two coordinates, and it contains one supported on **exactly** two. In the case of a plane on at most three axes, intersect it with a coordinate hyperplane. If the result is a singleton axis and the support has size three, combine or eliminate that axis from an independent vector to find a two-coordinate vector. For a coordinate plane take the sum of its axes.

Let i,j be the support of this vector. Frequencies (1,1,2) and (1,1,2,0), or their odd-frequency reversals, force the sums of bₗ and vₗ bₗ outside i,j to vanish. For the second equation the original weight is −(vᵢ+vⱼ+vₗ). If the three outside roots are a,c,d, the outside entries of b are therefore t times w = (c−d,d−a,a−c). Frequencies (2,2) and (2,2,0) give e₂(b) = 0 and Σ_{l<m}(vₗ+vₘ)bₗbₘ = 0. The two outside moments just found make all pair/outside cross terms vanish in both identities. Eliminating bᵢbⱼ gives

    t² Σ_{l outside i,j} (vᵢ+vⱼ−2vₗ) wₗ² = 0.

The coefficient is nonzero for each of the ten pairs. In the map from the fifth cyclotomic integers to the field of eleven elements sending ζ to 3, the residues in lexicographic pair order are 3,1,4,5,4,5,9,9,3,1. A nonzero residue proves the original coefficient is nonzero. Hence t = 0, and e₂(b) gives bᵢbⱼ = 0. Thus b is a singleton, say at k.

Project A onto the four coordinates outside k. The same (1,1,2) and (1,1,2,0) coefficients show the image is totally isotropic for both symmetric forms with zero diagonal and off-diagonals 1 and vᵢ+vⱼ, respectively. Denote these forms by M₀,N. The second form follows by subtracting the constant vₖ contribution. A common isotropic plane would make det(sM₀+N) a scalar times a square. In a basis beginning with the plane, the top-left two-by-two block vanishes and the determinant is the square of the off-diagonal block's determinant.

Rotate and rescale the roots so vₖ = 1. Under the same reduction modulo eleven the determinant has coefficients (1,4,4,6,8) in ascending powers. Its monic normalization is s⁴+9s³+6s²+6s+7. In a monic quadratic square the top two lower coefficients force the quadratic to be s²+10s+8, whose squared constant is 9 instead of 7. This rules out a square over ℂ as well: the monic square root's coefficients are determined successively using only division by two and by the leading coefficient of the determinant, both invertible in the reduction. Thus the projection of A has dimension at most one.

Since dim A ≥ 2, A is a plane containing eₖ. If x is an independent vector, e₄(x+s eₖ) = 0 gives both e₃ and e₄ zero on its four entries outside k. At most two such entries can be nonzero. Their e₂ is zero by the first projected form, leaving at most one. Therefore A is exactly a coordinate plane and its opposite is zero.

To finish, if d₂ > 0 and an odd space has dimension at least two, the dimensions are bounded by 1+2+1+0 = 4. If both odd dimensions are at most one, the bound is immediate. If d₂ = 0, opposite planes cannot coexist, and a three-dimensional odd space contains two axes and has zero opposite. These cases exhaust the possibilities.

For attainment take all matrices X with Xᵣⱼ = uᵣζʲ and arbitrary four row amplitudes u. This four-dimensional space is invariant under row permutations. Cyclically permuting columns multiplies X by ζ while preserving F. Each nonconstant homogeneous term has degree between one and four, so each vanishes. This proves sharpness.
