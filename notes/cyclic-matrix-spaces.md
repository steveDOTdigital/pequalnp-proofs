# Cyclic symmetries in the four-by-five permanent problem

Cyclic column symmetry alone bounds the dimension by **six**. If the space also respects cyclic row shifts, its largest possible dimension is **four**. Without imposing invariance on an extension, a full column Fourier mode is also inclusion-maximal. These results concern L-gct-179, which asks for a seven-dimensional space with no symmetry requirement.

Write F(X) for the sum over injections from rows to columns of the products of the selected entries of the all-ones matrix plus X. A level space is a complex linear subspace on which F equals F(0).

## Both cyclic shifts

Take primitive roots of unity of orders four and five. The twenty matrices with entries α^(ai) β^(bj), indexed by 0 ≤ a < 4 and 0 ≤ b < 5, are a basis of joint eigenvectors for the two shifts. Each character occurs once. The projections onto these basis lines are weighted averages of the shifts, so every invariant subspace is spanned by a subset of the twenty matrices.

For a multiset of k modes with 1 ≤ k ≤ 4, the corresponding coefficient in F is a nonzero rational multiple of the product of two sums. The row sum ranges over ordered distinct row indices and multiplies the k row characters there. The column sum does the same with the k column characters. To see this, label the k selected factors in each partial matching. The row and column choices are then independent. Each partial matching has the same number of full extensions, and removing labels for repeated modes divides by a positive integer.

Both sums are integers. Removing the last frequency lets its index range freely and subtracts one collision term for each earlier index. The collision events are disjoint because the earlier indices are distinct. At a collision the two frequencies add modulo the group order. The unrestricted sum of the last character is the group order for frequency zero and vanishes otherwise. This recurrence covers repeated frequencies as well.

The [exact enumeration](check-cyclic-matrix-spaces.py) counts 16, 76, 80, and 16 level subspaces in dimensions one through four, respectively. All five-element subsets contain an obstruction. Every larger subset contains a five-element subset. Four independent row amplitudes times a fixed nontrivial column character attain the bound.

## Extensions of one column Fourier mode

For any p ≥ 2 and q = p + 1, let ζ be a primitive q-th root of unity. Let U contain the matrices with entries aᵢ ζʲ for arbitrary row amplitudes aᵢ. Its dimension is p. A cyclic column shift acts on U by a single primitive scalar. Invariance of F under the shift makes every homogeneous term of degree 1 through p vanish on U, since all these degrees are less than q.

Suppose a level space contains U and X. Fix a set I of k rows, with 1 ≤ k ≤ p − 1. In F(sX + U(a)), extract the coefficient of s times the product of the distinct amplitudes indexed by I. If X contributes in column j, the Fourier factors use k distinct columns other than j. Their sum over ordered choices is k! times the k-th elementary symmetric function of all q-th roots except ζʲ. Dividing the identity ∏(1 + ζˡt) = 1 − (−t)^q by 1 + ζʲt shows this is k!(−ζʲ)^k. Completing the remaining rows multiplies every term by the same positive integer. Vanishing of the coefficient therefore gives

    Σ_{i outside I} Σ_j X[i,j] ζ^(kj) = 0.

For fixed k, exchanging one row of I with one outside it shows that all row sums in this display are equal. Since p − k is positive, all are zero. As k runs from 1 through q − 2, these equations eliminate every column frequency other than zero and one. Subtracting a member of U leaves a matrix R in the level space with entries constant along each row. If those constants are rᵢ, then F(tR)/F(0) = ∏(1 + t rᵢ). Any nonzero rᵢ supplies a root, contradicting the constant value one. Thus R vanishes and X belongs to U.

## A cyclic column shift alone excludes dimension seven

Let L be invariant under the five-cycle of columns, with arbitrary behavior under row permutations. Then **dim L ≤ 6**. The proof uses one exact Gröbner basis calculation over the rationals.

Averaging the powers of the column shift with character weights splits L into frequency spaces V₀ through V₄. A vector a in Vᵢ represents the matrix with entries aᵣ ζ^(ij). Each Vᵢ is a subspace of ℂ⁴. The row-constant argument above gives V₀ = 0. Relabelling columns by multiplication modulo five lets any chosen nonzero frequency play the role of frequency one.

For a multiset of frequencies, the column factor in its polarized coefficient is the ordered distinct-index sum described above. For (1,4), (1,1,4,4), (1,1,3), (1,1,1,2), and (1,2,2) it is respectively −5, 20, 10, −30, and 10. Each associated row coefficient must therefore vanish. Overall nonzero multiplicities from ordering repeated factors do not affect these equations.

**Opposite frequencies.** Write A = V₁, B = V₄ and M = J − I, with J the four-by-four all-ones matrix. The quadratic coefficient says aᵀMb = 0 for every a in A and b in B. Since M is invertible, dim A + dim B ≤ 4. In fact the dimensions cannot both be two. If they were, a row permutation puts A in the chart

    a = (x, y, px + qy, rx + sy).

Then B is the image under J − 3I = 3M⁻¹ of the span of (−p,−q,1,0) and (−r,−s,0,1). The quartic coefficient requires

    Σ aᵢaⱼ bₖbₗ = 0,

where the sum ranges over the six unordered pairs {i,j}, with {k,l} the complementary pair. This polynomial is homogeneous of degree two in each plane's coordinates. Evaluating each coordinate pair at (1,0), (0,1), and (1,1) therefore gives nine necessary and sufficient equations. Their reduced Gröbner basis over ℚ[p,q,r,s] is [1]. The equations consequently have no common complex solution. Every plane has some nonzero two-coordinate minor, and the row permutation acts on both planes, so the chart covers every case up to this symmetry. [Reproducible exact calculation](check-opposite-column-planes.py)

**A three-dimensional frequency.** Suppose V₁ is the hyperplane h(a) = 0. The opposite space V₄ has dimension at most one. Both V₃ and V₂ also have dimension at most one, as follows.

For b in V₃, the (1,1,3) coefficient says that the quadratic

    Qᵦ(a) = Σ aᵢaⱼ (bₖ + bₗ)

vanishes on h = 0, using the same complementary pairs. Thus h divides Qᵦ. The quadratic is squarefree in each variable, so the linear quotient uses only coordinates outside the support of h. This follows by adding degrees in each individual variable in a nonzero product. The map b ↦ Qᵦ is injective, since the six pair sums determine b.

If h uses all four coordinates, the quotient is zero. If it uses one or three, the three coordinates on the larger side have all their internal pair coefficients zero. This forces each of their b entries to equal the negative of the fourth entry. If h uses exactly coordinates 1 and 2, the two internal pair coefficients give b = (u,−u,v,−v). The coefficients of a₁a₃ and a₂a₃ must be proportional to (h₁,h₂), so h₂(−u−v) = h₁(u−v). This gives a nonzero linear constraint on u,v, since h₁+h₂ and h₁−h₂ cannot both vanish. In all cases dim V₃ ≤ 1.

For b in V₂, the (1,1,1,2) coefficient implies that h divides the cubic Σᵢ bᵢ ∏ⱼ≠ᵢ aⱼ. This map from b to cubics is injective. Its squarefree quadratic quotient uses only coordinates outside the support of h. If h uses at least two coordinates, the quotient space has dimension at most one. Otherwise permute rows so h = a₄ up to scale. Divisibility then gives b₄ = 0. The (1,2,2) coefficient with a equal to each of the first three coordinate vectors forces b₁b₂ = b₁b₃ = b₂b₃ = 0. A linear space contained in the union of three coordinate lines has dimension at most one. This proves the bound on V₂.

Finally, a frequency of dimension four already gives a maximal space by the preceding section. A frequency of dimension three gives total dimension at most 3 + 1 + 1 + 1. If every frequency has dimension at most two, each of the two opposite pairs contributes at most three because the (2,2) case is impossible. Thus a seven-dimensional witness must break cyclic column symmetry.
