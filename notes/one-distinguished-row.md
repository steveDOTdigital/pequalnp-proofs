# The sharp permanent bound with one distinguished row

Let n ≥ 3, let J be the n-by-n all-ones matrix, and let L be a complex linear space of matrices with per(J + X) = n! for every X in L. Suppose a group of row permutations preserves L, fixes one distinguished row, and acts transitively on the ordered pairs of distinct remaining rows. Then

    dim L ≤ 2n − 3.

Equality is attained in every size. The same statement holds for columns by transposition. This proves a symmetry-restricted case of L-gct-086 using Taylor degrees up to n − 1.

## Decomposing the row action

Call the other m = n − 1 rows ordinary. Averaging the group action gives a projection onto L₀, the part of L in which the ordinary rows are equal. The complementary subspace L₁ has zero distinguished row and its ordinary rows sum to zero as row vectors.

Write U for the (m − 1)-dimensional space of ordinary-row amplitudes with sum zero. The group-invariant subspace L₁ of U ⊗ ℂⁿ has the form U ⊗ B for some space B of column amplitudes. To see this, take the orthogonal projection onto L₁ for the usual Hermitian inner product. It commutes with the row action, which is unitary. Each block of this projection, from the U of one column to the U of another, extends by zero on constant vectors to a commuting map on ℂᵐ. Its entries are constant on the diagonal and constant off the diagonal by the ordered-pair hypothesis. Such a map acts as a scalar on U. Therefore the projection acts as the identity on the U factor tensored with one map on the column factor. Its image has the asserted form.

## At most one column amplitude

Write eₖ for the elementary symmetric polynomial and pₖ for the sum of kth powers. For a rank-one direction with entries aᵢbⱼ, the coefficient of tᵏ in per(J + t abᵀ) is

    k! (n − k)! eₖ(a) eₖ(b).

Indeed, choose the k rows and columns, a bijection between them and a permutation of the remaining positions. For every k from 2 to n − 1, take a in U with exactly k nonzero entries, k − 1 of them equal to one and the last equal to 1 − k. Extend by zero on the distinguished row. Then eₖ(a) is nonzero. Consequently e₂ through eₙ₋₁ vanish identically on B. Newton's identities give pₖ(b) = p₁(b)ᵏ for 1 ≤ k ≤ n − 1.

Suppose dim B ≥ 2 and choose a nonzero v in B with p₁(v) = 0. All its elementary symmetric polynomials through degree n − 1 vanish. The polynomial with roots vⱼ therefore has the form Tⁿ + constant. The constant is nonzero because v is nonzero. In particular all n coordinates are distinct, and their sums of powers 1 through n − 1 vanish.

For arbitrary u in B, differentiate pₕ₊₁(v + tu) = p₁(v + tu)ʰ⁺¹ at t = 0 for 1 ≤ h ≤ n − 2. This gives Σⱼ uⱼ vⱼʰ = 0. The n − 2 vectors with coordinates vⱼʰ in these equations are independent by the Vandermonde determinant. Their common orthogonal complement for the bilinear dot product has dimension two and contains both the constant vector and v. Write u = α1 + βv. Since both p₁(v) and p₂(v) vanish, the equality p₂(u) = p₁(u)² becomes nα² = n²α². Hence α = 0. This puts every u in the line spanned by v, a contradiction. We have dim B ≤ 1 and dim L₁ ≤ n − 2.

## The part fixed by the group

Write b for the common ordinary row and c for the distinguished row. Let D be the space of possible b and let N consist of the c occurring with b = 0. Rank-nullity gives dim L₀ = dim D + dim N.

Partition the columns according to equality of the coordinate functionals b ↦ bⱼ on D, and let h count the classes. Then D lies in the h-dimensional space of block-constant vectors. It cannot contain the all-ones vector: for any such b and its lift c, scaling by −1 would give zero ordinary rows in J + X, hence zero permanent. Thus dim D ≤ h − 1.

Choose a b in D whose entries distinguish its h classes. Such a choice avoids finitely many proper hyperplanes over ℂ. For u in N, vary the distinguished row alone in direction u while scaling a lift of b by t. Expanding the permanent along the distinguished row and taking the coefficient of this variation gives

    Σⱼ uⱼ ∏ₗ≠ⱼ (1 + t bₗ) = 0.

After dividing by the product of all (1 + t bₗ), this is the rational identity Σⱼ uⱼ/(1 + t bⱼ) = 0. Grouping equal values shows that the sum of u on each class is zero. Indeed the functions 1/(1 + tλ) for the distinct nonzero values λ have distinct simple poles, and a possible λ = 0 contributes only the constant function. These are h independent constraints on u, so dim N ≤ n − h. This proves dim L₀ ≤ n − 1 and the claimed upper bound.

For equality, allow entries only on the distinguished row and one chosen column. Require the distinguished-row entries outside that column to sum to zero, and the full chosen column to sum to zero. The two conditions give dimension 2n − 3. Each permutation uses at most two variable entries, and the conditions cancel both the linear and quadratic terms. This space is invariant under every permutation of the ordinary rows. [General cross construction](maximal-cross.md)
