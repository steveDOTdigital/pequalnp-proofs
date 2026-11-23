# Cyclic symmetries in the four-by-five permanent problem

The largest complex level space invariant under both cyclic row and cyclic column shifts has **dimension four**. Without imposing invariance on an extension, a full column Fourier mode is also inclusion-maximal. These results concern L-gct-179, which asks for a seven-dimensional space with no symmetry requirement.

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
