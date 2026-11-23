# Two eight-dimensional bounds for the five-by-five permanent

Let J be the all-ones matrix. L-gct-210 asks whether every complex linear space L on which per(J + X) = 120 has dimension at most eight. The bound holds if L is invariant under complex conjugation or if L is invariant under any five-cycle of the rows or columns.

## Complex conjugation

The linear coefficient in per(J + tX) says that the sum of all entries of X is zero. The quadratic coefficient gives a symmetric bilinear form that vanishes on L × L by polarization. Up to a positive factor, its matrix is M ⊗ M, where M = J − I in dimension five. Two positions pair with coefficient one precisely when both their row and column indices differ.

Over the reals M has eigenvalue 4 on constant vectors and −1 on their four-dimensional orthogonal complement. On the hyperplane of matrices with total sum zero the tensor product thus has eight negative directions and sixteen positive directions. Projection onto its negative subspace is injective on every real totally isotropic space: a vector in the kernel would have strictly positive square unless it were zero. This gives a bound of eight real dimensions. If L is invariant under conjugation, every vector of L is the sum of a real vector in L and i times another real vector in L. Its complex dimension therefore equals the dimension of its real part and is at most eight.

## A five-cycle of the columns

Relabel columns so the cycle adds one modulo five. Let ζ be a primitive fifth root of unity. The shift preserves L, so the five Fourier projections, which are linear combinations of powers of the shift, preserve L. For each k modulo five, write Aₖ for the subspace of vectors a for which Xᵢⱼ = aᵢ ζ^(kj) belongs to L. The spaces give a direct sum and dim L = Σ dim Aₖ.

For k = 0 the permanent on the line through X is 120 times the product of (1 + taᵢ) over the five rows. Constancy forces every aᵢ to be zero. For any k ≠ 0 the degree-five coefficient is 120 times the product of all aᵢ, because each permutation uses all five columns and ζ to the power 10k is one. The product therefore vanishes identically on Aₖ. A polynomial ring on a complex vector space is an integral domain, so some coordinate vanishes on all of Aₖ.

Take a ∈ Aₖ and b ∈ A₋ₖ. The coefficient using one entry from each vector in the permanent at J is −30 times aᵀMb. For each ordered pair of different rows, their two column indices j and l differ. The sum of ζ to the power k(j − l) over j ≠ l is −5, and each choice extends to six permutations. Hence Aₖ and A₋ₖ are orthogonal for the invertible pairing M, and their dimensions sum to at most five.

Equality would imply Aₖ = (M A₋ₖ)⊥ under the ordinary complex bilinear dot product. Choose a coordinate j vanishing throughout A₋ₖ. Then M⁻¹eⱼ belongs to Aₖ. But M⁻¹ = J/4 − I, so every coordinate of this vector is nonzero. This contradicts the coordinate constraint on Aₖ. Each opposite pair therefore contributes at most four dimensions. The pairs {1,4} and {2,3} together give the bound of eight. Transposing the matrix proves the row-cycle case.

In particular, a nine-dimensional counterexample would need genuinely complex directions and would have to break every row five-cycle and every column five-cycle. The proof allows arbitrary subspaces inside each Fourier eigenspace.
