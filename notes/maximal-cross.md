# The standard cross is maximal in every rectangular size

Let 3 ≤ p ≤ q. For a complex p-by-q matrix X, let F(X) be the sum over injections from rows to columns of the products of the selected entries of 1 + X. The 1 here is the all-ones matrix. A level space is a linear subspace on which F is constant.

Let U consist of matrices supported on row 0 and column 0 such that the entries of row 0 **outside** column 0 sum to zero, and the entries of the **entire** column 0 sum to zero. Then U has dimension p + q − 3 and **every level space containing U equals U**. This rules out enlarging this particular construction. The maximum dimension among other level spaces remains open.

## The level identity

The row entries outside column 0 give q − 2 parameters, and column 0 gives p − 1. Each injection uses at most two cross entries. In the expansion of F, all linear terms have the same coefficient and the total entry sum is zero. A quadratic term must use one entry of row 0 outside column 0 and one entry of column 0 outside row 0. Every such pair has the same coefficient, and its sum vanishes by the row condition. Thus F is constant on U.

## Constraints on an extension

Suppose X belongs to a level space containing U. In the expansion of F, a choice of k entries in distinct rows and distinct columns has a coefficient equal to the number of injections extending that choice. For k ≤ 3 this is a positive integer depending only on p, q and k. We cancel these common factors below.

Take A supported on row 0 with entries aⱼ in columns j > 0 summing to zero. Take B supported on column 0 with entries bᵢ at rows i > 0 and entry −Σbᵢ at row 0. Each bᵢ is free. The coefficient of str in F(sX + tA + rB) vanishes. Once A uses column j and B uses row i, the entry from X must avoid rows 0 and i and columns 0 and j. Hence

    Σᵢ bᵢ Σⱼ aⱼ Σ_{k > 0, k ≠ i} Σ_{ℓ > 0, ℓ ≠ j} X[k,ℓ] = 0.

For each i > 0, taking a difference of two columns j and j′ gives

    Σ_{k > 0, k ≠ i} (X[k,j] − X[k,j′]) = 0.

Write Dₖ = X[k,j] − X[k,j′]. These equations give Dᵢ = ΣDₖ for every i > 0. Summing yields (p − 2)ΣDₖ = 0, so every Dₖ is zero. Each positive-index row is therefore constant outside column 0.

The coefficient of sr in F(sX + rB) also vanishes. Put Rᵢ = Σ_{j > 0} X[i,j]. The contribution from bᵢ in row i and −bᵢ in row 0 is bᵢ(R₀ − Rᵢ). Consequently all Rᵢ equal R₀. The entire lower-right block of X is now one scalar d, and R₀ = (q − 1)d. The linear coefficient in F(sX) gives ΣX[i,j] = 0.

Let V have every row equal to (−(q − 1), 1, …, 1). The preceding equations say exactly that X − dV belongs to U. If d were nonzero, V would belong to the level space. A fraction p/q of injections use column 0. Splitting the sum according to whether they do gives

    F(tV) / F(0) = (1 − (p − 1)t)(1 + t)^(p − 1).

At t = −1 this is zero, whereas at t = 0 it is one. Hence d = 0 and X belongs to U.

The [four-by-five exact-arithmetic certificate](check-cross-extension.py) gives a separate finite verification in the first assigned size.
