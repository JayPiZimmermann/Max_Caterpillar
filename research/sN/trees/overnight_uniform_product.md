# Actual sheared-product operations

The unrestricted matching separator remains open. The live requirement is a
linear operation on the actual rational kernel, including every apex placement.
The two-shuffle factorization in the frozen pruning note is available; a
factor-by-factor signed reinterpretation still needs a descent argument.

## Direct doubled Vandermonde: exactly refuted

At five labels, write

\[
 \omega=(-x_1-x_2-x_3-x_4,x_1,x_2,x_3,x_4),\qquad
 \Delta(\partial)=\prod_{i<j}(\partial_j-\partial_i).
\]

The natural candidate is the actual linear differential operation

\[
 \mathcal V(R)=
 \left.\Delta(\partial)^2R(\omega)\right|_{x=(1,1,1,1)}.
\]

It is defined on the subspace analytic at that point. Both the maximum and
each apex placement of the following star are in this subspace:

\[
 U=\sigma(x_1-x_0+\sigma(x_2-x_1)+\sigma(x_3-x_2)+\sigma(x_4-x_2)).
\]

For the unaveraged full permutation sum \(F_U\), exact calculation gives

\[
 \mathcal V(M)=-864,\qquad
 \mathcal V(F_U)=-\frac{86380735795}{2834352}\ne0.
\]

Thus even the restricted tree factors do not rescue the naive doubled
Vandermonde bridge. Extending the operator to kernels singular at this point
cannot remove this analytic-star counterexample while preserving its value
on the analytic subspace.

The target value also has a short independent formula. The differential
operator commutes with multiplication by a function of \(\sum x_i\). Therefore

\[
 \mathcal V(M)=-\frac14\int_{\mathbb R_+^4}
                  \Delta(t)^2e^{-\sum_i t_i}\,dt
 =-\frac{4!}{4}\det[(i+j)!]_{i,j=0}^3=-864.
\]

Expanding both Vandermonde determinants and integrating each monomial proves
the determinant formula directly.

The star calculation uses exact polynomial moments. For linear denominator
vectors \(v_f\), write \(R(x)=b(x)\prod_f(v_f\cdot x)^{-1}\). Put

\[
 P(z)=\Delta(z)^2,\qquad z=\sum_f t_fv_f.
\]

Then at \(x=\mathbf1\), the needed formal moment polynomial is

\[
 b(\mathbf1)P(z)-\nabla b\cdot\nabla_z P(z),
\]

with a monomial \(\prod_f t_f^{k_f}\) assigned the exact moment
\(\prod_f k_f!/(v_f\cdot\mathbf1)^{k_f+1}\).
The formula follows either by differentiating inverse linear forms or by
formal exponential integration, and remains an algebraic identity when some
rates are negative. Every rate in the tested kernels is nonzero.

The producer evaluates all five choices of the label carrying the negative
frequency, multiplies by (4!), and checks the result again using normalized
heads in place of rooted edge cuts. It completes in under one second:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 research/sN/dfs/h4-general-neurons/venv/bin/python research/sN/trees/overnight_uniform_product_vandermonde.py
```

No claim about another differential operator, a relative operation retaining
attachment data, or the actual all-tree lower bound follows from this failure.
