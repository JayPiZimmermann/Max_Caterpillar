# The actual two-shuffle product, before choosing a score

For a rooted oriented nonapex tree (T) on (n=N-1) labels, put

\[
 a=\omega_{\mathrm{apex}}=-\sum_{v\in T}\omega_v,
 \qquad d_v=\operatorname{outdeg}_T(v)-\operatorname{indeg}_T(v).
\]

The ordered segment function \(\sigma(x_u-x_v)\) contributes one outgoing
edge at (u). In this note (d) is the signed degree, not a matching defect.
Its total sum is zero. For root (r), define the rooted-tree shuffle function

\[
 \Phi_{T,r}(z)=\prod_{v\in T}
   \frac1{\sum_{w\in\operatorname{subtree}_r(v)}z_w}.
\]

The root itself is included, so its denominator is the full coordinate sum.
Then the canonical Fourier kernel has the exact factorization

\[
 \boxed{R_U(\omega)=(-a)^{N-2}
    \Phi_{T,r}(\omega)\Phi_{T,r}(\omega+a d).}
\]

Indeed, on a root-away edge cut (C_e), the sum of the signed degrees is
the net number of oriented edges leaving that cut, namely its relative
orientation (\varepsilon_e\in\{-1,1\}). The two factors therefore supply
the denominators (q_e) and (q_e+\varepsilon_e a). Each root denominator
is (-a), accounting for the two extra powers in the prefactor.

For arbitrary generic (z), the ordinary rooted-tree shuffle identity is

\[
 \Phi_{T,r}(z)=
 \sum_{\pi\in\operatorname{LE}(T,r)}
   \prod_{j=1}^{n}\frac1{z_{\pi(j)}+\cdots+z_{\pi(n)}}.
\]

Here the root comes first, and every parent precedes its children. One proof
is to integrate the exponential over the rooted order cone. Its nonnegative
edge increments give the subtree denominators; partitioning the same cone
by total coordinate orders gives the sum of suffix denominators. The
identity first holds in the common convergent region and then as a rational
identity. It also follows by the usual shuffle partial fractions.

Consequently the Fourier kernel itself is a double sum over two rooted
linear extensions, with the second frequency vector sheared by the integer
signed-degree vector. This is a concrete generating-function version of the
two-character idea. It does **not** justify replacing the two extension sums
by signed counts: that replacement must still be realized by one linear
operation on the original rational function.

The root-slide identity gives a useful mandatory control. Moving the root
from (r) across an edge (s\to r) simultaneously reverses that edge,
changing the signed degree by (2(e_r-e_s)). The factorization therefore
changes both its rooted shuffle cone and its shear while representing the
same unit. A residue or polarization operation must respect this coupled
change, as well as the full augmented-tree head-exchange identity. The
failed current scores in `overnight_uniform_pruning_edge_current.md` violate
one of these conditions.

This factorization is a uniform rational identity, not a matching separator.
The remaining task is to define an actual residue/polarization operator on
the rational-function space that vanishes on matching-deficient trees and
has nonzero value on (1/\prod_i\omega_i\). No such operator is established
here.

## A genuine Vandermonde operation realizes one signed count

There is a direct linear differential operation behind the signed extension
count. Put (D=n(n-1)/2) and

\[
 \Delta(t)=\prod_{i<j}(t_j-t_i).
\]

Differentiating the convergent cone integral gives

\[
 \left.\Delta(\partial_z)\Phi_{T,r}(z)\right|_{z=\mathbf1}
   =(-1)^D c_n I(T,r),
 \qquad
 c_n=\int_{0<t_1<\cdots<t_n}
        \Delta(t)e^{-\sum_i t_i}\,dt>0.
\]

On each total-order chamber, the exponential at (z=\mathbf1) is invariant
under label permutations and the Vandermonde changes by permutation sign.
Thus all chambers have the same absolute integral, proving the identity.
No signed reinterpretation of a partial-fraction presentation is needed.
For example, gap integration gives (c_2=1/2) and (c_4=3/16).

The double product still requires an additional operation. Applying
\(\Delta(\partial)^2\) to a diagonal product introduces mixed Leibniz terms;
it does not apply one Vandermonde operator separately to each factor.
This cannot be repaired by choosing another constant-coefficient operator
that works for arbitrary factors. To see the obstruction already at four
variables, suppose a homogeneous polynomial symbol (P) of degree 12 had
middle polarization

\[
 [t^6s^6]P(tx+sy)=c\,\Delta(x)\Delta(y),\qquad c\ne0.
\]

Setting (y=x) forces (P) to be a nonzero multiple of (\Delta^2).
But for

\[
 x=(0,0,1,1),\qquad y=(0,1,0,1),
\]

both individual Vandermondes vanish, whereas

\[
 \Delta(tx+sy)=s^2t^2(t^2-s^2),\qquad
 [t^6s^6]\Delta(tx+sy)^2=-2.
\]

This refutes a universal factor-blind differential extraction of the square
of the signed count. The special coupled factors in the actual tree kernel
may still admit a different operation; the calculation does not exclude
that narrower possibility. Their orientation-dependent shear and the
frequency constraint (a=-\sum\omega_v) must remain part of such an argument.
