# Actual function relations and the surviving quadratic score

Status: proof-search results. The unrestricted exponential lower bound is
still open. No statement in this note supplies a uniform separator.

## What is proved and what failed

The exact local six-term grafting identity disproves the earlier score
\(Q_*\), as recorded in overnight_uniform_q9.md.
The present branch tests the **same** previously defined 288 features;
it introduces no extra feature or arity-dependent coefficient.

All 32,252 local graft identities at arities \(5,7,9\) were generated.
Their exact constraint rank is 155. An integer basis of the
133-dimensional coefficient nullspace was checked against every constraint,
with an explicit bound excluding integer overflow. The 133 parameters
include many formulas giving the same or zero assignments on these trees.
The assignment dimensions measured modulo 1000003 are \(2,4,10\) at the
three arities, and 16 jointly. Only these last dimensions are modular.

Two known five-label whole-kernel identities, together with those local
constraints, force the five-label target response to vanish. This is a
restriction on a common formula across the three arities, not a reason to
abandon a separator that begins at a larger odd arity.

A first four-feature survivor was

\[
 Q_1=\epsilon\left[
 \frac23\left(\sum_v d_v I_v\right)^2+
 2\left(\sum_v\chi_vd_vI_v\right)^2
 -\frac{10}{3}D_1+G_1\right].
\]

Here \(d_v\) is the vertex degree, \(I_v\) is the signed number of rooted
tree extensions, \(\chi\) is a bipartite sign, and

\[
 D_1=\sum_{v,w}\operatorname{dist}(v,w)I_vI_w,\qquad
 G_1=\sum_{v,w}\operatorname{dist}(v,w)(d_v+d_w)I_vI_w.
\]

It has a nonzero necessary maximum response from nine labels onward,
but it **fails** the exact twelve-term whole-function identity below.
Its discrepancy is \(-2048/3\).

## The twelve-term identity is an identity of the original functions

The twelve signed root/edge declarations are in
overnight_uniform_fay_relation12.txt. Each denotes the unaveraged sum over
all \(9!\) label permutations of its full canonical tree unit.
Their signed sum is identically zero on all real inputs.

This is stronger than a generic Fourier identity. On the chamber
\(x_0<\cdots<x_8\), each first hidden layer expression is linear. Write its
outer preactivation in the positive gaps \(x_k-x_{k-1}\). A form with all
gap coefficients nonnegative is linear there; one with all nonpositive
coefficients contributes zero. For every remaining form, normalize its
coefficient vector up to sign and use
\(\sigma(-t)=\sigma(t)-t\). The resulting 3717 distinct mixed walls all
have total coefficient zero, and the residual linear function is zero.
Permutation symmetry and continuity prove the identity everywhere.

The independent standard-library checker
overnight_uniform_fay_function_verify.py enumerates every label
permutation and directly builds the gap coefficients from intervals.
It imports neither a Fourier evaluator nor a matrix or score producer.
It passed in 16.65 seconds. A separate C++ aggregation in coordinate
coefficients gives the same result. The independent score checker
overnight_uniform_fay_relation_score_verify.py directly enumerates the
signed rooted orders and obtains the discrepancy \(-2048/3\) for \(Q_1\).

The identity was first suggested by a modular row-space test. The proof
above does not use the rank, sampled frequencies, or a presumed rank
stabilization.

## A surviving fixed formula

Put

\[
 B=\sum_v\chi_vd_vI_v,\qquad
 H_2=\sum_{v,w}\operatorname{dist}(v,w)^2d_vd_wI_vI_w.
\]

The same old feature alphabet contains

\[
 \boxed{Q_2=\epsilon\left(2B^2+\frac32D_1-\frac54G_1+H_2\right).}
\]

The score vanishes on trees without a perfect matching because every
\(I_v\) then vanishes. It is label-invariant since a relabeling changes
all signed rooted counts by the same sign.

Both \(Q_1\) and \(Q_2\) have the form \(\epsilon F(T)\), with \(F\)
depending only on the unoriented tree. Therefore they satisfy **every**
local six-term graft identity at every size: the two star terms have the
same orientation product and cancel, and the two terms on each path shape
also have the same orientation product and cancel.
This observation applies to arbitrary attached subtrees and requires no
finite-rank inference.

They also respect the whole-function root slide
\(x_r+\sigma(x_s-x_r)=x_s+\sigma(x_r-x_s)\).
The underlying tree stays fixed; reversing the traversed edge while moving
the root leaves every root-relative orientation sign unchanged. Thus
\(\epsilon\) is unchanged. Equal normalized \(\kappa\) descriptions on
a fixed tree differ by such path slides, by uniqueness of flow on a tree.

\(Q_2\) survives the twelve-term identity exactly. On the cached nine-label
PM-plus-star matrix, the entire feature family gains only that one
additional constraint after the earlier five- and seven-label gates.
This is still a **necessary modular diagnostic** about that matrix.
It does not cover arbitrary matching-deficient nonstar columns, and it is
not a descent proof for \(Q_2\).

## The eventual target response does not vanish

The signed caterpillar identity determines a necessary response if a score
descends. Write \(N=2q+1\). The perfectly matchable caterpillars are indexed
by bits \(b_1,\ldots,b_q\), with matching pairs \((a_j,c_j)\), and

\[
 C_j=\binom{q-1}{j-1},\quad
 s_j=(-1)^{b_1+\cdots+b_{j-1}},\quad
 I_{a_j}=s_jC_j,\quad I_{c_j}=-s_jC_j.
\]

Their construction coefficient equals their orientation product
\(\epsilon\). Consequently the signed sum of \(\epsilon F(T)\) is
\(2^q\) times the uniform Boolean-cube average of \(F\).
Set
\(A_d=\binom{2q-2}{q-1-d}\), with out-of-range binomial coefficients zero,
and \(A_0=\binom{2q-2}{q-1}\).
For \(q\geq3\), direct moment calculation gives

\[
\begin{aligned}
 B^2&=2(1-(-1)^q),\\
 \mathbb E D_1&=-2A_0,\\
 \mathbb E G_1&=-8A_0+4-4A_1,\\
 \mathbb E H_2&=-7A_0-7A_1+A_2+A_3+
                 6-(q-1)(q-2).
\end{aligned}
\]

For the last identity, the within-pair contribution is \(-7A_0+6\).
For pairs separated by \(d\), the Boolean sign character annihilates every
cross-pair contribution when \(d\geq4\).
The mean unordered contributions for \(d=1,2,3\), divided by \(C_jC_{j+d}\),
are respectively \(-7/2,1/2,1/2\) in the interior.
At \(d=2\), each endpoint boundary lowers the coefficient by \(1/2\).
The \(d=1\) double-endpoint exception occurs only at \(q=2\).
Vandermonde's identity sums these three diagonals, giving the formula.

It follows that the signed sum is

\[
 S_q=2^q\left[
 5-4(-1)^q-(q-1)(q-2)-2A_1+A_2+A_3\right].
\]

It is zero at \(q=3\), and the separate \(q=2\) calculation is zero too.
For every \(q\geq4\), it is strictly negative:
\(A_1>A_2\geq A_3\), and
\(5-4(-1)^q-(q-1)(q-2)<0\).
The first three nonzero sums are \(-448,-2528,-17536\).
The necessary maximum response is \(S_q/(2q+1)!\).

Thus the target sequence of the remaining fixed feature space does not
vanish identically or eventually. What remains missing is an actual linear
operation on functions or rational kernels whose evaluation is \(Q_2\).
Local grafting and root slides are not known to present all the global
relations, especially those involving different apex placements.

## Structural continuation

The pure orientation channel of a rooted edge is
\[
 f_+(z)-f_-(z)=-\frac{2a}{z(z^2-a^2)}.
\]
In edge coordinates, the corresponding signed orientation sum of units is
a full finite difference of the outer ReLU, of box-spline type. This is
an actual-function interpretation of the channel, but no global apex
compatibility theorem has been established.

The new continuous four-corner crease functional used in the minimum
first-hidden-layer problem is another actual-function construction.
Its immediate extension to arbitrary tree units has an additional term:
edges joining different coordinate blocks create first hidden layer walls
inside the product cones. An aggregated curvature operation must retain
these extra jumps. A fixed prescribed matching cannot be imposed, as the
exact noncrossing construction already rules out that stronger condition.
