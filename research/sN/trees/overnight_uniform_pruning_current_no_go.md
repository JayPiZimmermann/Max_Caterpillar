# No matching separator of the odd-root current form

**Exact negative result for a proof architecture, already at five labels.**
There is no permutation-invariant linear functional on the generic Fourier
kernel space that detects the maximum,
annihilates all canonical oriented stars, and represents every head choice of
each oriented augmented tree by the current formula below. This allows an
arbitrary auxiliary vector for each augmented tree. No Laplacian formula,
polynomial dependence, or equivariance of that vector is assumed.

This refutes the proposed current architecture. It does not refute a general
two-shuffle functional or the unrestricted all-tree exponential lower bound.

## Scope of the current representation

For an oriented tree (B) on five labels, let (J_v) be its signed number of
rooted-away linear extensions at root (v). Suppose there is a zero-sum vector

\[
 K_B\in\mathbb R^5,\qquad \sum_v(K_B)_v=0,
\]

used for **all** choices of the head edge in this fixed oriented tree. For a
head (H=u\to v), let (S_H) sum coordinates on the (u)-side of (B-H).
The proposed functional value on the full permutation sum (F_H) is

\[
 \Lambda(F_H)=S_H(J)(K_u-K_v)-S_H(K)(J_u-J_v). \tag{1}
\]

The normalization of full permutation sums is consistent throughout: there
is no division by (5!). The target kernel is (M=1/\prod_{i=0}^4\omega_i).

## A cherry forces a necessary path value to vanish

Take the oriented augmented tree

\[
 B=\{1\to0,\;2\to1,\;0\to3,\;0\to4\}.
\]

Its rooted signed vector is

\[
 J=(0,0,0,-1,1).
\]

Deleting any of (0,1,2) leaves no perfect matching. At root (3), the only
surviving domino order is ((3,0,4,1,2)), of odd sign; at root (4) it is
\((4,0,3,1,2)\), of even sign. The ordinary incomparable-pair involution
cancels all other orders.

Use first (0\to3), then (0\to4), as the head. The resulting units are
exchanged by permuting labels (3,4), so their full permutation sums agree.
Formula (1), using both zero-sum conditions, gives respectively (K_0) and

\[
 -K_0.
\]

Their common functional value is therefore zero. Up to relabeling, either
unit is

\[
 U_2=\sigma(x_1-x_0+\sigma(x_2-x_1)+\sigma(x_1-x_3)+\sigma(x_4-x_2)).
\]

The unit

\[
 U_1=\sigma(x_1-x_0+\sigma(x_2-x_1)+\sigma(x_3-x_1)+\sigma(x_2-x_4))
\]

has the same full permutation sum: swap (1,2) and (3,4), then use

\[
 x_2+\sigma(x_1-x_2)=x_1+\sigma(x_2-x_1).
\]

Consequently (\Lambda(F_{U_1})=0).

## The maximum is this path modulo stars

For a canonical unit, write (F(r;E)) for its unaveraged full permutation
sum of Fourier kernels, with apex (0), root (r), and ordered inner edges

\[
 E=\{(u,v):\text{ the segment function is }\sigma(x_u-x_v)\}.
\]

Set

\[
\begin{aligned}
 S_0&=F(1;\{(2,1),(3,2),(4,2)\}),\\
 S_1&=F(1;\{(2,1),(3,2),(2,4)\}),\\
 S_2&=F(1;\{(2,1),(2,3),(2,4)\}),\\
 S_3&=F(2;\{(2,1),(3,2),(2,4)\}).
\end{aligned}
\]

All four inner trees are stars. The following is an exact rational identity:

\[
 \boxed{360M+12F_{U_1}-4S_0-3S_1-3S_2-3S_3=0.} \tag{2}
\]

If (\Lambda) vanishes on oriented stars, (2) gives

\[
 \Lambda(M)=-\frac1{30}\Lambda(F_{U_1})=0.
\]

This proves the claimed impossibility. Only one augmented tree was needed;
arbitrary choices of (K_B) elsewhere cannot repair it. A successful
extension must change the current form or allow additional head-dependent
data, then justify head exchange separately.

## Certificate and finite-search provenance

`overnight_uniform_pruning_current_relation_check.py` independently verifies
(2) by normalized heads and all label permutations. It forms a common
multivariate polynomial denominator and checks a zero numerator over

\[
 \mathbb Q(r,s,t),\qquad
 \omega=(1,r,s,t,-1-r-s-t).
\]

Homogeneity extends the identity to every generic frequency. The check uses
601 summands for (2) and no sampled matrix or signed-count recurrence. The
same run verifies the four-unit relation first identified by the finite
matrix gate. Both checks finish in under one second with FLINT.

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 research/sN/dfs/h5-growth/venv/bin/python research/sN/trees/overnight_uniform_pruning_current_relation_check.py
```

The preceding `edge_current_space` search found 122 exact structural equations
of rank 21 on the 26 canonical orbit scores. Intersecting with the saved
exact evaluation space left two dimensions, both with zero target response.
That finite observation motivated (2); the proof above uses the independently
verified rational identity and does not infer a universal identity from
matrix rank.
