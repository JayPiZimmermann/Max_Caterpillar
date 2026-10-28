# Independent review: seven-label matching separator gives a quartic bound

24 October 2026. This is a review of the bridge from the root agent's exact
seven-label matching separator. It does not independently recheck that finite
separator and is not a Lean theorem.

Assume the certified seven-label separator annihilates every canonical rooted
oriented tree unit whose six-vertex inner tree has matching number at most two,
while taking a nonzero value on the seven-input maximum. It acts on the top
quotient, so lower-dimensional terms are also annihilated.

Consider any exact expansion of `max_N` by canonical tree-face units and the
paper's auxiliary span, with `N≥7`. All orientations and all five edge states
are allowed. Apply the existing canonical-germ reduction at each seven-label
tie, with one fixed separated outside ordering for that tie. Its nonzero top
germs have their fixed apex in the tie, and their retained hinges form a
connected tree on the other six tied labels. The germ head is again canonical.

The separator forces at least one contributing germ whose six-vertex tree has
a perfect matching. This matching consists of three original-tree edges.
For a fixed original unit, assign one such matching to every tie it covers.
The endpoints of the matching recover the six nonapex tied labels, and the
unit's fixed apex recovers the seventh. Hence the assignment is injective.
No root, permutation, outside-order, or unmatched-vertex factor is needed.

Write `m_k(F)` for the number of size-`k` matchings in a forest on `n` vertices.
For a leaf `v` with neighbour `u`,

\[
m_k(F)=m_k(F-v)+m_{k-1}(F-u-v)
\le\binom{n-k-1}{k}+\binom{n-k-1}{k-1}
=\binom{n-k}{k}.
\]

The induction handles an isolated vertex by deleting it without a second
summand; `m_0=1`, and impossible matching sizes contribute zero. Consequently
`m_3(F)≤binom(N−4,3)` for an original tree on `N−1` vertices.

Double counting gives the stronger weighted inequality

\[
\sum_{\text{units }j}m_3(T_j)\ge\binom N7.
\]

In particular,

\[
\boxed{
|K|\ge\frac{\binom N7}{\binom{N-4}3}
=\frac{N(N-1)(N-2)(N-3)}{840}
=\frac{\binom N4}{35}.}
\]

The integer lower bound can be rounded upward. Original trees of matching
number at most two contribute zero to the weighted inequality and may be
added freely. Signed output coefficients cause no difficulty: a nonzero
separator value of the target forces at least one term with nonzero separator
value at each tie, regardless of cancellation among other terms.

The scope is the canonical tree-face dictionary. The argument does not extend
automatically to arbitrary real heads, arbitrary edge weights, or graphs with
cycles. For face states, connectedness of the retained six-vertex germ forces
all edges of the induced original subtree to be retained; omitted or linear
states can only remove eligible ties. The existing canonical-head germ bridge
is essential and must remain part of the theorem's dependency record.
