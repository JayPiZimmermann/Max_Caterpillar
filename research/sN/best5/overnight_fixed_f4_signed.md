# The signed relations in the finite Hadamard orbit

This addendum classifies all linear combinations of the 48 orbit functions
that are shallow. It does not produce a maximum construction.

Write

\[
 A_1=\frac12\begin{pmatrix}1&-1&-1&-1\\1&-1&1&1\\1&1&-1&1\\1&1&1&-1\end{pmatrix},
 \qquad
 A_2=\frac12\begin{pmatrix}1&-1&-1&1\\1&-1&1&-1\\1&1&-1&-1\\1&1&1&1\end{pmatrix}.
\]

Let \(A_0=I\), and let \(E_\varepsilon(x)\) be the sum of the eight
functions \(q(s_1x_1,\ldots,s_4x_4)\) with
\(\prod_i s_i=\varepsilon\). Equivalently, it is
\(\min_i|x_i|\) on orthants of sign parity \(\varepsilon\), and zero on
the other orthants. At the boundary both descriptions give zero.

The following three identities hold globally:

\[
\begin{aligned}
 E_+(x)-E_+(A_2x)&=\tfrac12(\|x\|_1-\|A_2x\|_1),\\
 E_-(x)-E_+(A_1x)&=\tfrac12(\|x\|_1-\|A_1x\|_1),\\
 E_-(A_2x)-E_-(A_1x)&=\tfrac12(\|A_2x\|_1-\|A_1x\|_1).
\end{aligned}
\]

Each is a relation among sixteen distinct orbit functions and a shallow
function. Their three supports partition the 48-function orbit.

## Short proof of the identities

Selecting the best sign vector of prescribed parity gives

\[
 E_+(x)=\tfrac12\|x\|_1-\|A_1x\|_\infty,\qquad
 E_-(x)=\tfrac12\|x\|_1-\|A_2x\|_\infty.
\]

Indeed, if the maximizing unrestricted sign vector has the wrong parity,
the best permitted choice changes the sign of a coordinate of minimum
absolute value. If it already has the permitted parity, no coordinate
changes. The eight odd-parity sign vectors are precisely the signed rows
of \(2A_1\); the eight even-parity vectors are the signed rows of
\(2A_2\).

Up to signed row permutations,

\[
 A_1A_2=A_1,\qquad A_1^2=A_2,\qquad
 A_2^2=I,\qquad A_2A_1=I.
\]

These equations mean equality of the sets of signed rows, not equality of
the matrices. The corresponding infinity norms are equal, and substitution
in the preceding formulas proves all three identities.

## Completeness

Apply all group transforms of the seven-point functional from
`overnight_fixed_f4.md` to a shallow combination \(\sum_Qw_Q Q\).
Each transformed functional has value proportional to
\(w_Q+w_{Q'}\) for a pair of orbit functions. The resulting graph has
48 vertices and 96 edges. It is the disjoint union of three connected
bipartite graphs of sixteen vertices each. Consequently every shallow
combination has alternating coefficients on each component, determined by
one scalar per component.

The three displayed identities supply those three independent alternating
coefficient vectors. They therefore generate **every** shallow relation
among the orbit functions, even when the shallow representation is allowed
arbitrary first hidden layer directions. For the latter statement, any
consolidated wall outside the orbit's 24 potential walls has zero gradient
jump and hence zero coefficient.

The three right sides span a two-dimensional space. The three norms
\(\|A_ix\|_1\) are linearly independent because their wall sets are
nonempty and disjoint. The combination first identity minus second plus
third has zero right side and gives the unique global linear dependence
among the 48 functions. Thus:

- the coefficient space of relations modulo shallow functions has dimension 3;
- the span of the 48 functions has dimension 47;
- its intersection with the shallow functions has dimension 2;
- its quotient by shallow functions has dimension 45.

## Exact verification

`overnight_fixed_f4_signed_verify.py` uses standard-library rational and
integer arithmetic. It constructs the group action on the 48 functions,
computes the 96-edge orbit, verifies the three connected bipartite
components, and matches their alternating vectors to the displayed
identities. It also checks the signed row identities proving the norm
formulas. It imports only the exact matrix helpers from the frozen
`overnight_fixed_f4_verify.py`; it does not use numerical ranks or read the
exploratory proposal file.

The signed relations explain precisely what the positive-fold obstruction
leaves available in this finite family. They alone do not isolate a single
\(q\) function or yield a finite outer-ReLU construction.
