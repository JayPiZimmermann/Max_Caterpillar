# Exact logarithmic transfer and its finite realization obstruction

This is a uniform algebraic identity and two precise cutoff obstructions.
It does not construct a finite network.

## The completed change of generators

Let $g_e$ denote translation along an oriented edge and $E_e$ its cubical
generator, with $dE_e=g_e-1$. Work in the augmentation completion over
$\mathbb Q$. Put

\[
 \ell_e=\log g_e,\qquad
 J_e=\frac{\ell_e}{g_e-1}E_e.
\]

The quotient is a well-defined power series with constant coefficient one.
Then

\[
 dJ_e=\ell_e.
\]

Geometric doubling acts by $S(g_e)=g_e^2$ and
$S(E_e)=(1+g_e)E_e$. Consequently

\[
 S(J_e)=\frac{2\ell_e}{g_e^2-1}(1+g_e)E_e=2J_e.
\]

Orientation reversal gives $J_{ji}=-J_{ij}$ exactly. For a root $0$,

\[
 Z_{ij}=J_{ij}-J_{i0}+J_{j0}
\]

is closed because $\ell_{ij}=\ell_{i0}-\ell_{j0}$.
Changing the root from $0$ to $1$ therefore has the constant linear rule

\[
 Z_{ij}\longmapsto Z_{IJ}-Z_{I1}+Z_{J1}.
\]

The translated-head correction of the ordinary edge basis has disappeared.
Constant wedges of $k$ such closed generators are exact doubling
eigenvectors of weight $2^k$.

This is compatible with Eulerian/Bernoulli methods, but does not supply a
finite geometric realization. Menous, Novelli and Thibon give a
plane-tree expansion of Eulerian idempotents via a discrete-integral
recurrence in Sections 5.2–5.3 of
[Tree expansions of some Lie idempotents](https://doi.org/10.5802/alco.373).
Their expansion supplies arity-dependent coefficients; identifying its
class sums with the present network dictionary remains a separate task.

## No finite edgewise logarithm can have this naturality

Suppose a Laurent polynomial $L(z)\in\mathbb Q[z,z^{-1}]$ satisfies

\[
 L(xy)=L(x)+L(y).
\]

For every nonzero exponent $k$, the coefficient of $x^ky^k$ on the left
is the coefficient of $z^k$ in $L$, while the right side has no such
monomial. Thus all nonconstant coefficients vanish. The constant
coefficient also vanishes, so $L=0$.

In particular no nonzero finite Laurent multiplier
$J_e=f(g_e)E_e$, with $L(z)=(z-1)f(z)$, can replace the logarithm while
keeping the exact additive root-transfer rule.

The ordinary Taylor truncation is explicitly defective. For

\[
 P_L(z)=\sum_{r=1}^{L}\frac{(-1)^{r-1}}r(z-1)^r
\]

the coefficient of $x^Ly^{-L}$ in
$P_L(x/y)-P_L(x)+P_L(y)$ is $(-1)^{L-1}/L$, which is nonzero.
Thus every finite truncation leaves a nonzero cubical boundary.
An arity-dependent multivariate correction could still repair a special
global state; this argument only excludes the edgewise shortcut.

## Augmentation is not nilpotent after coning

There is also no universal finite augmentation cutoff for coned cubes.
In two physical dimensions consider

\[
 U_j(x,y)=\sigma(x+jy+\sigma(y)).
\]

For dual coordinates $A,B$, its generic kernel is

\[
 R_j=\frac1{A(B-jA)(B-(j+1)A)}.
\]

For every integer $m\ge0$, the exact forward-difference identity is

\[
 \sum_{j=0}^{m}(-1)^{m-j}\binom mj R_j
 =\frac{(m+1)!\,A^{m-1}}
        {\prod_{j=0}^{m+1}(B-jA)}.
\]

It follows by writing $R_j=A^{-2}\Delta_j(B-jA)^{-1}$ and applying the
elementary reciprocal divided-difference formula. The right side is
nonzero at every order. In cubical language the left side comes from
$(g_e-1)^m$ times one translated segment, coned from the origin.
Hence arbitrarily high augmentation powers can retain a nonzero top
class.

This prevents replacing the completed logarithmic algebra by a fixed
finite quotient before applying the coning map. A successful use of
Eulerian or Baxter states must prove exact cancellation for those
particular global states, or provide a finite resummation into geometric
units. A compact formal series alone is not a width bound.

The adjacent standard-library checker clears the finite-difference
denominators for $m=0,\ldots,12$ and checks the leading mixed monomial of
the truncated logarithm for $L=1,\ldots,12$. The proofs above are uniform;
the receipt is a reproducible convention control.
