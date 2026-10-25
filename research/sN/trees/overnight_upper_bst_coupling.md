# Coupled binary-search-tree compression: the first necessary state

The live route is to group the factorial permutation sum into binary-search
tree classes for a fixed label order, while retaining the two coupled
shuffle channels of a tree kernel. There are Catalan many tree shapes.
This count is useful only if each grouped expression has an appropriate
geometric realization. The following exact control explains a necessary
state distinction; it does not exclude a correctly coupled construction.

For an ordered list `pi` of all vertices, write

\[
C_\pi(z)=\prod_{j=1}^n
 \frac1{z_{\pi(j)}+\cdots+z_{\pi(n)}}.
\]

Permutations producing one fixed binary search tree under insertion are
exactly its root-first linear extensions. Consequently the ordinary
shuffle identity turns their sum into the rooted-cut product
`Phi_T(z)`. The actual canonical kernel, however, uses the product

\[
(-a)^{N-2}\Phi_{T,r}(\omega)\Phi_{T,r}(\omega+a d),
\]

where `d` is the signed degree vector of the oriented tree. Expanding
this product gives two independently chosen extensions. Restricting to
the same extension in both factors changes the rational function.

## A double pole that requires off-diagonal states

Take a root `r` and two leaves, with leaf frequencies `x,y`, root
frequency `-a-x-y`, and signed degree shifts `+1,-1` at the two leaves
and zero at the root. This is the binary search tree whose root is the
middle label. Its two extensions put the leaves in either order.

After including the canonical prefactor `a^2`, the sum using the same
extension in the two factors is

\[
D=\frac1{(x+y)^2}
 \left\{\frac1{y(y-a)}+\frac1{x(x+a)}\right\}.        \tag{1}
\]

At a generic point of the hyperplane `x+y=0`,

\[
\left.(x+y)^2D\right|_{y=-x}
 =\frac2{x(x+a)}\ne0.                               \tag{2}
\]

Thus this diagonal class has a genuine double pole. The two off-diagonal
terms are

\[
O=\frac1{(x+y)^2}
 \left\{\frac1{x(y-a)}+\frac1{y(x+a)}\right\},
\]

and their double-pole coefficient is the negative of (2). In fact

\[
D+O=\frac1{xy(x+a)(y-a)},                            \tag{3}
\]

the original star kernel. All three identities are elementary rational
identities, checked symbolically by `overnight_upper_bst_coupling.py`.

This obstruction concerns geometry, not merely the narrow canonical
tree dictionary. In dimension at least two, a generic top Fourier
kernel of a homogeneous CPWL function has at most simple poles along
each linear hyperplane. To see this, express the function as a difference
of polytope support functions and triangulate those polytopes. The
support-function valuation and lower-dimensional face terms reduce the
top class to a finite sum of full-dimensional simplex classes. Each
simplex has Fourier kernel a constant divided by the product of its
`d+1` barycentric frequency forms. These forms are pairwise
nonproportional for a nondegenerate simplex in `d >= 2`. A finite sum
of such fractions still has at most simple poles. A lower-dimensional
remainder does not change the generic kernel.

The double pole in (2) therefore prevents the diagonal grouped class
from being any finite CPWL dictionary combination in the top quotient.
Allowing cycles, arbitrary heads, or real inner weights cannot realize
that isolated expression. The missing off-diagonal terms must remain
within a grouped state or cancel with other grouped states before a
geometric realization is sought.

The same simple-pole property holds after taking a residue while the
remaining dimension is at least two: a simplex residue is again a
simplex fraction in one lower dimension, or zero. This gives a useful
necessary control for coupled expressions, without assuming they are
geometric in advance.

## Orientation averaging does not repair every pair of trees

Retaining the full independent product is necessary but not sufficient.
Take two binary search trees on four nonapex labels, with common root 0:

\[
 T:0\to1\to2\to3,\qquad U:0\to3\to1\to2.
\]

For each of the eight orientations of `T`, use its signed degree vector
`d_epsilon` in the second channel and form

\[
 R_c=(-a)^3\sum_{\epsilon\in\{\pm1\}^3}
 c_\epsilon\Phi_T(\omega)\Phi_U(\omega+a d_\epsilon).
\]

Here `a` is the apex frequency, and the four nonapex frequencies sum to
`-a`. Both the plain coefficients `c_epsilon=1` and the signed
coefficients `c_epsilon=epsilon_1 epsilon_2 epsilon_3` fail the necessary
CPWL residue condition. Put `x=omega_1`, `y=omega_2`, `z=omega_3`.
For the plain sum, the residue at `x+y=0` is

\[
 \frac{4a(a^2y+2a^2z-y^2z)}
 {yz^2(a-z)(a+z)(2a-y)(2a+y)(y+z)}.
\]

Its coefficient of `z^(-2)` is `4a/[y(4a^2-y^2)]`, which is nonzero.
For the signed sum that coefficient is
`-8a^2/[y^2(4a^2-y^2)]`, also nonzero. These residues live in dimension
three, where a double pole is inadmissible. The symbolic producer
`overnight_upper_bst_pair_states.py` verifies the full rational residue,
including the shifts and normalization, and records the offending flag.

Thus a successful Catalan grouping must couple different shape pairs or
retain additional cancellation states. Independently assigning one
geometric atom to each pair of trees, even after either of these full
orientation averages, is false. The complete coupled route remains open.

## An exact split-channel product rule

One way to keep the missing data explicitly is to distinguish the two
channel offsets. Put

\[
F_{s,t}(q)=\frac1{(q+sa)(q+ta)}.
\]

Applying the ordinary two-term shuffle identity in each channel gives

\[
\begin{aligned}
F_{\alpha,\beta}(x)F_{\gamma,\delta}(y)
={}&F_{\alpha+\gamma,\beta+\delta}(x+y)\\
&\quad\cdot\left[
 F_{\alpha,\beta}(x)+F_{\gamma,\delta}(y)
 +\frac1{(x+\alpha a)(y+\delta a)}
 +\frac1{(y+\gamma a)(x+\beta a)}\right].             \tag{4}
\end{aligned}
\]

The last two summands attach the two channels to different branches.
Deleting them is precisely the error exposed by (1)--(3). The previously
proved six-term local Fay identity is one cancellation rule between
these split states; it does not remove all split states independently.

The next missing statement is constructive: find a grouping of the
simplex target whose coupled states cancel every inadmissible double
pole and admit a controlled geometric realization. A Catalan number of
abstract shapes or a pair of ordinary shuffle identities alone does
not establish that statement. No exponential upper construction or
uniform negative theorem is claimed here.
