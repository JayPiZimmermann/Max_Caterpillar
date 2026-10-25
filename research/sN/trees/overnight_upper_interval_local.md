# The smallest ordered grafting identity

Let `f_+(q)=1/[q(q+a)]` and `f_-(q)=1/[q(q-a)]`. Then

\[
\begin{aligned}
 f_+(x)f_-(y)-f_-(x)f_+(y)
={}&f_+(x+y)\bigl(f_+(x)-f_+(y)\bigr)\\
 &-f_-(x+y)\bigl(f_-(x)-f_-(y)\bigr).
\end{aligned}
\]

This is an exact rational identity for the same external parameter `a`.
It exchanges an antisymmetric combination of two root branches with
two ordered path-attachment combinations. It retains the placement
information lost by the uniform root sums in the preceding interval
tests.

The proof is elementary. Both sides simplify to

\[
\frac{2a(x-y)}{xy(x^2-a^2)(y^2-a^2)}.
\]

For the right side, use
`f_+(x)-f_+(y)=(y-x)(x+y+a)/[xy(x+a)(y+a)]`, and the analogous minus
formula. Each path factor cancels one of the two sum poles; subtracting
the channels cancels the other.

This is, up to scale, the only constant-coefficient relation among the
twelve local functions

\[
 f_e(x)f_f(y),\qquad f_e(x+y)f_f(x),\qquad
 f_e(x+y)f_f(y),\qquad e,f\in\{+,-\}.
\]

The independent polynomial check multiplies by their common product of
nine linear denominators, expands the twelve degree-five numerators
using integer arithmetic, and finds exact rank eleven. The displayed
relation annihilates every polynomial coefficient. Thus its one-dimensional
star-branch projection cannot convert all four orientation combinations
to path states. A proposed scalar uncrossing rule that treats these
combinations as interchangeable would be false already here.

This relation may be used as a local ordered boundary-state rule. No
global noncrossing construction or sufficiency theorem follows from it
alone. Producer and receipt: `overnight_upper_interval_local.py/.json`.
