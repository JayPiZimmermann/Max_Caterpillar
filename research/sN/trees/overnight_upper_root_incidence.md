# The first bounded-root correction obstruction

For the actual undoubled recurrence with the fixed star-Koszul contraction,
the next correction cannot always be chosen with at most two factors
depending on the current root. This failure already occurs when choosing
$C_5$ on six labels, and survives every earlier homology-gauge choice.
It does not exclude another contraction or another geometric recurrence.

There is an important distinction between closed representatives and genuine
freedom in this gauge. Since $dH+Hd=1-ip$, a closed chain $C$ satisfying
$HC=0$ must equal $ipC$. Translating its triangle-cycle representatives and
then restoring $HC=0$ therefore produces the same canonical closed lift.
The first correction $c_3$ is unique. The full space of choices for $c_4$
has dimension one; that parameter is included in the test below.

Split the cycle space on labels $0,\ldots,n-1$ as

\[
 Z=Z(\{1,\ldots,n-1\})\oplus
       \operatorname{span}\{z_{i1}:2\le i<n\}.
\]

A basis for the first summand is
$z_{ij}-z_{i1}+z_{j1}$, with $i>j>1$. It is represented by triangle cycles
avoiding label $0$. The second summand consists of the root-dependent
triangles on $0,1,i$. The candidate allows every wedge with at most two
factors from that second summand, and arbitrary other triangle factors.
Thus it is broader than an interval-supported two-root-block family.

The first two full correction maps have dimensions/ranks $3/3$ and $20/19$.
Propagating their entire affine solution space through the actual filling
gives

\[
 X_5(t)=X_5(0)+tV_5,\qquad
 a_5(t)=p\phi_0X_5(0)+t\,p\phi_0V_5.
\]

There are 185 candidate wedge columns for $c_5$ and one prior gauge column.
In all 1365 target rows, the ordinary and augmented ranks are 173 and 174.
More simply, the coefficient of

\[
 z_{21}\wedge z_{31}\wedge z_{41}\wedge z_{65}
\]

is zero on every allowed source boundary and on $p\phi_0V_5$, but equals
one on $p\phi_0X_5(0)$. This single coefficient is the complete dual
certificate. The receipt stores the full target and gauge variation.

The root-incidence filtration is preserved by cofaces: cycles avoiding
root $0$ continue to avoid it, and one root-dependent triangle maps to a
sum with at most one root-dependent factor. However, the displayed
functional annihilates the **boundaries** of the permitted source space;
it does not annihilate every target wedge of root incidence at most two.
The result is therefore a filtered boundary obstruction, not a claim that
the target itself has incidence degree three.

Producer and receipt: `overnight_upper_root_incidence.py/.json`. The exact
rational calculation takes about 1.5 seconds. It covers all prior
homology gauges for this specified contraction and canonical closed lift.
It does not cover arbitrary closed-chain representatives outside
$\ker H$: those would restore the root-preserving coface terms omitted
by the single-coface recurrence.

This closes the proposed uniformly two-root-dependent-block route in its
stated form. Increasing the incidence threshold is not by itself a route
to an exponential width bound.
