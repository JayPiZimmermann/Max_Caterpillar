# Shorter lower-count routes: one germ and one generating function

Status: uniform mathematical derivations independently reviewed; not new
Lean certificates. Exact finite controls and a fresh root replay passed;
see `lower_count_elegance_independent_audit.md` and
`lower_count_elegance_root_replay.json`. The existing formal statements remain valid. These
routes keep the caterpillar and Brunck-et-al. rooted-star face dictionaries,
source-oriented tree functions and all their faces, and the weighted large-matching
mixtures. The face extension is proved in
[source_face_closure_audit.md](source_face_closure_audit.md); the full-unit
cover below is one ingredient of that proof. They do not establish an unrestricted all-tree exponential bound.

## 1. DIRECT_REPLACE: one germ on a generic ordered tie stratum

For a tied set $T$, set every tied coordinate to **one**, not zero.
Prescribe a strict order of all outside coordinates below one. Every unit's
preactivation restricts to an affine function on this open stratum: the
internal comparisons vanish, and all other comparisons have fixed signs.
Choose a point avoiding the zeros of all nonzero affine restrictions in
the finite expansion. Then a unit can have a nonzero top germ only if its
preactivation vanishes identically on the stratum. Thus all outside
coefficients vanish, as does the coefficient $\lambda$ of a common tied
shift. Its tied germ is therefore translation invariant.

Take the ordinary germ at this point, then fix one tied perturbation
coordinate to zero, and work modulo $\mathcal L_{m-2}$ for $m=|T|\ge3$.
The maximum gives the nonzero $(m-1)$-simplex class; shallow functions vanish.
If $G[T]$ has $c$ components, its comparisons and one head span at most
$m-c+1$ forms, so a surviving unit requires $c\le2$.
For unit inner coefficients, the outside coefficient is
$\kappa_o-u_\rho(o)$. An isolated tied label has head coefficient $\kappa_t$.
If it is zero, all forms annihilate both that coordinate vector and the
all-ones vector, giving dimension at most $m-2$ even when that label is the
anchor. These are exactly the old passing conditions.

This removes the second derivative, base-$B$ arithmetic and integrality
from the written argument. In particular, the reduced-forest proof extends
to arbitrary real heads when the inner coefficients are still one.
It does **not** thereby allow arbitrary inner coefficients in the
coefficient-balance/block argument.

A scope-preserving, explicit alternative is to keep integer heads, choose
$p_t=1$, $p_o=-B^{\rho(o)}$, and $B>\sum|h_i|+|M|$.
Then $A(p)=\lambda-\sum_o(\kappa_o-u_\rho(o))B^{\rho(o)}$ has integer
digits of modulus less than $B$. Its vanishing forces $\lambda=0$ as well
as all outside digits to vanish. This also needs only one germ.

## 2. The cross-size injection is the useful simplification

For a unit-inner-weight forest $F$, call degree-one vertices with
$\kappa=0$ pendants, and let $\Phi$ contain the nonisolated nonpendants.
For a passed tied set $T$:

* an original isolate is tied exactly when its $\kappa$ is nonzero;
* a pendant whose neighbor is not pendant is tied exactly when its
  neighbor is tied;
* a two-pendant component is entirely tied.

Therefore $T$ is determined by $A=T\cap\Phi$, **across all cardinalities**,
not only at a fixed tied size. Also $|T|\ge|A|$.
For fixed $T$, balance prescribes an orientation of $F-T$ uniquely:
delete leaves to see that a forest orientation is determined by its
outdegrees. Let $a_U(T)$ be the fraction of outside orders that pass.
For $0<y\le1$, define
$$
 F_U(y)=\sum_T a_U(T)y^{|T|}.
$$
The injection gives a single product bound for this entire generating
function, rather than a separate bound for each coefficient.

## 3. Smaller blocks and their exact order probabilities

Use a degree-two covering subforest on $\Phi$, with each isolated vertex
either adjacent to a pendant or forced into $T$. For a reduced-degree-two
forest use its reduced forest. A path with at least two vertices partitions
into edges and, if its size is odd, one three-vertex path.

A singleton with a fixed pendant has factor $1/2+y$; a forced singleton
has factor $y$. The chosen pendant vertices are outside $\Phi$, are
distinct, and cannot overlap another block. All block order restrictions
therefore involve disjoint vertex sets.

An edge block has factor
$$
 E(y)=\tfrac12+2y+y^2.
$$
A three-vertex path has factor
$$
 P(y)=\tfrac13+2y+3y^2+y^3.
$$
For the empty selected subset of the path, a prescribed orientation is
realized by at most two of its six orders, giving $1/3$.
If only the middle vertex is selected, the factor is one; if only one
leaf is selected, the remaining edge has order probability $1/2$.
These give the coefficient $2y$. The other coefficients are immediate.
Relative orders on disjoint blocks are independent.

More generally, a star with $s$ leaves has the useful bound
$$
 W_s^*(y)=y(1+y)^s+
       \frac{(1+y)^{s+1}-y^{s+1}}{s+1}.
$$
When its center is outside and $q$ leaves remain outside, any prescribed
orientation has probability
$1/((q+1)\binom qr)\le1/(q+1)$, where $r$ leaves lie above the center.
Summing these probabilities gives the displayed integral polynomial.
In particular $W_1^*=E$ and $W_2^*=P$.
This uses the existing orientation-uniqueness argument but avoids choosing
a separate matching inside each block.

For source-oriented trees, root the underlying tree at its head root $r$.
Include all out-leaf edges, then choose one child edge at every nonleaf
with neither a pendant nor an out-leaf neighbor. Only $r$ and the source
$s$ can be out-leaves. Each vertex therefore has at most one selected
child edge: only $s$ can be an out-leaf child, and an out-leaf root has
only one child. A vertex adding a child edge had none from the out-leaf
rule. Each vertex also has at most one parent edge. Hence the selected
forest has degree at most two without an exceptional common-neighbor
case. Every isolated vertex in $\Phi$ is pendant-adjacent or a leaf with
$\kappa\notin\{0,1\}$, and the latter is forced tied.
Thus the same four block factors apply to the entire base family.
All face states of these source-oriented trees are now included by the
component-charge reduction in [the face-closure proof](source_face_closure_audit.md).
The degree-two cover itself need not survive taking a face; the reduction
transfers detection capacity to one smaller full source unit instead.

## 4. Pure base: remove the polynomial loss, or improve the base

All four block factors are at most one at $y=1/6$. Consequently
$F_U(1/6)\le1$ for every base unit. Cover all ties of size at least three
and sum their weights:
$$
 |K|\ge(7/6)^N-1-N/6-\binom N2/36.
$$
This already gives $\Omega((7/6)^N)$ and eliminates the binomial-mode or
$(N+1)$ averaging step.

There is a stronger equally explicit choice
$$
 y_0=\sqrt{3/2}-1,\qquad E(y_0)=1,\qquad
 P(y_0)=\tfrac56+\tfrac12y_0<1.
$$
The singleton factors are also below one. Thus
$$
 |K|\ge (3/2)^{N/2}
       -1-Ny_0-\binom N2y_0^2
       =\Omega((3/2)^{N/2}).
$$
The second formula uses the improved $1/3$ empty-path order probability.
It is optional if maintaining the existing $7/6$ base is preferable.
With all canonical oriented star face functions free, replace the
quadratic truncation by $\sum_{m=0}^4\binom Nm y^m$; the exponential rates
are unchanged. Arbitrary-real-head or weighted stars are not free.

## 5. One generating-function inequality for mixtures

Put $p=y/(1+y)$ and $W=(1+y)^N$.
For weighted comparison pseudoforests with a matching of size at least
$k$, the independent component witnesses give
$$
 F_G(y)\le W\rho^k
 \left(1+ka+\binom k2a^2\right),\qquad
 \rho=1-p(1-p),\quad a=p(1-p)/\rho.
$$
For a free-family threshold $r$ ($r=3$ normally, $r=5$ with free canonical
stars), the common covering inequality is
$$
 W-\sum_{m<r}\binom Nm y^m
 \le \sum_{\text{base }U}F_U(y)+\sum_{\text{added }G}F_G(y).
$$
It applies to mixed families because the same one-germ test supplies both
necessary conditions.

### Preserve the current matching exponential base, without mode estimates

Take $p=1/4$, $y=1/3$ and $\rho=13/16$.
Even the old path factor with empty coefficient $1/2$ satisfies, blockwise,
$W_B(1/3)\le(\sqrt{13}/3)^{|B|}$:
the edge check is $23/18\le13/9$, and the three-vertex check reduces to
$6889\le8788$ after squaring.
The singleton factors also satisfy this bound. Since $|\Phi|\le N$ and
$\sqrt{13}/3>1$,
$$
 F_U(1/3)\le(\sqrt{13}/3)^N
       =W\rho^{N/2}\le W\rho^k \qquad(2k\le N).
$$
Hence the number $Z$ of counted base and added terms satisfies
$$
 Z\ge
 \Pr(\operatorname{Bin}(N,1/4)\ge r)
 \frac{(16/13)^k}{1+3k/13+9\binom k2/169}.
$$
The tail factor is at least $1/2$ for $N\ge12,r=3$ and for $N\ge20,r=5$.
Thus the denominator $20d_k$ or $(N+1)d_k$ can be replaced by $2d_k$,
with no anti-concentration or coefficient estimate.

### A sharper matching base with the improved path factor

Take $p=1/3$, $y=1/2$, $\rho=7/9$ and $\tau=\sqrt7/2$.
The four block checks are
$$
 \tfrac12+y=1\le\tau,\quad y\le\tau,\quad
 E(1/2)=7/4=\tau^2,\quad P(1/2)=53/24\le\tau^3.
$$
The last inequality is $2809\le3087$ after squaring.
Therefore $F_U(1/2)\le\tau^N=W\rho^{N/2}\le W\rho^k$, and
$$
 Z\ge
 \Pr(\operatorname{Bin}(N,1/3)\ge r)
 \frac{(9/7)^k}{1+2k/7+4\binom k2/49}.
$$
In particular the prefactor is at least $1/2$ for $N\ge9,r=3$ or
$N\ge15,r=5$; keeping the existing thresholds 12 and 20 is harmless.
This improves the exponential base while shortening the proof.

For excess at most $b$, replace the quadratic in either mixture formula
by $\sum_{j=0}^{\min(k,b+2)}\binom kj a^j$.
If $k=\Omega(N)$ and $b=o(N)$, this costs only $\exp(o(N))$.
All graph coefficients and heads may be real and signed in the added
family; only the base block argument uses unit inner coefficients.

## 6. KEEP: the all-tree quadratic argument

At a three-label tie, a canonical tree face's apex must be tied: its
outside coefficient would otherwise be $-1$. The other two labels must
share a retained edge, or there are three induced components.
Each term has at most $N-2$ such edges, giving
$\binom N3\le(N-2)|K|$ and $|K|\ge N(N-1)/6$.
This already covers all orientations and face states and needs no further
machinery.

## Guardrails and a failed shortcut

Deleting the second germ while retaining top height zero is invalid for
arbitrary integer heads. On tied coordinates $(x_1,x_2,x_3)$, the unit
$\sigma(x_1+\sigma(x_1-x_2))$ has isolated coordinate 3 with $\kappa_3=0$.
After anchoring coordinate 3 its support triangle has dimension two,
so the mere coordinate-absence argument does not put it in $\mathcal L_1$.
Using top height one or the generic-stratum test is essential.

A large matching cannot replace coefficient balance under the existing
base scope: rooted stars have matching number one but belong to the
exponentially bounded base family. Conversely arbitrary signed inner
weights do not retain the same $\kappa$ and pendant rules. The generating function
unifies the counting, not these two distinct structural hypotheses.

## Exact convention controls

The standard-library checker `lower_count_elegance_check.py` and adjacent
JSON receipt independently enumerate the block orders and all 9,296
four-label forest/head cases with $\kappa\in\{-1,0,1,2\}$ and reduced
degree at most two. All 18,992 passed tied sets respect the cross-size
injection; the $y=1/6$ and $p=1/3$ product bounds pass.
It also checks the simplified source-oriented covering forest for all
50,068 labelled tree/source/root choices through six tree vertices.
The four displayed binomial-tail thresholds are checked with exact
rational arithmetic. All controls pass in 5.45 seconds.
These finite checks support conventions; the preceding proofs are uniform.
