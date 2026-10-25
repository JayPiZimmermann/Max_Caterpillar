# One local test for the orientation and graph lower bounds

This is a mathematical simplification of the existing paper proofs, not a
new Lean certificate. It preserves the integer-head scope of the reduced
forest theorem and the arbitrary-real-head/weight scope of the graph bounds.
Biases may first be removed by taking recession functions; the homogeneous
target, comparison graphs, coefficients and number of terms are preserved.

For a positively homogeneous CPWL function, write
$$
 \partial_v f(y)=\lim_{\epsilon\downarrow0}
       \frac{f(v+\epsilon y)-f(v)}{\epsilon}.
$$
This is linear in $f$. For a support function it is the support function of
the face exposed by $v$, so it preserves every dimension space
$\mathcal L_d$. Linear precomposition also preserves $\mathcal L_d$.

## The common local test

Fix a tied set $T$ of size $m\ge3$, a point $p$ with $p_t=0$ for $t\in T$
and distinct negative coordinates elsewhere, and an anchor $a\in T$.
Let $E_T:\mathbb R^T\to\mathbb R^N$ insert zero perturbations outside $T$,
and let $J_a:\mathbb R^{T\setminus\{a\}}\to\mathbb R^T$ insert a zero at $a$.
Define the linear test
$$
 \mathcal G_{p,T,a}f
   =\left[
       \bigl(\partial_{\mathbf1_T}
           ((\partial_p f)\circ E_T)\bigr)\circ J_a
     \right]
 \quad\bmod\mathcal L_{m-2}.
 \tag{1}
$$
The all-ones derivative is taken in the full $m$ tied coordinates.
**The anchor is fixed only afterwards.** Reversing these operations loses
the common-translation argument.

The target survives: $(\partial_p\max_N)\circ E_T=\max_T$, and
$\partial_{\mathbf1_T}\max_T=\max_T$. After anchoring this is
$\max(0,y_1,\ldots,y_{m-1})$, the support function of a full-dimensional
simplex, whose class modulo $\mathcal L_{m-2}$ is nonzero.
This is the simplex nonvanishing fact already proved in the paper by
successive opposite-face differences and dimension drop.
Every shallow remainder is killed, since the operations preserve
$\mathcal L_1\subseteq\mathcal L_{m-2}$.

Consider
$$
 U=\sigma(A),\qquad
 A=h+\sum_{ij\in M}c_{ij}\sigma(x_i-x_j),
 \tag{2}
$$
with arbitrary real linear $h$ and arbitrary real coefficients.
If $A(p)\ne0$, the first germ is zero or shallow, so (1) vanishes.
Otherwise it has the form
$$
 g(y)=((\partial_pU)\circ E_T)(y)
     =\sigma\!\left(H(y)+
          \sum_{ij\in M[T]}c_{ij}\sigma(y_i-y_j)\right).
$$
Put $\lambda=H(\mathbf1_T)$. Directly from the derivative definition,
$$
 \partial_{\mathbf1_T}g=
 \begin{cases}
  0,&\lambda<0,\\
  g,&\lambda=0,\\
  H+\sum_{ij\in M[T]}c_{ij}\sigma(y_i-y_j),&\lambda>0.
 \end{cases}
 \tag{3}
$$
The last line is shallow. Thus a nonzero test requires $\lambda=0$;
the surviving germ is invariant under a common translation of all tied
coordinates. This extra derivative is what permits the same test to handle
arbitrary heads, rather than assuming translation invariance in advance.

Two consequences give the different counting capacities.

1. **Graph condition.** If the induced graph on $T$ has $c$ components,
   including isolates, its comparison forms span dimension $m-c$.
   Adjoining $H$ gives at most $m-c+1$ forms. A unit depending on those
   forms belongs to $\mathcal L_{m-c+1}$, even for signed coefficients:
   write its preactivation as $h_P-h_Q$ and use
   $\sigma(h_P-h_Q)=h_{\operatorname{conv}(P\cup Q)}-h_Q$.
   Therefore a nonzero test requires $c\le2$.

2. **Integer-head balance.** Suppose every inner coefficient is one and
   $h=\sum h_ix_i$ is integral. Put
   $\kappa_i=h_i+\#\{j:(i,j)\in M\}$.
   For a label permutation $\rho$, let $T=\{i:\rho(i)<m\}$ and
   $p_i=-B^{\rho(i)}$ off $T$, where the integer $B>1$ exceeds
   $\sum_i|h_i|+|M|$ for every integer-head unit being counted.
   Let $u_\rho(i)$ count neighbors at smaller positions. Then
   $$
    A(p)=-\sum_{i\notin T}
                (\kappa_i-u_\rho(i))B^{\rho(i)}.
   $$
   Nonzero test requires $A(p)=0$. All integer digits have modulus less
   than $B$, so successive reduction modulo $B$ gives
   $u_\rho(i)=\kappa_i$ for every $i\notin T$.
   If a tied vertex $t$ has no tied neighbor, its coefficient in $H$ is
   $\kappa_t$. If this is zero, every local linear form annihilates both
   $e_t$ and $\mathbf1_T$, the latter by (3). These two vectors are
   independent. Hence the germ depends on at most $m-2$ forms and the
   test vanishes. Thus $\kappa_t\ne0$ is also necessary.

The second consequence is exactly the existing passing condition.
No small perturbation size, finite cube, or integrality argument controlling
the sign on a cube is required. The subsequent forest orientation,
matching, star-block product and binomial arguments are unchanged.

## One covering inequality, distinct capacities

Choose $B$ simultaneously for the finite collection of integral units.
For every permutation locality, (1) is nonzero on the target, so at least
one term contributes. Normalize the number of localities served by a unit
by $m!(N-m)!$, and call its upper capacity $C_m(U)$. Then
$$
 \binom Nm\le\sum_U C_m(U).
 \tag{4}
$$
The established counting arguments give:

* integer-head functions with reduced forest degree at most $\Delta\ge2$:
  $C_m(U)\le(2\Delta+2)^m$;
* canonical tree face functions with at most $s\ge1$ out-leaf neighbors
  at every vertex: $C_m(U)\le(2s+4)^m$;
* every integer-head unit with reduced forest degree at most two,
  including caterpillar/rooted-star face functions, and every full
  source-oriented tree function: $C_m(U)\le6^m$;
* arbitrary weighted comparison graph $G$:
  $C_m(U)\le\#\{T:|T|=m,\ c(G[T])\le2\}$.

Thus all reduced-degree-two integer-head functions and source-oriented full
tree functions may be included in the base class of the matching and
bounded-degree mixtures without changing any bound.
This does not include every face state of those source-oriented trees:
freezing edges can create additional out-leaves.
The degree, matching, and orientation restrictions remain distinct; (4)
does not assert one new graph condition covering unrestricted trees.

The same test is compatible with the established free canonical-star
extension: a surviving canonical top germ is unchanged by the second
derivative, and the previously constructed star separator can then be
applied. This does not make arbitrary real-head/weighted stars free.

## The quadratic bound already holds for all canonical tree faces

Consider a canonical tree on the $N-1$ labels other than an apex $a$, with
arbitrary orientation and any face state. A pyramid face function has
head coefficient $-1$ at $a$, and no retained comparison meets $a$.
Thus $\kappa_a=-1$, unchanged by freezing other edges into the head.
At a three-label tie, the balance condition forces $a$ to be tied:
otherwise $u_\rho(a)=0\ne-1$.
Write the other two tied labels as $i,j$. Unless $ij$ is a retained edge,
the induced comparison graph has three components, so the common test is
zero. Each unit therefore serves at most $N-2$ three-label tie sets,
one for each retained edge. Faces without the apex have shallow support
functions and may be absorbed into the remainder. Consequently every
expansion by canonical tree face functions satisfies
$$
 \binom N3\le(N-2)|K|,
 \qquad |K|\ge\frac{N(N-1)}6 \quad(N\ge3).
 \tag{5}
$$
This includes every tree shape and every orientation or face state.
It does not extend this quadratic argument to arbitrary real heads or
weights, where the distinguished coefficient $-1$ need not exist.

## Compact matching mixture, without anti-concentration

Take $m=\lfloor N/4\rfloor$, $\rho=13/16$ and
$d_k=1+3k/13+9\binom k2/169$. Adjoin arbitrary-real-head/weight
comparison pseudoforest functions with matching number at least $k$
to the full base class of capacity $6^m$ above.
For $0\le2k\le N$ and $N\ge12$, matching witnesses give each added
function weighted capacity at most $\rho^k d_k$.
The weighted base capacity is
$$
 6^m(1/4)^m(3/4)^{N-m}
   =(3/4)^N2^m\le\rho^{N/2}\le\rho^k.
$$
The first inequality reduces to $162\le169$.
Consequently, with $Z$ counted terms and
$P_m=\binom Nm(1/4)^m(3/4)^{N-m}$,
$$
 Z\ge\frac{P_m(16/13)^k}{d_k}
   \ge\frac{(16/13)^k}{(N+1)d_k}.
 \tag{6}
$$
Here $m$ is a binomial mode, so $P_m\ge1/(N+1)$.
With free canonical stars, require $N\ge20$, so $m\ge5$.
Removing the coefficient/Fourier estimate replaces the paper's stronger
denominator $20d_k$ by $(N+1)d_k$, while preserving the exponential base
$16/13$ and every orientation/head/weight scope. Keeping the exact $P_m$
form also retains an elementary route to the $N^{-1/2}$ asymptotic
prefactor via Stirling, if desired.

For added graphs of excess
$b(G)=\sum_C\max(0,|E(C)|-|V(C)|)\le b$, replace $d_k$ in (6) by
$$
 D_{k,b}=\sum_{j=0}^{\min(k,b+2)}\binom kj(3/13)^j.
$$
This elementary proof works for every $b\ge0$; the discarded
anti-concentration proof's condition $b+2\le N/4$ is unnecessary here.
When $k=\Omega(N)$ and $b=o(N)$, $\log D_{k,b}=o(N)$, so the same
exponential-rate statement $\exp(k\log(16/13)-o(N))$ follows.

## Suggested paper condensation

Place (1)--(3) and their two consequences once before the counting proofs.
In the reduced-forest proof replace the mixed-cube and small-$\delta$
paragraphs with the integer-head consequence, then retain the existing
combinatorial proof. In the weighted proof cite the graph consequence
instead of repeating the local simplex and rank argument.
State (4) once for all mixtures, and use the five-line argument (6) for
matching mixtures. The finite-size improvement with denominator $20d_k$
can remain in the research coefficient addendum rather than the paper.
