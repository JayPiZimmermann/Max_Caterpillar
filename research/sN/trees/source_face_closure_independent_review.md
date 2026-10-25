# Independent review: including every face in the lower-count families

Verdict: both proposed extensions are valid. Reduced-degree closure is
literal edge containment. Source-oriented faces need the component argument
below; their entire reduced forests need not have bounded degree.
This is a mathematical review, not a new Lean certificate.

## Reduced-degree closure for arbitrary real heads

Start with $U=\sigma(h+\sum_{e\in M}\sigma(\ell_e))$, with unit inner
coefficients and arbitrary real $h$. Give each edge an omitted, linear or
retained state and absorb the linear states into the new head.

An original degree-one vertex with $\kappa=0$ has only one incident edge.
If that edge remains retained, its head coefficient and $\kappa$ are
unchanged, so it is still removed when forming the new reduced forest.
If the edge is not retained, the vertex is isolated. Thus no originally
removed vertex has an edge in the new reduced forest. Every new reduced
edge was an old reduced edge.

Consequently the maximum reduced degree cannot increase. Strictly speaking,
the **edge set**, or the nonisolated part, is a subgraph of the old reduced
forest: a previously deleted vertex may reappear as an isolate. This minor
vertex-set qualification has no effect on degree or counting.
Base faces without the pyramid apex are shallow and can be put in the
remainder.

## Source-oriented face charges

Let the original tree have nonapex vertex set $V$, source $s$, head root $r$,
and all edges oriented from parent to child away from $s$. The apex is $a$.
After choosing the edge states, let $M$ be the retained forest and let
$h'$ be the new head on $V$; its coefficient at $a$ is still $-1$.
Define
$$
 \kappa_v=h'_v+\operatorname{outdeg}_M(v),\qquad
 e_v=\kappa_v-\deg_M(v)+1 \quad(v\in V).
$$
Initially $e=\delta_s+\delta_r$. Replacing a parent-child edge $p\to q$
by its linear form adds one to $e_p$; omitting it adds one to $e_q$.
These are the only changes. Thus every $e_v$ is a nonnegative integer.
For every retained component $C$,
$$
 e(C)=h'(C)+1,
 \qquad\sum_{C}h'(C)=1.
$$
The first identity follows from $|E(C)|=|C|-1$.

Use the refined necessary conditions for detection: outside coefficient
balance, isolated-label activity, and at most two induced components on
the tied labels. Consider a tied set of size at least three.
The apex must be tied, since its outside coefficient would be $-1$.
It is isolated, so all other tied labels form one connected set in one
retained component $C$.
Every other component $D$ is entirely outside the tie. Summing its zero
outside coefficients gives $h'(D)=0$, since the coefficients of every
comparison sum to zero. Therefore $h'(C)=1$.

Thus a potentially detecting face has one **fixed** component $C$ with
head sum one and every other component has head sum zero. This component
depends on the face, not on the particular locality. If this pattern
fails, the face has zero capacity. If $C$ is a singleton, its capacity
for ties of size at least three is also zero.

## Exact realization by a smaller source-oriented unit

The inherited orientation on a retained component $C$ points away from
one vertex $b_C$, the vertex nearest the original source. Hence
$e|_C=h'|_C+\delta_{b_C}$.
Since $e(C)=2$, write $e|_C=\delta_u+\delta_v$, allowing $u=v$.
Reverse the edges on the path from $b_C$ to $u$. Using
$\sigma(x_p-x_q)=x_p-x_q+\sigma(x_q-x_p)$ transports the head by
$\delta_{b_C}-\delta_u$. The resulting head on $C$ is exactly $\delta_v$,
and all edges point away from $u$. Including the apex term $-x_a$ gives
a full source-oriented canonical unit on $\{a\}\cup C$.
This is an exact preactivation identity on that component.

Similarly a component $D$ with head sum zero has $e(D)=1$.
Reorienting it away from its unique charge leaves head zero and a sum
of nonnegative comparison ReLUs. At a balanced outside locality its
linear germ is zero. No additional head or nonlinear germ survives
from these other components.

## Capacity on the original $N$ labels

Define $a_U(T)$ using the refined passing conditions, and only use
$|T|\ge3$. For a face of positive capacity, every such $T$ is contained
in $\{a\}\cup C$.
Each passing global outside order restricts to a passing outside order
for the smaller source-oriented unit. Reorientation preserves $\kappa$,
and all retained neighbors of a vertex of $C$ remain in $C$.
Uniform global outside permutations induce a uniform relative order
on $C\setminus T$. Therefore
$$
 a_{\rm face}(T)\le a_{\rm smaller}(T).
$$
The other components impose additional restrictions and cannot increase
this fraction. Consequently, for $0<y\le1$,
$$
 F_{\rm face}(y)
 :=\sum_{|T|\ge3}a_{\rm face}(T)y^{|T|}
 \le F_{\rm smaller}(y).
$$
The established smaller-unit block bound gives
$F_{\rm face}(y_0)\le1$ for $y_0=\sqrt{3/2}-1$.
At $y=1/2$ it gives
$$
 F_{\rm face}(1/2)\le
       \tau^{|C|+1}\le\tau^N,\qquad\tau=\sqrt7/2>1.
$$
Thus the pure-base rate and the $9/7$ matching-mixture rate are unchanged
after adjoining all source-oriented face functions.
The same comparison remains valid with the tied-size threshold five
used when canonical oriented stars are free.

It would be incorrect to claim that every source face has the old
bounded-out-leaf property, or to transfer **all** old passing localities
without the induced-component condition. The refined capacities above
are what the common local test actually requires.

## Exact finite convention checks

An independent standard-library enumeration in this review checked all
labelled trees on two through four nonapex vertices, every source and head
root, and every three-state edge assignment: 7,167 cases in total
(12, 243 and 6,912 by tree size).
It reconstructed the charge vector directly from heads and retained edges,
checked the component charge identities and the smaller-unit normalized
head, and enumerated every ordered tie of size at least three.
All 3,899 passing ordered ties mapped to the claimed smaller component.
The exact passing-fraction inequality and the original-$N$ bound at
$y=1/2$ passed in every case. Runtime was 0.45 seconds.
These are finite convention controls; the argument above proves the
uniform statements.
