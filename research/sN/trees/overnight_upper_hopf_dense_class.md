# A uniform obstruction to one sparse graph per Baxter class

Let $T_N$ be the unnormalised signed caterpillar sum for the ascending word
$(1,\ldots,N-1)$, with apex $0$ and nonempty cut set. This word is a
singleton twin-BST class: its two BSTs are the opposing combs.

For every $N\ge4$, any representation of $T_N$ by units

\[
 \sigma\left(h(x)+\sum_{uv\in G}w_{uv}\sigma(x_u-x_v)\right),
\]

with arbitrary real linear heads, signed inner/output weights and widths,
even modulo $L_{N-2}$ on the $(N-1)$-dimensional translation quotient,
must have every edge of the complete graph on
$\{1,\ldots,N-2\}$ in the **total** comparison graph $G$.
In particular it needs at least $\binom{N-2}{2}$ distinct comparisons.
The claim concerns this individual class, not the maximum.

## Exact surviving-cut formula

Put $q=N-1$ and fix $1\le i<j<q$. First apply
$D_{e_0-e_q}$, then $D_{-e_v}$ for all
$v\in\{1,\ldots,q-1\}\setminus\{i,j\}$ in increasing order.
Modulo shallow functions, the result is

\[
\begin{aligned}
 &\mathbf 1_{\{i\ge2\}}\,
 \sigma(2x_i-x_0-x_q+\sigma(x_i-x_j))\\
 &\hspace{30mm}
 -\sigma(2x_j-x_0-x_q+\sigma(x_i-x_j)).
\end{aligned}
\]

Here is the complete cut classification. The first direction leaves a
top-dimensional apex/base face only when $q$ is a nonspine leaf.
Since it is the last word label, its parent is the last spine vertex $p$.
The frozen edge changes the head to $2x_p-x_0-x_q$.

The marked vertex $p$ cannot be deleted: at $-e_p$ the head contributes
$-2$, while there is at most one incoming edge, and at $+e_p$ the
outer value is positive. Hence $p$ must be $i$ or $j$.

Every other deleted vertex can contribute only in one of two ways.
An unmarked leaf is removed at the positive direction and contributes a
minus sign to $D_{-e_v}$. The current first spine vertex can be removed
at the negative direction only if it has just one remaining child,
contributing a plus sign. Losing two or more free edges is already
lower-dimensional and cannot affect the final nonshallow class.

Because the deletions proceed from left to right, every label before $i$
must consequently be a consecutive spine vertex. If $p=i$, there are
no later spine vertices. This gives the unique cut set
$\{2,\ldots,i\}$, which is permitted exactly when $i\ge2$.
If $p=j$, no deleted label between $i$ and $j$ can be a spine vertex,
so the unique cut set is $\{2,\ldots,i\}\cup\{j\}$.
All remaining deleted vertices are leaves.

There are $i-1$ first-spine deletions and $N-i-3$ leaf deletions.
Combining their signs with the original coefficient
$(-1)^{N+|S|}$ gives $+1$ in the first case and $-1$ in the second,
proving the displayed formula.

## Separation of a missing comparison

Use odd-additivity at $x=e_0$ and $y=e_i$ on the final derivative.
The first displayed unit has value zero under this functional; the
second has value $-1$. Thus the value on $T_N$ is **$+1$**.

Across this entire flag of $N-3$ directions, the only pair comparison
that remains nonlinear is $x_i-x_j$. If $ij$ is absent from $G$,
every source unit becomes shallow. The same odd-additivity functional
annihilates it. It also annihilates an $L_{N-2}$ remainder, which is
lowered to $L_1$ by the flag. This proves the required edge.

All directions and points are classes in the translation quotient;
one may subtract their zeroth coordinate to write them in $H_0$.
Biases in an exact homogeneous representation can be removed by
recession. No assertion is made about additional first-hidden-layer
features outside pair comparisons.

## Consequence for the live construction route

An apex-star/twin-BST union has at most $3N-5$ edges.
For $N\ge10$ this is less than $\binom{N-2}{2}$.
Therefore a map sending each Baxter class into units on just one such
graph cannot be uniform, even if it may choose the graph centre, root,
all orientations, arbitrary heads and arbitrary weights.

The global exponential family remains open. It can combine several
graphs within a class, or work directly with the symmetric target
without representing every class separately.
The geometric image of a marked Hopf operation must account for that
mixing; exponential abstract basis size alone does not establish it.

The standard-library checker verifies the complete surviving-cut formula,
the odd-additivity value and the comparison-freezing assertion for every
pair at $N=4,\ldots,10$. These finite controls supplement the uniform proof.
