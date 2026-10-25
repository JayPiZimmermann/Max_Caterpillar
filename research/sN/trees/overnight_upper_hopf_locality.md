# A two-flag obstruction to the full classwise Baxter wheel map

Let $T$ be the signed caterpillar class sum for the two ordinary-label
words $(3,1,4,2)$ and $(3,4,1,2)$, with apex label $0$.
The natural associated graph is

\[
 G=\{01,02,03,04,12,13,24,34\}.
\]

There is **no** representation of $T$, even modulo $L_3$ on the
four-dimensional translation quotient, by finitely many units

\[
 \sigma\left(h(x)+\sum_{ij\in G}w_{ij}\sigma(x_i-x_j)\right)
\]

with arbitrary real linear heads $h$, arbitrary signed inner/output
weights, and either orientation of every listed comparison.
An arbitrary shallow remainder does not help.
This is stronger than the finite five-state exclusion.

## The elementary separating functional

Take $u=e_2-e_0$ and $v=-e_3$. Every edge of $G$ has nonzero
evaluation in at least one of these directions. The only comparisons
left free after the first directional germ are $13$ and $34$;
the second direction freezes both.

For any one of the displayed units, a nonzero outer value at the first
direction leaves a shallow derivative. If the outer value is zero,
the remaining unit has only the first-free comparisons as nonlinear
inner functions. After the second germ, every inner function is linear.
Hence $D_vD_u$ of any such network is shallow. This argument uses no
restriction on the heads, orientations, magnitudes, signs or width.

For a shallow homogeneous ReLU sum, the odd part is linear. Consequently
the functional

\[
 \Lambda(f)=[g(x+y)-g(-x-y)]-[g(x)-g(-x)]-[g(y)-g(-y)],
 \quad g=D_vD_u f,\quad x=e_0,\quad y=e_1,
\]

annihilates every allowed network. It also annihilates an $L_3$
remainder because two directional germs lower that filtration to $L_1$.

The exact value on the target is

\[
 \Lambda(T)=-1.
\]

The adjacent checker computes this in two ways. One updates the
head and free-edge list at each direction, discarding only shallow
terms. The second evaluates the original nested ReLUs on exact
lexicographic jets with coefficients of $1,\epsilon,\epsilon\delta$.
It does not use the germ simplification or any Fourier formula.
Both yield the same nonzero defect.

The result also applies to affine biases in an exact homogeneous
representation, by taking recession functions. Additional
first-hidden-layer features outside the stated comparison graph
are not covered.

## Relation to the complete finite residue gate

The independent rational search found the same obstruction at the
Fourier pole $\omega_2=\omega_0$. It enumerated all 52 spanning
two-forests, all 49,676 normalized heads, and all 30,436 distinct
nonzero proportional kernels of the original five-state family.
At this pole, its 612 incident kernels reduce to 63 distinct
residue columns. Their ordinary/augmented ranks are $60/61$;
all three independent null relations pass exact principal-part
verification. No candidate source was excluded by a pole filter.

The elementary two-flag proof supersedes that finite exclusion for this
fixed graph. It does not refute the full exponential candidate family:
that family may change the graph centre and the twin-tree pair.
Its exact five-input maximum control and embedding of the seven-input
noncrossing witness remain valid.

The structural consequence is precise. A uniform Hopf/class map cannot
send each Baxter class solely into its own apex-star/union graph,
even with unrestricted heads and weights. It must mix graph centres,
mix classes, or retain extra geometric boundary data.
