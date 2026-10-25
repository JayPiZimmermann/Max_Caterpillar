# The first ordered facet lift forces the full base orbit

This is a necessary-lemma test for replacing the facet symmetrization in
BHR+ Lemma 12. It does not rule out changing the facet representatives,
adding chains in the kernel of the coning map, or a different coherent
lift in higher dimensions.

The standard tetrahedron has, modulo lower-dimensional polytopes, the
one-paramid representative `-conv(0,Delta_P-Delta_Q)`, where `P,Q` are
disjoint two-element label sets. Its parallelogram base is

\[
Z_{P,Q}=e_{p_0}-e_{q_0}
       +[0,e_{p_1}-e_{p_0}]+[0,e_{q_0}-e_{q_1}].
\]

The corresponding exact four-input function identity is displayed in
`overnight_upper_relative_nc.md`. It fixes the sign of this representative
without relying on a Fourier sample.

For the four-simplex on five labels, choose one such representative in
each tetrahedral facet, allowing arbitrary linear combinations. A state
is an ordered partition `(P,Q,{m})` of the five labels with sizes
`(2,2,1)`, where `m` is the omitted facet label. There are 30 states,
six per facet. Include the usual alternating facet orientation signs.
Let `lambda_(P,Q,m)` denote the coefficient relative to the normalized
tetrahedron representative, so each facet requires

\[
\sum_{P\sqcup Q=[5]\setminus\{m\}}\lambda_{P,Q,m}=1.
\]

**There is only one cubical cycle with these facet normalizations:**

\[
\lambda_{P,Q,m}=\frac16\qquad\text{for every state}.
\]

Each base has four boundary segments. A segment of the form
`e_p-Delta_Q` belongs to exactly the two states obtained by putting either
of the two remaining labels beside `p` in `P`; the unused label is `m`.
The two induced signs are opposite, so cancellation equates those two
coefficients. Likewise a segment `Delta_P-e_q` equates states obtained
by swapping the missing label with one member of `Q`.

Thus every boundary equation identifies the weights of states related
by exchanging the missing label with one present label. This exchange
graph is connected: transpositions through the missing position generate
all assignments of the five labels to the two pairs and the missing
position. All 30 weights are equal, and each six-term facet normalization
sets the common value to `1/6`.

There are 60 boundary segments. The exact producer independently
canonicalizes their lattice translations and oriented edge directions,
checks that every segment occurs in precisely two states with opposite
signs, and checks the complete rational boundary system. The full system
has rank 30, agreeing with uniqueness. Restricting each facet to the
four noncrossing ordered pair partitions leaves 20 columns and augmented
rank 21, so that restriction cannot give the required cycle.

The obstruction is already present at the first lift of this particular
one-paramid base. Selecting a preferred ordering, a cyclic suborbit, or
only its noncrossing copies cannot replace the full orbit. To pursue an
exponential homological construction, a coherent lift must introduce
additional facet-chain freedom, such as explicit coning-kernel
corrections, instead of merely reweighting these base copies.

Files: `overnight_upper_ordered_lift.py/.json` and their bounded-run log
and exit record. The argument is mathematical, not Lean verified.
