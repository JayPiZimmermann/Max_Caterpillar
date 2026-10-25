# Retaining the future attachment edge before averaging

The exact seven-label ear obstruction for the `D_6`-averaged kernel
does not test the full lower lift space. An ear singles out an old edge,
so averaging over rotations before adjoining it can discard relevant
correction states. This note specifies the refined finite test precisely.
It does not assert a uniform construction.

Let `V` be the cubical span of all raw labelings of the six product types
used in the exact six-label control, retaining exactly the labelings
whose triangle factors fit two noncrossing pages in the fixed cyclic
order. Mark the future attachment edge `{0,5}` and let

\[
R(i)=5-i\quad(0\le i\le5).
\]

This reflection preserves the edge and has permutation sign `-1`.
It splits `V` into two character spaces `V_+` and `V_-`. Since coning
is equivariant, its kernel splits as well. The known particular lift
`Y_6` is alternating under `D_6`, hence belongs to `V_-`. Every lift in
this space of the same simplex boundary is therefore of the form

\[
Y_6+K_-+K_+,
\qquad K_\pm\in\ker(\rho|_{V_\pm}).
\]

The complete inventory has 2,052 raw product descriptions and 1,026
reflection orbits. After dropping zero or proportional formal projected
chains, each character has 968 columns. Exact rational-function checking
gives:

| Reflection character | Rank after coning | Coefficient-kernel dimension |
|---|---:|---:|
| `-1` | 756 | 212 |
| `+1` | 752 | 216 |

Every kernel relation was checked exactly. In each basis, 27 relations
are zero already as formal cubical chains and may be dropped from any
subsequent operation. The remaining 185 and 189 chains span all the
needed correction states; they are not claimed to be formally linearly
independent.

## Both ear characters are required

Insert label 6 between labels 5 and 0. For a fixed reflection choice of
the ear triangle, write `gamma_r` for its boundary attached at `r`, using
the producer's convention that the two other vertices are listed in
increasing order. Extending `R` to fix label 6 gives

\[
R\gamma_0=\gamma_5,\qquad
R\gamma_5=\gamma_0,\qquad
R\gamma_6=-\gamma_6.
\]

The alternating `D_7` projection has reflection character `-1`.
Consequently, for any old state `X` of character `chi`,

\[
\operatorname{Alt}_{D_7}(X\gamma_5)
 =-\chi\operatorname{Alt}_{D_7}(X\gamma_0),
\]

and the root-6 ear vanishes after projection when `chi=-1`. It follows
that the complete relevant channel list is:

* old character `-1`: root-0 ears, with both reflections;
* old character `+1`: root-0 and root-6 ears, with both reflections.

Together with the particular lift this gives
`2*(185+1)+4*189=1128` output states. No attachment channel is lost by
this reduction. The inventory retains a quotient map from every source
state and records the exact orientation signs.

The resulting states share 3,958 oriented `D_7` product orbits. A
permutation contributes both the reversal signs of individual triangle
boundaries and the sign from reordering the degree-one factors. The
canonicalization routine was checked against explicit permutations of
the full cubical chains; it also detects an orbit that vanishes because
its stabilizer has incompatible signs.

This is the full linear span obtained by multiplying any affine lift in
the specified six-label space by the ear factors and then alternating
over `D_7`. Thus a negative result would exclude that whole marked ear
recurrence, while a positive result would give a new exact boundary lift.
It would not settle the complete two-page family or all arities.

The exact lower-state receipts are
`overnight_upper_marked_kernel_minus_6.json` and
`overnight_upper_marked_kernel_plus_6.json`. The shared output inventory
is `overnight_upper_marked_ear_inventory_7.json`; its bounded span gate
is `overnight_upper_marked_ear_probe.py`.

## Completed exact obstruction

The bounded gate completed successfully in 458.64 seconds. Its sampled
matrix had ordinary/augmented ranks `780/781`. All 348 independent
coefficient-kernel relations were then verified as exact rational
identities on every supporting-hyperplane orbit. Thus the ordinary
rational-function rank is at most `1128-348=780`, while a modular minor
proves that adjoining the target has rank at least 781. The target is
not in this output span. This is an exact finite obstruction, not a
claim inferred from a modular rank gap alone.

The exclusion retains the complete lower coning kernels, marks the
attachment edge before averaging, and includes both reflection
characters with every surviving ear root and reflection choice. It
therefore closes the possibility that the earlier ear obstruction was
caused only by premature dihedral averaging or by dropping lower
kernel corrections. The complete two-page product dictionary at seven
labels remains untested by this exclusion. A genuine reopening must
use a different extension operation, other lower source types, or
nonproduct relative states.

`overnight_upper_marked_bundle.py` extracts a compact replay artifact:
it stores selected modular minors, exact relations, the underlying
descriptions, and the particular six-label positive witness. Its replay
regenerates the two-page source coverage, recomputes all selected minor
entries, verifies both complete lower kernels, checks all attachment
channels, and checks all 348 output identities. Historical full sampled
matrices are unnecessary. No Lean verification or uniform construction
is claimed.
