# Independent cyclic-model review — 24 October 2026

The fixed cyclic-order candidate is refuted at five inputs in its stated
canonical-head, unit-edge-weight model. This does **not** rule out arbitrary
per-unit cycles, arbitrary graph units, or arbitrary inner coefficients.

## Fourier and tiling bridge

For a tree on nonapex labels, take a head `h` with `Σh_i=0` and `h_a=-1`.
Use `t=h·x` and the oriented edge differences as coordinates. The change
of coordinates has determinant of magnitude one. If deleting an oriented
edge leaves component `C` containing its positive endpoint, set
`q_C=Σ_(i∈C)ω_i`, `H_C=Σ_(i∈C)h_i`, and `a=ω_apex`. Summing the dual
coordinate equation over that component gives

\[
\omega_t=-a,\qquad \omega_e=q_C+aH_C.
\]

Therefore the generic Fourier transform, with the common nonzero factor
suppressed, is

\[
R(\omega)=\frac{(-a)^{N-4}}
 {\prod_e(q_C+aH_C)(q_C+a(H_C+1))}.
\]

This proves the formula used by `research/sN/cycles/cycle_fourier.py` for
general normalized heads; its validity is not based only on the finite
chamber-integral controls.

For a consistently directed simple cycle, the generators satisfy
`Σ_e g_e=0`. Every representative `t∈[0,1]^m` can be shifted to
`t-min_e(t_e)·1`, without changing its image in the zonotope. Consequently
the images of the `m` cube facets `t_j=0` tile the zonotope; their interiors
are disjoint because a generic representative has a unique minimum.
Each tile is exactly the deleted-edge path zonotope. The common apex is
outside the base affine span because `h_a=-1`, so coning preserves the
subdivision. Support functions therefore add modulo lower-dimensional
terms, justifying the Fourier tile sum.

An edge reversal changes the head by minus its original generator, as
implemented. For a cycle on `N-1` vertices, zero or one nonhinge edge can
contribute in dimension `N-1`; two nonhinge edges leave at most `N-3`
segments, so the pyramid has dimension at most `N-2`. Thus the producer's
full-cycle and deleted-edge-path cases include every relevant state case.

## Exact finite obstruction and its scope

`research/sN/cycles/cycle_obstruction_5.json` records 106 dihedral orbit
columns (1,040 labelled units), 32 independently verified rational-function
relations, rational rank at most 74, and modular augmented rank 75 at
prime 1,000,003. The exact verifier recomputes the modular evaluations and
checks relation independence after integer lattice reduction. This proves
that the five-input maximum is outside this fixed-cycle dictionary even
modulo lower dimension. The completed certificate took 19.64 seconds.

The scope is a fixed cyclic order, deletion of the chosen apex from that
order, a canonical head `x_r-x_a`, arbitrary edge orientations, and all
omitted/linear/hinge states with unit edge coefficients. Cycles with other
label orders, more general graphs, or more general coefficients remain
outside this negative certificate.

## Global first-layer graph obstruction

If the first hidden layer uses only coordinate-difference hinges on one
global graph `G` (plus linear channels), the existing C4′ lemma in
`research/sN/frontierN/PROOFS.md` implies: for every four-set `I` and every
`a∈I`, some edge joins `a` to `I\{a}`. Thus

\[
\delta(G)\ge N-3,\qquad |E(G)|\ge\binom N2-N.
\]

This condition holds regardless of the second hidden layer's width,
coefficients, or choice of graph units. A simpler independent-triple
argument gives `α(G)≤2`: otherwise a generic triple-maximum tie makes
the first hidden layer locally affine. The resulting one-hidden-layer
germ has linear odd part, whereas `max_3+min_3` is nonlinear. The C4′
condition is stronger.

Accordingly, a single global `C_N` cannot work from `N=6`, and a single
global `C_N^2` cannot work from `N=8`. The union of the fixed cyclic-order
graphs obtained by deleting one apex is `C_N^2`, so this also obstructs
that global feature architecture asymptotically.

These statements do **not** exclude varying cyclic graphs from unit to
unit: their union can be dense or complete and satisfy the necessary
condition. Nor do they imply that a cyclic unit can be replaced by one
tree unit. The tiling above uses several tree atoms with shifted heads.
The all-tree lower-bound head-flow argument also does not transfer to
cycles, because an outside component may have multiple attachments.
