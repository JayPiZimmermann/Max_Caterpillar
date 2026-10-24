# Defect at most one: exact seven-label separation and uniform exclusion

Status: an exact finite Fourier certificate, a mathematical coordinate-
deletion proof, and an independent checker. **Not Lean-verified.** This
does not settle the unrestricted all-tree exponential lower bound.

## Model and defect

A full canonical tree unit has a tree `G` on the `n=N-1` nonapex labels,
head `x_r-x_a`, every edge retained as a unit-coefficient function
`sigma(x_u-x_v)`, and arbitrary orientations. Normalize each pair to
`u<v` using hinge reversal, and put

\[
\kappa_v=h_v+\#\{(v,w)\text{ among the normalized pairs}\}.
\]

At a nonapex vertex this equals the outdegree in the original orientation
plus `1_(v=r)`. Thus `kappa_v>=0`, `sum_v kappa_v=n`, and the apex has
coefficient `-1`. Define the defect `d` as the number of nonapex vertices
with `kappa_v=0`.

For a fixed tree, the normalized function is determined by `kappa`:
its normalized head is `h_v=kappa_v-outdegree_<(v)`. Consequently:

* `d=0` means `kappa=1` everywhere;
* `d=1` means `kappa=1+e_s-e_t` for two distinct vertices `s,t`.

Every ordered pair `s,t` is realizable. Orient the tree towards sink `t`
and use head root `s`. The case `s=t` realizes `d=0`, and the resulting
function is independent of that common mark. Thus arbitrary roots and
orientations with `d<=1` introduce no additional functions beyond this
description. Nonadjacent `s,t` are included.

## Exact finite result

At `N=7`, all six nonisomorphic six-vertex tree shapes, with every
ordered mark pair and the zero-defect case, give **81 function orbits**
under label permutations. All `7!` labelings are included in each orbit
sum. A first modular probe gave ranks `60/61`; that was only diagnostic.

The exact gate uses 61 frequency multisets. Each has six distinct positive
entries from `[10,20)` and their negative sum. These are nonsingular for
all the cut denominators. For each row, a power of `lcm(1,...,B)` clears
every denominator, so the entire orbit sum is computed with integers.
No rational reconstruction or floating-point approximation is used.

The exact ordinary/augmented matrix ranks are **60/61**. The saved integer
left-kernel vector annihilates all 81 orbit columns and has a nonzero
value on the maximum column. After incorporating the row denominators,
it is a finite rational-evaluation functional separating the maximum
from the real span of this full family modulo `L_5`.

Files:

* `lower_defect_review_probe.py` and `lower_defect_review_probe_7.json`:
  the initial modular proposal and exhaustive defect-closure controls;
* `lower_defect_review_exact.py` and `lower_defect_review_exact_rows_7.json`:
  all 61 exact scaled rows, scales, frequencies, and representatives;
* `lower_defect_review_separator_7.json`: integer row weights and nonzero
  target, with content hashes;
* `lower_defect_review_check.py`: independent coverage and arithmetic
  checker, with receipt `lower_defect_review_check_7.json`.

The checker enumerates all 1,296 labelled six-vertex trees through
Pruefer sequences, checks every root and orientation on the six shapes,
and recovers precisely the same function-orbit family. It recomputes
every exact row using normalized integer heads and positive-endpoint
cuts. The producer instead used inward-root representatives and cuts
away from the head root. Finally the checker verifies every annihilation
and the nonzero target by integer dot products, without FLINT or solving
a linear system. The established generic Fourier formula and the
lower-dimensional Fourier vanishing statement are the mathematical
bridge; this is not a kernel-level Lean certificate.

## Coordinate deletion never increases defect

Use the operator `T_j=(partial_{-e_j}-partial_{e_j})` followed by inserting
zero at coordinate `j`, in full coordinates. For deletion at arity
`m>=4`, it maps `L_(m-2)` into `L_(m-3)`, and maps `max_m` exactly to
`max_(m-1)`. A surviving tree top class can only come from deleting a
nonapex leaf. The other cases either expose a zonotope in `L_1` or fix
at least two segments and therefore have dimension at most `m-3`.

For a leaf `j` with neighbour `v`, there are three cases:

* `kappa_j=0`: the leaf is not the head root and its edge is sourced at
  `v`. Its deletion subtracts one from `kappa_v`, so
  `d'=d-1+1_(kappa_v=1)<=d`.
* `kappa_j=1`: either the leaf sources its edge and is not the head root,
  or it is the root receiving its edge. In the latter case the head
  transfers to `v`, exactly compensating for the removed outgoing edge
  at `v`. In both cases the remaining `kappa` values are unchanged and
  `d'=d`.
* `kappa_j=2`: the leaf is the root and sources its edge. The next top
  class vanishes.

The `m>=4` qualification matters: an apex deletion gives a zonotope in
`L_1`, which is in the next lower-dimensional span only from this arity
onwards. We use deletions only at arities above seven.

Compose the exact seven-label separator with `N-7` coordinate deletions.
Every full canonical unit with `d<=1` remains in that class or vanishes
in the successive top quotient. The maximum remains the maximum, and
`L_(N-2)` maps into `L_5`. Hence the uniform mathematical result is

\[
\max_N\notin\operatorname{span}\{U:\ d(U)\leq1\}+L_{N-2}
\qquad(N\geq7).
\]

In particular, the face-closed dictionary generated by these full units
cannot construct `max_N`: any nonhinge face state at the original arity
has at most `N-3` generators and lies in `L_(N-2)`. This uniformly rules
out the complete defect-at-most-one construction family, including all
tree shapes and all realizable orientations in that class.

## Actual top ties preserve the surviving kappa values

For a full unit, use the maximum localities from the lower-bound argument:
tie the chosen coordinates at zero and freeze the others at distinct generic
negative values, chosen so a zero outer preactivation forces coefficientwise
outside balance. Consider ties of at least three labels. At a nonzero top
germ, the apex is tied and the other tied labels form a connected subtree.
Every boundary hinge sourced at a tied
vertex becomes a linear term with coefficient `+1` there; this replaces
exactly its previous contribution to that vertex's outdegree. A boundary
hinge sourced outside is inactive. Thus

\[
\kappa_{\rm germ}(v)=\kappa_{\rm original}(v)
\quad\text{at every surviving nonapex label}.
\]

The germ defect is exactly the number of original zero-kappa vertices
retained in the tie set, and in particular is at most the original
defect. This is a statement about maximum localities with all untied
coordinates below the tie, not arbitrary exposed directions.

Zero-kappa vertices of a full canonical tree form an independent set:
an edge contributes one to the outdegree of one endpoint. At a surviving
tie, a zero-kappa vertex is tied if and only if at least one neighbour
is tied. The forward implication uses connectedness of the nonapex tied
subtree; the reverse is the outside-balance condition. Therefore all
zero-vertex memberships are determined by the positive-kappa vertices.
A full unit with `d` zeros has at most `2^(n-d)` eligible tie sets,
where the apex is fixed. Large defect would supply an exponential saving;
the exact `d<=1` exclusion alone does not force linearly large defect.

## Essential face-state caveat

The uniform top-span exclusion above remains valid after adding faces
at that same original arity. But defect need not stay small when a full
unit is replaced by a face state before taking a smaller tie germ.
For an edge sourced at `u` and ending at `v`, linearization subtracts one
from `kappa_v`, while omission subtracts one from `kappa_u`. Faces can
therefore create additional zeros or negative kappa values.

Consequently the locality count and original-to-germ defect bound cannot
silently be applied to all faces of a low-defect full unit using the
original full unit's defect. A lower-bound theorem for such mixed face
dictionaries needs an additional bridge or the actual face description's
kappa values. No such unrestricted all-tree exponential bound is claimed
by this certificate.

## Reproduction

```sh
P=research/sN/dfs/h4-general-neurons/venv/bin/python
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/lower_defect_review_probe.py 7
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/lower_defect_review_exact.py rows
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/lower_defect_review_exact.py solve
OPENBLAS_NUM_THREADS=1 "$P" research/sN/trees/lower_defect_review_check.py
```

Each exact phase has a 120-second budget. Exact row construction took
45.0 seconds; nullspace production and integer checks took 0.10 seconds.
The independent checker recomputed all rows in 40.46 seconds and exited
successfully. It checked all 1,152 root/orientation choices on the six
shapes, including 396 allowed choices, and recovered all 81 function
orbits; its separate Pruefer enumeration checked all 1,296 labelled trees.
The solve phase uses the already installed python-flint in the research
`h5-growth` environment. The standalone checker does not need FLINT.
