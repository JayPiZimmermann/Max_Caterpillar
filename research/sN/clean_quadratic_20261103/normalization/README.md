# A simpler normalization route for the quadratic paper proof

The manuscript fragments `normalization.tex` and `normalization.md` give
self-contained mathematical proofs of bias removal, diagonal normalization,
coordinate localization, and support regularization. Only the new coordinate
localization and its linear algebra are formalized by the Lean modules here.

`AnchorLift.lean` defines an explicit lift from selected coordinates: selected
values are unchanged and every outside coordinate is assigned one selected
anchor value. It proves:

* The lift preserves every constant diagonal vector.
* At a point tied at zero on the selected coordinates and negative elsewhere,
  MAX of the perturbed lifted point equals the selected MAX times the step,
  for every positive step, not just sufficiently small steps.
* The explicit pullback of linear forms preserves their coordinate sums.

`AnchorLocalization.lean` applies the existing exact directional rule once,
in the original dimension, then pulls back along the anchor lift. It proves
an actual exact normalized MAX representation on any nonempty selected set,
retaining both original hidden-layer index types. A first row survives with
its original restricted coefficients exactly when its whole support lies in
the selected set. The generic tied point is constructed inside the theorem.
No second diagonal normalization is performed.

The formal construction uses `localize` (the scalar first- and second-gate
directional rules at the same point) and `anchorPullback`. It does not invoke
`normalizeOuter`, the previous second diagonal pass. Importing the old
localization module only supplies the first-order identities and tied-point
existence; it does not turn the new result into a wrapper around the old
normalized-restriction theorem.

The independent `AnchorCheck.lean` checks literal expected types and concrete
nonvacuity controls. Run

    python3 research/sN/clean_quadratic_20261103/normalization/recheck.py --run

for source-closure build, exact-type, axiom, and source-hash evidence. The
receipt is an isolated research receipt, with no production-facade promotion.

`ordinary_linear_bound.md` records a separate elementary mathematical proof
of h2>=ceil(N/2) for the ordinary architecture. This auxiliary result and the
recession/support-averaging manuscript proofs are not claimed to be newly
Lean-verified by this directory's receipt.
