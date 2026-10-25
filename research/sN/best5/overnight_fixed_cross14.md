# The nine-row first hidden layer now has an upper bound of fourteen

The rational network in `overnight_fixed_cross_net9_14_simple.json`
equals the maximum of five real inputs globally and has widths (9,14).
Every coefficient belongs to `{0,1/2,-1/2,1,-1}`. Its first hidden layer
is exactly the P4 comparison layer in the earlier (9,17) construction.
The separate certified lower bound in `overnight_root9.md` is six for
this same first hidden layer, so the current interval is **6<=h2<=14**.
This is not a matched result and remains outside the paper.

The second hidden layer consists of two neurons encoding the reference
coordinate plus a first-layer linear combination, three neurons whose
interior creases cancel, and nine correction neurons. The initial mixed-
integer search produced an equally valid network with some coefficients
of magnitude eight. A subsequent exact-pattern linear solve removed those
arbitrary magnitudes; the simpler network is the preferred artifact.
The initial network and its receipt are retained separately as
`overnight_fixed_cross_net9_14.json` and its companion check file.

Both networks independently pass `overnight_fixed_cross_verify.py`, the
standalone exact checker described in `overnight_fixed_cross.md`. The
simplified network has eight groups of cancelling interior hyperplanes
across all 120 braid cones. After cancellation, the checker compares the
remaining input gradient coefficientwise with the maximizing coordinate.
Continuity covers every cone boundary. This is a rational global
certificate, not a sampled test or a Lean theorem.

Reproduce the preferred upper certificate with:

    python3 overnight_fixed_cross_verify.py overnight_fixed_cross_net9_14_simple.json

The bounded search's optimal correction count is not claimed as a lower
bound: it fixes a cancellation pattern, a finite family of correction
sign cones, and parameter bounds. Neither the original (9,17) manifest
nor its checked artifacts has been changed.
