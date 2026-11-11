# Independent audit of the shared-contact obstruction

This is a mathematical audit, not a Lean verification of the support
classification. The local zero-core lemma used by the argument is separately
formalized in `../triple_contact/TripleContact.lean`.

I checked `segment_obstruction.md` against the actual two-positive-core
identity, including opposite first-row orientations, repeated root rows,
zero coefficients, and arbitrary signs of the two core values.

The argument is sound with “other first normals” understood to exclude
all rows parallel to the mandatory comparison normal `e3-e4`. Such parallel
rows are consolidated, rather than counted as exceptional nonroot rows.

The necessary root curvature is fixed without assuming a particular
orientation of a physical first row. At the unique contact `q0`, the
appropriately complemented first core has germ
`max(x3,x4)-max(x1,x2)`. Its consolidated curvature on the whole comparison
hyperplane `x3=x4` is therefore +1. The second core has the same +1 curvature
from its unique contact `q1`. Complementation preserves the three shared
zeros and only adjusts the shallow remainder within the same actual span.

For any homogeneous first feature, the exact additivity defect at
`q3,q4,q3+q4` is

    sigma(-a3)+sigma(-a4)-sigma(-a3-a4)
      = (|a3|+|a4|-|a3+a4|)/2.

It is zero when either coordinate is absent, and equals `|a3|` for a root34
normal. Summing coefficients therefore gives both core values equal to -1
when there is no nonroot row containing both coordinates. This contradicts
the necessary zero of at least one core at the three-way top tie. No
assumption on the outer gate signs near that tie is needed.

I also checked the stronger segment argument. If an exceptional row's knot
differs from the root knot, the side of the root knot with no other knot
extends to an endpoint. Zero coverage and endpoint vanishing force one
core to vanish on that entire side. Its nonzero jump then forces the other
core to vanish immediately on the opposite side; the other's nonzero jump
contradicts its zero endpoint on the first side. This proof works for
arbitrary nonzero consolidated root jumps, without requiring their signs
to agree. A nonexistent exceptional knot is included in the contradiction.

Thus a sole exceptional row must satisfy `a3+a4=0`. For exact support034,
the zero row sum then contradicts `a0 != 0`. For exact support0134, the
remaining balanced possibility is correctly left open by this argument.

The finite support count is separate: the frozen checker and receipt in
`../same_label/midpoint_cover.py` and `midpoint_cover_receipt.json` select
225 of the 387 retained same-label support classes, with physical root-row
counts 3:4, 4:47, 5:107, 6:67. This count depends on the existing audited
387-class cover. It does not prove the full (9,4) exclusion or improve the
unrestricted width interval 4 <= h2 <= 6.
