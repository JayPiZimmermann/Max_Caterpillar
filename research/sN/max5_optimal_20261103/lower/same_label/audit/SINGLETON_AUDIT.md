# Case 277: independent audit of the singleton-triple constraints

Date: 3 November 2026. **PASS** for the mathematical necessity and the
six added clauses in `emit_singleton.py` / `case277_single.smt2`.
The underlying model and its existing scope are unchanged. This audit
does not establish arithmetic unsatisfiability or a new global width bound.

## Which first rows remain singular

The producer orders the physical supports as

    02, 12, 34, 012, 013, 0134, 014.

For the triple T={0,1,3}, precisely row 4 has support contained in T.
For T={0,1,4}, precisely row 6 does. Both normals have exactly three
nonzero coordinates and coordinate sum zero, so neither is a coordinate
difference on its triple.

Choose a generic point of the face where precisely the coordinates in T
tie for the maximum and the other two are strictly smaller. A first row
supported on T vanishes everywhere on this face. Any other invariant row
restricts to a nonzero linear function of the two outside coordinates
relative to the tied value, so its zero set has empty relative interior.
There are only finitely many rows; a point avoiding all their zero sets
therefore exists. Exactly the specified row is singular at that point.

Its local directional feature is ReLU of its original linear normal.
All other first features contribute linear functions or zero. Restrict
directions to the tied coordinates and remove their common translation.
The target becomes max(0,x,y), with one nonroot first line and otherwise
arbitrary linear terms. This argument does not require all five quadruple
contacts to be shared; the local lemma applies to the present three-shared
case directly.

## Elementary two-positive-fold calculation

Relabel the triple and, if needed, rewrite a reversed first hinge by
ReLU(-H)=ReLU(H)-H. The sole first line can be written

    H=alpha*x+beta*y,  alpha>0, beta>0.

This rewriting changes only an allowed local linear term. It does not
assume that the physical first feature can be reversed for free.

The half-plane H<0 contains the two distinct target crease rays x=0,y<0
and y=0,x<0. On that half-plane all first features are linear. If either
outer core were nonzero at the chosen base point, its outer ReLU would
linearize, leaving at most one folded linear function to produce these
two noncollinear rays. That is impossible. Thus both actual cores vanish
at the base point and both remain folded in the local germ.

The outer coefficients are positive. Hence an interior crease from either
fold cannot be canceled by the other fold in H<0, where the remainder is
linear. Each fold must carry one of the two target rays. The target's unit
gradient jumps, followed by permissible local core complementation, fix
the two forms on H<0 to x and y, and the remainder to zero there.

Their restrictions to H=0 have both signs. By continuity each linear
extension into H>0 must have a zero line crossing that open half-plane.
The target has only the ray x=y>0 there. Positivity again rules out any
other crossing, so both zero lines are x=y. Matching the boundary values
then forces the two global local preactivations to be

    x - ReLU(H)/(alpha+beta),
    y - ReLU(H)/(alpha+beta),

up to their independent complements and interchange. Their coefficients
on the single nonlinear first feature are nonzero and have identical
absolute magnitude 1/(alpha+beta).

Returning to the actual physical feature preserves equality of these
magnitudes: both coefficients are measured against the same normal, and
any positive rescaling multiplies both by the same factor. A local core
complement changes the sign of its coefficient only. Consequently the
global necessary conclusion for the unique singular row j is exactly

    g_j != 0,  h_j != 0,  and (g_j=h_j or g_j=-h_j).

No single global complement choice across the two triples is assumed.
The two disjunctions retain all independent sign combinations.

## Source and formula audit

The emitter rebuilds the original case-277 model with the original
coefficient gauge. It independently enumerates the singleton triples,
obtaining exactly (013,row4) and (014,row6), and adds precisely the three
displayed clauses for each. It does not import the broader helper
`max5_three_shared_singleton_criterion.py`, whose additional endpoint and
face-curvature conditions are outside this audit.

`check_singleton.py` independently reconstructs the support order and the
two singleton triples. It compares the emitted assertion set with the
original case277 formula and proves that no assertion was removed and
exactly the six claimed clauses were added. It checks source and metadata
hashes and finds no integer-division operation. The separate receipt is
`CASE277_SIX_SINGLETON_CLAUSES_AUDIT_PASS_NOT_UNSAT`.

The earlier notes `allfive_shared_rank.md` and `shared_rank_audit.md`
contain the same local geometric lemma; their hashes are pinned in the
receipt. The present audit checked its application to three shared contacts,
the nonzero conclusion, the actual coefficient convention, and independent
local complementation explicitly.
