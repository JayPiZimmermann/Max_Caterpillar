# Independent audit of the raw-array segment bridge

Auditor: triple-contact Lean worker. This note first checks the intended
mathematical signature; the final paragraph records whether the actual
Lean declaration has also been inspected. It does not certify the support
classification that supplies the hypotheses in the Max5 search.

## Intended statement

Let

```
g(x) = sum_j c_j ReLU(A_j dot x),
h(x) = sum_j d_j ReLU(A_j dot x).
```

Assume MAX5 = R + ReLU(g) + ReLU(h) on every real input, with R an arbitrary
affine-plus-shallow-ReLU function. Assume both cores vanish at q3=-e3 and
q4=-e4. Fix a physical row k, and suppose every j different from k satisfies

```
A_j3=0  or  A_j4=0  or  A_j3+A_j4=0.
```

For w(p,q)=|p| when p+q=0, and w(p,q)=0 otherwise, assume

```
sum_{j != k} c_j w(A_j3,A_j4) = 1,
sum_{j != k} d_j w(A_j3,A_j4) = 1.
```

The conclusion A_k3+A_k4=0 is mathematically correct.

## Row restriction and coefficient normalization

At x(t)=-t e3-(1-t)e4, the row with p=A_j3, q=A_j4 is

```
ReLU((q-p)t-q).
```

If p=0, this equals (1-t) ReLU(-q) for 0<=t<=1.
If q=0, it equals t ReLU(-p) on that interval. Thus either omission gives
an affine term and no interior hinge.

If p+q=0, the same function is ReLU(-p(2t-1)). For p<=0 it equals
|p| ReLU(2t-1). For p>=0 it equals

```
|p| ReLU(2t-1) - p(2t-1).
```

Consequently the coefficient in front of the canonical hinge
ReLU(2t-1) is exactly |p|, with no missing factor of two. Reversing a row's
orientation changes its affine part but leaves this coefficient unchanged.
The intersection p=q=0 contributes zero under either case.

Summing all rows except k therefore gives, for each core, an affine
function plus exactly one copy of ReLU(2t-1). The exceptional physical
row contributes a second hinge with A=q_k-p_k and B=-q_k. The scalar
`SegmentBalance.crossing_balanced` conclusion A/2+B=0 is exactly
-(p_k+q_k)/2=0, hence the claimed coordinate balance.

## Zero coverage and endpoints

The exact expected type of `TripleContact.max5_weighted_pair_contact`
permits arbitrary affine shallow R, g, h. The homogeneous cores here are
special cases with zero affine term and zero first biases. At each
0<t<1, take positive weights a=t, b=1-t and distinct coordinates 3,4.
It gives g(x(t))=0 or h(x(t))=0 without a genericity assumption or a
strict sign choice. The endpoints satisfy x(0)=q4 and x(1)=q3, so all
four endpoint assumptions required by the scalar balance theorem follow.

## Boundary cases and precise scope

- All core coefficients are arbitrary real numbers; zero coefficients
  and cancellation are retained.
- Repeated and oppositely oriented physical rows are retained. Their
  signed coefficients multiply the same nonnegative hinge weight and
  are summed explicitly.
- A row supported on additional coordinates can satisfy p+q=0. The bridge
  deliberately retains such balanced nonroot rows because their
  restrictions have the same midpoint hinge.
- The distinguished row k need not be nonzero, used by either core, or
  unbalanced in the hypothesis. If already balanced, the conclusion is
  immediate; the proof is still valid.
- The row restriction permits at most one unbalanced crossing physical
  row. It does not silently consolidate several unbalanced parallel
  physical rows into one. Applying it to such a group would require an
  additional explicit consolidation lemma.
- The conclusion is only A_k3+A_k4=0. It does not assert that A_k is
  supported on {3,4}, is a comparison normal, or is unused.
- This is a bridge for a specified reduced representation. It does not
  assert that every ordinary Max5 network admits the two-core reduction,
  the endpoint zeros, or the two normalized coefficient sums.

## Implementation audit

**Semantic signature: PASS.** The final declaration
`SegmentNetwork.exceptional_row_balanced` was inspected in
`SegmentNetwork.lean`. Its primitive arrays, endpoint assumptions,
row-wise disjunction, two signed midpoint masses, global exact identity,
and coordinate-balance conclusion match the intended statement above.
`core`, `midpointWeight`, `midpointMass`, and `contactPoint` were unfolded
for this inspection. The helper `core_shallow` embeds the homogeneous
cores by setting their affine term and every first bias to zero, without
changing their actual finite sum.

The finite-sum proof isolates the physical row k with `Finset.univ.erase k`;
it neither deletes zero rows nor chooses orientation representatives.
It separately decomposes each remaining row and sums its signed midpoint
coefficient. The assembled scalar arguments are A=A_k4-A_k3 and B=-A_k4,
so the final scalar conclusion has the advertised sign and factor.

This is an independent mathematical and signature audit. Compilation and
axiom status should be taken from the segment-network worker's final
exact-type receipt, not inferred from this note. The audited proof uses
only the previously checked scalar balance and full-segment zero-core
lemmas plus explicit row algebra. It makes no implicit support-cover or
network-classification claim.

The subsequent `no_three_coordinate_exception` declaration was also
inspected. It adds a third label r distinct from 3 and 4, explicit zero
entries outside {r,3,4}, an explicit zero row sum, and A_k r nonzero.
`sum_three_coordinate_support` proves the full five-coordinate sum equals
A_k r+A_k3+A_k4. The already proved balance then forces A_k r=0,
contradicting the stated nonzero entry. This conclusion is sound. The
formal hypotheses do not require A_k3 or A_k4 to be nonzero, so they retain
boundary cases and are slightly more general than the prose phrase
“exactly three coordinates.” Invariance is assumed only where actually
used, for the exceptional row's zero sum; it is not inferred from the
support description. No additional support classification is hidden in
this corollary.
