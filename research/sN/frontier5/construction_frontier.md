# Max5 construction frontier and scope audit

Checkpoint: 2026-10-29. This note concerns exact computation of the maximum
of five arbitrary real inputs by an ordinary ReLU network with two hidden
layers, no skip connection, and a linear output. Widths are written in
first-hidden-layer, second-hidden-layer order. Padding propagates each
upper bound to all coordinatewise larger widths.

## Current exact frontier

| Question | Current result | Scope and source |
|---|---|---|
| Minimum first hidden layer width | Exactly 9 | Arbitrary finite second width and arbitrary real weights. `../best5/overnight_fixed_first9_paper.tex` combines the finite first-layer classification and rectangle obstruction; `overnight_fixed_first9_paper_manifest.json` pins the sources. |
| Certified construction at first width 9 | **(9,11)** | New C5 weights: `max5_nine_c5_atoms_o2_r1.network.json`; independent all-input receipt: `max5_certificate_9_11_c5.json`. The previous `(9,14)` P4 construction remains certified. |
| Certified construction at first width 10 | (10,6) | Physical weights: `../best5/netB_10_6.json`. |
| Minimum second hidden layer width, arbitrary first width | Between 4 and 6 | `../best5/overnight_fixed_second4_manifest.json`, `overnight_fixed_unrestricted.md`, and `overnight_fixed_complete_status.md`. A general exclusion of widths 4 and 5 is open. |
| Minimum second width over the displayed nine-row P4 layer | Between 7 and 14 | Latest lower bound: `../best5/overnight_fixed_p4_k4.md`. The older `overnight_fixed_cross14.md` lower endpoint 6 is superseded. |
| Minimum second width over the displayed ten-row bowtie layer | Exactly 6 | `../best5/overnight_fixed_bowtie.md`: four free outer neurons are necessary and sufficient; the coordinate carrier requires two more. This does not exclude a different first layer with second width 5. |

Thus the currently certified undominated upper pairs are **(9,11)** and
(10,6). These are not asserted to be the complete optimal Pareto frontier.
At each fixed first width 10, 11, and 12, the minimum second width is
currently between four and six. A dedicated search is tracked in
`matching_bounds_current.md`.
Within the bowtie family, adding any one or two coordinate-comparison
features leaves the exact minimum second width at six. These extension
lower bounds now have independently checked proof certificates; see
`max5_first11_identity.md` and `max5_first12_status.md`. They do not
exclude smaller second widths with other first dictionaries.
For the broader family whose nonzero invariant first directions are
coordinate differences, second width four is now excluded through first
width twelve, even with arbitrary noninvariant carriers. Its minima at
ten, eleven, and twelve are therefore between five and six; see
`max5_root12_singleton_tail.md`. Nonroot invariant directions remain
outside this lower bound.
At first width 9, the necessary row-sum splits are (1,1,7) and (2,2,5),
where the entries count positive-sum, negative-sum, and zero-sum first
rows. The second split is not excluded. Consequently the fixed-P4 lower
bound 7 cannot be substituted for an unrestricted lower bound at width 9.
See `../best5/overnight_fixed_first9_splits.md`.

## New minimum-first-width construction

The C5 construction has nine first-hidden-layer neurons and eleven
second-hidden-layer neurons. Its first features are the positive parts of

```
x1-x0, x1-x2, x3-x2, x3-x4, x4-x0,
x0, -x0, x2, -x2.
```

The emitted physical matrices have rational coefficients. The independent
arbitrary-direction checker exhaustively verifies 134 full-dimensional
first-activation/winner cells and 157 interior ridge groups, with 3,650
exact feasibility calls. Continuity covers all boundaries and ties. This
improves the upper point at first width nine from `(9,14)` to `(9,11)`;
it does not prove optimality of the second width eleven. Source and exact
receipt are linked in the table above. The existing P4-specific lower
bounds do not apply to this different first dictionary.

The old artifact `../kN/max5_chain7.json` describes seven correction
neurons before carrying its shallow remainder. Its name is not a claim
of a physical first width or physical second width of seven. The Lean
artifact `Max5General4` describes four correction neurons and compiles
through the larger paper dictionary to (16,6); the sparse physical
realization (10,6) is the better upper point listed here.

## A transparent identity behind the (10,6) construction

Write `relu(a)=max(a,0)` and take `x1` as the reference coordinate. Set

```
u=x0-x1, v=x2-x1, s=x3-x1, t=x4-x1,
p=relu(u), q=relu(v), r=relu(s), z=relu(t),
U=max(u,v), V=max(s,t),
H=V-U, K=(p+q-r-z)/2.
```

The four correction neurons implement the exact identity

```
max(0,u,v,s,t)
  = p + relu(H) - relu(H+K)
      + relu(q-p-r+z)/2 + relu(q-p+r-z)/2.
```

The actual eight invariant first-hidden-layer neurons are

```
relu(u), relu(u-v), relu(-v), relu(v),
relu(s), relu(-t), relu(t), relu(s-t).
```

They supply `H` because

```
H = relu(s-t)+t-v-relu(u-v),
v = relu(v)-relu(-v),
t = relu(t)-relu(-t).
```

The two remaining first-hidden-layer neurons are `relu(x1)` and
`relu(-x1)`. The first two second-hidden-layer neurons carry the head
`x1+p` as `relu(x1+p)-relu(-x1-p)`. The four correction neurons above
complete the six-neuron second hidden layer. The output weights are
`1,-1,1,-1,1/2,1/2` in the physical JSON's order.

Here is a short proof of the identity. Put `A=p+q`, `B=r+z`,
`C=abs(p-q)`, and `D=abs(r-z)`. The head `p` plus the last two
correction terms is `(A+max(C,D))/2`, by
`relu(a+b)+relu(a-b)=a+max(abs(a),abs(b))`.

* If `U,V>=0`, then `U=(A+C)/2` and `V=(B+D)/2`.
  Hence `H+K=(D-C)/2`. Removing this correction changes
  `(A+max(C,D))/2` into `U`, and the remaining correction
  `relu(V-U)` produces `max(U,V)`.
* If `U<0<=V`, then `A=C=0`. Both `H` and `H+K=D/2-U`
  are positive. Their difference is `B/2`; together with `D/2`
  this gives `V`.
* If `V<0<=U`, then `B=D=0`. Both `H` and `H+K=V-C/2`
  are negative, so the result is `U`.
* If `U,V<0`, all of `A,B,C,D` vanish and the two `H`
  terms cancel, giving zero.

This gives a merge algorithm for two pairs together with a reference
input. The negative-output correction removes the excess introduced by
the two absolute-difference corrections. Their intermediate creases can
cancel: requiring every second-layer neuron individually to follow the
target's ordering cones would incorrectly rule out this construction.

## An exact two-parameter family with noncanonical first rows

This construction also immediately has deformations beyond neuron scaling.
For arbitrary real parameters `alpha,beta`, replace the last two
first-hidden-layer neurons by `relu(ell),relu(-ell)`, where

```
ell = x1 + alpha*(x2-x1) + beta*(x4-x1).
```

Replace the two signed head preactivations by plus and minus

```
ell + p - alpha*(relu(v)-relu(-v))
        - beta*(relu(t)-relu(-t)).
```

The displayed expression is identically `x1+p`. Every correction neuron
is unchanged. This proves exactness for all parameters and all inputs,
with the same widths (10,6). The two carrier rows have coordinate sum
plus and minus one, fixing their positive-scaling normalization. Varying
`alpha,beta` therefore gives a two-dimensional family even after positive
neuron rescaling and neuron permutation are quotiented out. Generic
carriers have three nonzero coordinates and are neither a coordinate
difference nor a signed coordinate. The straight parameter path to
`alpha=beta=0` connects them to canonical first rows.

The parameter slice is a copy of the plane, not merely a pair of tangent
directions: the normalized positive-sum carrier determines `alpha,beta`
uniquely. Within the restriction that the other eight first-layer
functions and all second-layer preactivation functions stay fixed, this
is the full carrier-tilting family. Indeed, the globally linear functions
in the span of those eight invariant functions are exactly `span(v,t)`.
The two opposite-orientation pairs supply these linear functions; every
other first-layer hyperplane occurs in only one orientation and its
curvature must have zero coefficient in a linear function. Consequently
no other linear carrier displacement can be absorbed in that span.

This family supports the possibility of canonical representatives in
components; it does not prove that every Max5 solution admits such a path.
It changes the internal coordinate carrier while leaving the six
second-layer preactivation functions identical, so it is a representation
deformation rather than a different comparison algorithm.

`construction10_6_family.py` emits its exact rational weights. For example:

```
python3 research/sN/frontier5/construction10_6_family.py \
  --alpha 1/3 --beta 1/3 \
  --output research/sN/frontier5/construction10_6_tilted.json
```

For these parameters the carrier is `(x1+x2+x4)/3`. The independent
general-direction verifier `../best5/cert.py` freshly passed all 120
braid cells and 517 refined linear regions, with 4530 exact
Fourier--Motzkin calls and zero failures. See
`construction10_6_tilted_check.log`. The symbolic argument above proves
the whole real-parameter family; this separate certificate validates the
emitted noncanonical example.

## Fresh verification

`construction10_6_check.json` records a fresh independent exact check of
the physical (10,6) network: all 720 augmented braid cones pass, including
192 interior-hyperplane groups. The checker groups proportional crossing
hyperplanes, verifies that their signed curvature cancels, then compares
the remaining gradient with the winning coordinate. Continuity covers
cone boundaries. This is an all-input rational certificate, not a sampled
test. Reproduce it with:

```
python3 research/sN/best5/overnight_fixed_physical_verify.py \
  research/sN/best5/netB_10_6.json \
  research/sN/frontier5/construction10_6_check.json
```

The construction9 audit and its two fresh verification receipts are
separate files in this directory. `construction9_audit.md` also records
two restricted compression exclusions: an exact 19-by-19 determinant
excludes deletion by output reweighting and head adjustment alone, and
twelve rational Farkas certificates exclude deleting any one outer neuron
while varying all 91 coefficients with current braid-cell wall directions
and sign patterns fixed. The latter replay was run again from this audit
and passed all twelve cases without a numerical solver. It is not a
global lower bound or a separately implemented checker. No smaller
construction was obtained, and no new unrestricted optimality claim is
made by these construction checks.
