# Uniform separation of arbitrarily oriented stars

Status: mathematical proof using the independently checked five-label
complete-flag separator. **Not Lean-verified.** This proves a uniform
all-oriented-star separation theorem. It does not prove the outward-twin
lemma for general trees, or an unrestricted all-tree exponential bound.

## Statement

For every `m>=5`, there is a linear functional `Lambda_m` on finite linear
combinations of polytope support functions on `R^m` which:

* annihilates `L_(m-2)`, the span of support functions of polytopes of
  affine dimension at most `m-2`;
* annihilates every canonical star unit
  `sigma(x_r-x_a+sum_l sigma(epsilon_l*(x_l-x_c)))`, where `a` is the apex,
  `c` the star centre, `r` any nonapex label, and all orientations
  `epsilon_l in {+1,-1}` are allowed;
* takes the value `120` on `max_m`.

The same functional kills every face-state variant of these star units:
if even one original edge is omitted or linear, the resulting pyramid has
at most `m-3` segment generators and dimension at most `m-2`.

## Coordinate deletion as a dimension-lowering linear operator

Work in full coordinates, which avoids any implicit choice of quotient
chart. For a label `j`, let `iota_j` insert a zero coordinate at `j`, and
define

\[
\mathcal T_j f(y)=
\bigl(\partial_{-e_j}f-\partial_{e_j}f\bigr)(\iota_j y).
\]

For a support function `h_P`, the two directional derivatives here are
the support functions of the minimum and maximum coordinate faces of `P`.
Hence `T_j` is linear on their span. Furthermore

\[
\mathcal T_j(L_d)\subseteq L_{d-1}\qquad(d\geq1).
\tag{1}
\]

If the coordinate is constant on `P`, its two exposed faces coincide and
their difference is zero. Otherwise each face has dimension at most
`dim(P)-1`. Restriction along `iota_j` replaces each face by its linear
projection, which cannot increase dimension. The same argument kills
`L_0` outright. This proves (1) without requiring any function to be
invariant under adding a common coordinate shift.

Directly,

\[
\mathcal T_j\max_m=\max_{m-1}.
\tag{2}
\]

Indeed, the minimum coordinate face of the standard simplex is the
simplex on all labels except `j`, while its maximum coordinate face is
the vertex `e_j`, whose support function vanishes after the restriction.

## What deletion does to a canonical star

Let its head be `h=e_r-e_a`, and write the base as the zonotope
`Z=h+sum_l [0,g_l]`, where `g_l=epsilon_l(e_l-e_c)`. The pyramid is
`Q=conv(0,Z)`. A base-only face is a translated zonotope, so its support
function lies in `L_1`. Modulo `L_1`, the deletion cases are:

| Deleted label | Retained class after `T_j` |
|---|---|
| Nonroot leaf `l`, with `g_l=e_l-e_c` | `+` canonical star with `l` deleted, same root |
| Nonroot leaf `l`, with `g_l=e_c-e_l` | `-` canonical star with `l` deleted, same root |
| Root leaf `r`, with `g_r=e_c-e_r` | `+` canonical star with `r` deleted, root transferred to `c` |
| Root leaf `r`, with `g_r=e_r-e_c` | zero |
| Apex `a` | zero |
| Centre `c` | zero |

For a nonroot leaf the base coordinate ranges from `0` to `1`, or from
`-1` to `0`. The face at coordinate zero contains the apex and the base
with that segment fixed at zero, yielding the smaller star. The other
face is a translated zonotope. If the leaf is the root, its base coordinate
instead ranges from `1` to `2`, or from `0` to `1`. Only the latter case
gives an apex-base face, with shifted head
`e_r-e_a+(e_c-e_r)=e_c-e_a`.

Deleting the apex exposes the whole base on one side and the apex on the
other. Deleting the centre fixes every segment at an endpoint, since every
segment has nonzero centre coordinate. Each exposed face is consequently
a point or a segment after optionally adjoining the apex. Both cases lie
in `L_1`. These arguments prove the table exactly, including all signs.

## Propagation of the exact five-label separator

Choose any five labels to retain, and any order of the other `m-5` labels.
Apply the corresponding deletion operators successively, then apply the
exact five-label complete-flag separator from
`all_tree_dfs/complete_flags_5.json`. Its independent vertex-based checker
is `dfs_review_flag_certificate.py`; it annihilates every canonical
five-label star and `L_3`, and takes value `120` on `max_5`.

By the deletion table, each canonical `m`-label star becomes a signed
canonical five-label star modulo `L_3`, or lies in `L_3`. Lower-dimensional
errors introduced at any stage stay harmless under subsequent deletions:
`L_1` maps to `L_0`, then to zero, and a final `L_1` error already lies in
`L_3`. Equation (1) also maps the original `L_(m-2)` into `L_3` after
exactly `m-5` deletions. Equation (2) maps `max_m` to `max_5`. The composite
is the asserted `Lambda_m`.

Thus the five-label certificate really does imply a **uniform** theorem
for all oriented stars. No finite-dimensional rank extrapolation is used.

## Consequence for the matching theorem

The mixed matching theorem in `orientation_audit_matching.md` can be
enlarged further. In addition to its base class `K0` and arbitrary tree
face functions `K1` with original matching number at least `k`, allow an
arbitrary third class `Kstar` consisting of star-tree face functions with
every root, orientation, and edge state. Then, for `N>=5` and
`0<=2k<=N-1`, every expansion of `max_N` satisfies

\[
|K_0|+|K_1|\ \geq\ \frac{(169/147)^k}{(N+1)^4}.
\tag{3}
\]

In particular, the star units are free in this lower count. The enlarged
dictionary is nonvacuous, since `K0` contains the caterpillar dictionary.

For a tie set of size `m>=5`, the canonical-head reduction turns every
surviving top germ of a star-tree face into a canonical star on that tie
set. Apply `Lambda_m` to the germ identity. All star terms and all
lower-dimensional terms vanish, while the maximum remains nonzero. Thus
some unit in `K0` or `K1` has a nonzero top class. The same passage and
connected-subtree counts now cover levels `m=5,...,N`, giving, for `y>0`,

\[
(1+y)^N-\sum_{j=0}^4\binom Nj y^j
\leq |K_0|\sum_{m=5}^N(6y)^m
   +|K_1|ny(1+y)^n\rho^k,
\qquad \rho=\frac{1+y+y^2}{(1+y)^2}.
\tag{4}
\]

Take `y=2/11` and `E=(13/11)^N(147/169)^k`. As in the matching proof,
`E>=(12/11)^N>=1`. Put `Z=|K0|+|K1|`; the nonzero maximum at any
five-element tie gives `Z>=1`. Therefore (4) implies

\[
(13/11)^N\leq
\left(\sum_{j=0}^4\binom Nj(2/11)^j+N-4+2n/13\right)EZ
\leq(N+1)^4 EZ.
\]

For the final elementary bound, use `2/11<=1`, `binomial(N,j)<=N^j`, and
`2n/13<=N`; the coefficient is at most
`N^4+N^3+N^2+3N-3 <= (N+1)^4`. Cancelling yields (3).

The remaining unresolved shapes are trees of sublinear matching number
which are not stars, with arbitrary orientations. The deletion argument
does **not** prove uniform outward-twin separation: deleting one of the
two outward leaves can remove the only twin pair and leave a surviving
canonical tree without twins.

## Exact checks

`python3 research/sN/trees/orientation_audit_stars.py` checked 14,784
exposed-vertex deletion cases: every root, orientation, and deleted label
for `m=5,...,9`, with apex and centre fixed by label equivariance. It
compares the exact vertex sets of the exposed faces with the predicted
smaller pyramid or translated zonotope; it does not sample functions.
All six cases in the table occurred. It also checked the maximum deletion
identity and the polynomial absorption for `5<=N<=500`. The run passed in
2.03 seconds with exit status zero. The receipt is
`orientation_audit_stars.json` and the log is `orientation_audit_stars.log`.

The existing independent checker was replayed under a 90-second budget:

```sh
OPENBLAS_NUM_THREADS=1 research/sN/dfs/h4-general-neurons/venv/bin/python \
  research/sN/trees/dfs_review_flag_certificate.py
```

It passed all 640 labelled canonical five-label stars and the
lower-dimensional controls, and returned `120` on the simplex, with exit
status zero. The fresh log is `orientation_audit_stars_base.log`. These
finite controls supplement the uniform deletion argument; the result is
not a Lean declaration.
