# A rectangle of curvature scores excludes every finite second width

**Result:** no finite shallow completion of the natural eight-row first
hidden layer computes `max_5`. Together with the independently checked
classification of every possible first hidden layer of width eight, this
proves the unrestricted minimum first hidden layer width is **nine**. The
exactly verified `(9,14)` network attains that first width. Its second
width is not claimed optimal.

The obstruction below is an analytic argument over arbitrary real
coefficients, with no finite coefficient enumeration. It was independently
reviewed by the general-bound agent. The last finite-sum identity is also
Lean verified, but the geometric model bridge is not yet formalized in
Lean. The earlier K4 and K5 packages remain unchanged; this result
supersedes their lower bounds for the natural eight-row layer.

## Model

Put

\[
 (a,b,c)=(\sigma(u),\sigma(v),\sigma(v-u)),\qquad
 (d,e,f)=(\sigma(s),\sigma(t),\sigma(t-s)).
\]

Each block image is the union of three cones between consecutive rays
`(1,0,0),(1,1,0),(0,1,1),(0,0,1)`. We allow an arbitrary linear remainder
in the six features and any finite signed sum of outer ReLUs of arbitrary
linear forms in those features. The desired function is

\[
 F=\max(a,b,d,e).
\]

It suffices to use four full four-dimensional corner cones:

| Corner | First block | Second block | Target |
|---|---|---|---|
| `00` | `c=0, a>=b>=0` | `f=0, d>=e>=0` | `max(a,d)` |
| `02` | `c=0, a>=b>=0` | `d=0, f>=e>=0` | `max(a,e)` |
| `20` | `a=0, c>=b>=0` | `f=0, d>=e>=0` | `max(b,d)` |
| `22` | `a=0, c>=b>=0` | `d=0, f>=e>=0` | `max(b,e)` |

Both `b` and `e` are independent coordinates on every corner span.
This fact is essential; the argument does not replace these cones by
their two-dimensional ray quadrants.

## Isolate one class of crossing hyperplanes

Consider a preactivation whose coefficients at `b,e` are `B,E`.
Only the class

\[
 B=-E\ne0
\]

can contribute to a hyperplane whose normalized `b,e` coefficients are
`1,-1`. No other class can cancel such a crossing hyperplane on any
corner, because the `b,e` coordinates remain independent there.

For each term in this class, use
`\(\sigma(-g)=\sigma(g)-g\)` if needed and positive homogeneity to
normalize its form as

\[
 g=\alpha a+b+\gamma c+\beta d-e+\varphi f.
\]

Its outer coefficient is an arbitrary signed real number `w`; normalization
multiplies the old coefficient by `|B|`. The sign flip contributes only
to the allowed common linear remainder.

On the four corners, this unit has normalized hyperplane parameters

\[
 (\alpha,\beta),\quad(\alpha,\varphi),\quad
 (\gamma,\beta),\quad(\gamma,\varphi),
\]

respectively. For a parameter pair `(x,y)`, the four extreme-ray values
of the restricted form are, up to order,

\[
 x,\quad x+1,\quad y,\quad y-1.
\]

Therefore it has fixed sign on the cone precisely when

\[
 (x\ge0\text{ and }y\ge1)
 \quad\text{or}\quad
 (x\le-1\text{ and }y\le0).
\]

Outside these two closed regions, its hyperplane crosses the cone's
relative interior. All degenerate boundary cases are included in the
fixed-sign regions.

## A score that is intrinsic modulo linear functions

Define

\[
 s(x,y)=\mathbf1_{x\ge0}-\mathbf1_{y\ge1}.
\]

It vanishes on both fixed-sign regions. On a corner, sum `w*s(x,y)`
over the normalized terms of the selected class.

This total depends only on the represented function modulo linear
functions on that cone. To justify this, consolidate identical crossing
hyperplanes. The normalization `b=1,e=-1` removes all proportionality and
orientation ambiguity, so distinct pairs `(x,y)` give distinct
hyperplanes. At a generic point on any one crossing hyperplane, avoiding
the finitely many others, its gradient jump forces its total signed
coefficient. In particular, a sum that is linear on the corner has total
coefficient zero for every crossing pair. Fixed-sign terms contribute
zero to the score. The discontinuity of `s` in its parameters is harmless:
no continuity in parameter space is used.

For the desired target, the scores are

\[
 S_{00}=0,\quad S_{02}=0,\quad S_{20}=0,\quad S_{22}=1.
\]

Indeed, the target normals on the first three corners are `a-d`, `a-e`,
and `b-d`, whose `b,e` coefficient pairs are `(0,0),(0,-1),(1,0)`.
They are outside the selected class. On corner `22`,
`max(b,e)=e+sigma(b-e)`, so the selected pair is `(0,0)` with coefficient
one and `s(0,0)=1`.

## The contradiction

Every normalized unit satisfies

\[
\begin{aligned}
 &s(\alpha,\beta)-s(\alpha,\varphi)
       -s(\gamma,\beta)+s(\gamma,\varphi)=0,
\end{aligned}
\]

because the score is the sum of a function of its first argument and a
function of its second. Multiplying by arbitrary signed outer coefficients
and summing over any finite number of units yields

\[
 S_{00}-S_{02}-S_{20}+S_{22}=0.
\]

The target's scores give one instead of zero. This proves the claimed
all-finite-width obstruction.

## Consequence for the unrestricted first hidden layer

The finite real-coefficient classification in
`../frontierN/overnight_general_six.md` proves that any hypothetical exact
five-input network with first hidden layer width eight has, after
recession, permutation, and positive row rescaling, the first-layer
functions

\[
 \sigma(x_0),\ \sigma(-x_0),\
 \sigma(x_i-x_0)\ (1\le i\le4),\
 \sigma(x_1-x_2),\ \sigma(x_3-x_4).
\]

Either matching edge orientation is covered by swapping the corresponding
pair of input labels. Restrict to `x0=0`; the two carrier features vanish,
and the remaining six features give precisely the product image above,
after swapping the names within each block. Any finite second hidden
layer would contradict the rectangle obstruction. Thus no first-width-eight
network exists, at any finite second width. The earlier unrestricted
`h1>=8` result excludes smaller first widths.

The rational network `overnight_fixed_cross_net9_14_simple.json`, checked
globally by `overnight_fixed_cross_verify.py`, has first width nine and
second width fourteen. Hence **the minimum possible first hidden layer
width for exact `max_5` is nine** in the arbitrary-real, arbitrary-bias,
no-skip two-hidden-layer model. This matches first width only; it does
not determine the minimum second width at first width nine.

## Verification, controls, and status

- `overnight_fixed_natural8_rectangle.lean` proves score vanishing on both
  fixed-sign regions, the rectangular identity, the target score, and
  impossibility of the four prescribed totals for every finite index set
  and arbitrary real weights and parameters. It does not claim to
  formalize the geometric hyperplane independence or first-layer
  classification.
- `overnight_fixed_natural8_allwidth_score.py` checks 49 rational closed
  sign-boundary cases and 9604 scaled-unit controls exactly. These are
  implementation controls, not an enumeration used to prove the uniform
  theorem.
- The previously constructed network matching all sixteen ray quadrants
  has score vector `(0,0,0,0)`, as required for a finite representation;
  the target has `(0,0,0,1)`. Thus this invariant detects precisely the
  full-cone information that that earlier control omitted.
- The localized-overlap expression `Q` from
  `overnight_fixed_localized_overlap.md` also has score vector zero.
  Its localized target contribution and its additional interval-overlap
  crease cancel in the score. Collective cancellation is fully allowed.

The independent review explicitly checked intrinsic coefficient classes,
normalization and signed weights, the full four-dimensional domains,
closed sign boundaries, generic-point crease independence, and the four
target scores. No gap was found. The original five-unit proof and its
manifest remain intact as a successful precursor.

## Complete scope audit for the matched first-width statement

The model is exactly

\[
 x\longmapsto b_3+\sum_{k=1}^{h_2}d_k\,
 \sigma\!\left(b_{2,k}+\sum_{j=1}^{h_1}W_{kj}
       \sigma(a_j\cdot x+b_{1,j})\right),
 \qquad x\in\mathbb R^5,
\]

with finite widths and arbitrary real coefficients and biases. It has no
input-to-hidden or input-to-output skip and no uncounted neurons. This is
`Network` in `MaxCaterpillar/Definitions.lean`. A learned raw-input linear
skip is not covered by the matched statement. The feature-linear remainder
allowed by the rectangle proof is a stronger local obstruction and is not
an extra input skip in the network definition.

**Affine biases.** Divide the output at `t*x` by `t` and let positive `t`
tend to infinity. Every layer bias disappears; the same weights and widths
compute the positively homogeneous maximum. The repository proves this
as `Network.eval_zeroBias_of_posHom` and `Network.toZ_eval_of_max` in
`MaxCaterpillar/Frontier/Basic.lean`, including output bias. The rectangle
proof is then applied to this homogeneous network. No assumption that
individual original affine rows pass through the origin is imposed.

**Arbitrary real rows and signs.** The classification allows all real
coefficient magnitudes. It partitions exact nonzero supports and all
coefficient-sign patterns, and uses lexicographic test points with a base
chosen sufficiently large for each fixed collection of real rows. It does
not restrict coefficients to a rational grid or bound their magnitudes.
Positive rescaling of a first row is absorbed by inverse rescaling of its
outgoing weights. Both orientations of either matching comparison are
included and are converted to the displayed block orientation by swapping
its two input labels. Output weights in the rectangle proof are arbitrary
signed reals throughout.

**Zero rows, degeneracies, and repetitions.** The earlier five-row support
certificate establishes `|J0|>=5`, and a singleton signed row class needs
at least six nonzero zero-sum features. Consequently first width eight
forces row-sum class sizes `(1,1,6)`. A zero row would reduce that effective
feature count and is already excluded by the preceding certificate.
The six-row classification enumerates support **multisets**, so repeated
supports and repeated or proportional rows are not silently discarded.
Within a sign profile coefficients may be arbitrarily close to zero;
actual zero coefficients instead belong to a smaller exact support and
are separately covered. The surviving profiles force six distinct pair
supports and the specified orientations up to the two independent
matching reversals. No generic-position assumption is used.

**Exact scope of the classification.** Its necessary feature-cell
factorization is uniform over every finite second width. The checker
covers 2767 labelled support multisets, 43 support orbits, and 58176
coefficient-sign profiles. Exactly four bowtie orientations survive.
Component equations force the same linear functional `ell=e0`; the
singleton positive and negative row-sum reductions then force the two
signed first rows to be positive multiples of `e0` and `-e0`. Thus the
coordinate carrier pair is a conclusion, not an assumption. The final
restriction `x0=0` in the rectangle argument is therefore legitimate.

**Trust boundary.** The existing classification is a complete exact finite
certificate plus a written real-parameter bridge, not a Lean theorem for
all networks. Its modular arithmetic is exact over the rationals because
all relevant matrices have at most six columns with entries zero or one,
so every determinant has absolute value at most `6!=720<1009`; this
includes augmented-rank and forced-equation tests. No modular claim is
made about unknown real coefficients. The new rectangle lemma is an
analytic theorem with independent review and a Lean-verified algebraic
core. The upper network is a separate exact rational, global cone
certificate. Their combination establishes a matched first-width result
with that mixed mathematical/certificate trust boundary; it does not
establish a fully Lean-verified minimum-width theorem.

**Upper bound and optimality convention.** The preferred nine-row network
has two hidden layers of widths `(9,14)`, zero biases, and coefficients in
`{0,1/2,-1/2,1,-1}`. Its independent checker verifies cancellation of every
interior hyperplane on every one of the 120 braid cones and then equality
of the remaining gradient to the maximizing coordinate. Homogeneity and
continuity complete the global check. This is an attained upper bound for
first width nine. The matched statement is exactly

\[
 \min\{h_1:\exists\text{ a finite }h_2\text{ and an exact network}\}=9.
\]

Neither `(9,14)` nor any pair with first width nine is asserted jointly
optimal. The certified interval for the particular nine-row first layer
remains `6<=h2<=14`.
