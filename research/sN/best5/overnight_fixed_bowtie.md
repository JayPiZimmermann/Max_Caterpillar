# Matching second width for the fixed ten-row first hidden layer

**Status: exact finite certificate and mathematical model reduction,
independently checked; not Lean verified. The minimum second-hidden-layer
width for this fixed first hidden layer is exactly six.**

Set `u=x0-x1`, `v=x2-x1`, `s=x3-x1`, and `t=x4-x1`. Let `W` be the span
of these eight translation-invariant first-hidden-layer functions:

```
sigma(u), sigma(u-v), sigma(-v), sigma(v),
sigma(s), sigma(-t), sigma(t), sigma(s-t).
```

The first hidden layer under consideration consists of these functions
and `sigma(x1), sigma(-x1)`. It is exactly the first layer of the already
certified network `netB_10_6.json`.

Its minimum second-hidden-layer width is exactly six, with arbitrary
real weights and signed output weights.
Arbitrary biases do not improve this minimum: if a biased network equals
the positively homogeneous maximum, taking `F(tx)/t` as `t` tends to
positive infinity removes all biases while preserving its matrices and
widths. The known six-neuron construction has zero biases.

## Reduction to four free neurons

Write `f=max_5-x1`, and let `k_W` be the least number of outer neurons in

```
f = R + sum_(j<K) d_j sigma(g_j),   R,g_j in W.
```

For this fixed first hidden layer, the exact relation is
`h2*=k_W+2`. Here is a proof specialized to this layer, so it does not
assume that `W` contains arbitrary linear functions.

Every second-layer preactivation is

```
g_k(x) = v_k(x) + a_k sigma(x1) + b_k sigma(-x1),  v_k in W.
```

Translate `x` by `t` in all coordinates. At positive infinity only
neurons with `a_k=0` remain nonlinear, and the positive `a_k` neurons
give a remainder in `W` after the required linear term `x1` is removed.
Thus at least `k_W` neurons have `a_k=0`, and at least one has `a_k>0`.
At negative infinity the analogous facts hold for `b_k`.

If `h2=k_W+1`, each end has a unique passing neuron and all others have
zero slope there. The positive-end passing neuron `n` has `d_n>0`; the
negative-end passing neuron `m` has `d_m<0`, so they are distinct.
Consequently `b_n=a_m=0`, and all other neurons have `a=b=0`. The two
translation identities give

```
f = d_n v_n       + d_m sigma(v_m) + common,
f = d_n sigma(v_n) + d_m v_m        + common.
```

Subtracting yields `d_n sigma(-v_n)=d_m sigma(-v_m)`. The two signs force
both sides to vanish. The passing neurons can therefore be absorbed
into the remainder, leaving only `k_W-1` free neurons, a contradiction.
For the reverse inequality, write `x1+R=sigma(x1+R)-sigma(-x1-R)`.
Both preactivations are available from the fixed first layer.

The existing network supplies `k_W<=4`. The new finite calculation
excludes `k_W<=3`, giving the matching equality `k_W=4` and `h2*=6`.

## Continuous parameter domain and necessary equations

Absorb every nonzero output magnitude into its preactivation, leaving
`d_j` equal to `+1` or `-1`. Put `v_j(S)=g_j(1_S)`. Each `v_j` is a
quadratic Boolean function with zero values on the empty and full sets.

For a top triple tie `T` and next label `o`, a neuron contributes to the
third mixed difference only if `v_j(T)=v_j(T union {o})=0`. For a
four-label tie `U` it contributes only if `v_j(U)=0`. At the full tie it
always contributes. For a contributing neuron,

```
Q_U(v_j) = sum_(empty != S proper subset U)
             (-1)^(|U|-|S|) |v_j(S)|
          = 2 mu_U(sigma(g_j)).
```

The remainder is annihilated because its Boolean degree is at most two.
The target gives `2*(-1)^(|U|+1)`. These are 20 triple equations, five
four-tie equations, and one full-tie equation.

There are also 22 equations eliminating the free remainder. The 30
nontrivial Boolean rays give a `30 by 8` first-feature value matrix of
rank eight. For each row `a` in its left kernel,

```
sum_S a_S sum_j d_j |v_j(S)|
  = 2 sum_S a_S (1 - 1_{1 in S}).
```

This follows by writing `2 sigma(g)=g+|g|` and absorbing the linear
combination of the `g_j` into `W`. These equations use the actual fixed
feature span; they are stronger than the equations for an arbitrary
remainder in the full span of coordinate-difference functions.

The exact vanishing sets among the 15 triples and four-sets form 623
flats, including the zero flat. Every real preactivation has one exact
vanishing set in this list. The search assigns equations using that
exact set, then relaxes its parameter domain to the entire corresponding
linear flat. Boundary points with additional zeros are covered again
under their own exact vanishing set. No nonzero magnitude cutoff is
used, and irrational coefficients are included.

The 622 nonzero flats yield 30,041 unordered covering triples. All
eight output signs are retained, giving 240,328 cases. The six flats
whose mixed-difference contribution vanishes identically are included.
Zero preactivations or zero output coefficients reduce to at most two
free neurons, already excluded in the independently checked certificate
documented in `overnight_fixed.md`.

## Independent proof gate

`overnight_fixed_bowtie_coverage.py` independently regenerates the flat
lattice by recursive kernel intersections, checks the producer's bases
and every contribution mask, then regenerates every covering triple.
It uses only Python's standard library and does not import the search.

`overnight_fixed_bowtie_verify.py` rebuilds the 48 direct equations from
the actual first-layer rows. Most cases have rational cone separation
certificates using nonnegativity of absolute values and, when needed,
inequalities of the form

```
sum_(i != j) |c_i| |l_i(x)| >= |c_j| |l_j(x)|,
where sum_i c_i l_i = 0.
```

The checker verifies the displayed linear dependence before accepting
such an inequality. It checks each rational Farkas sum against the
unreduced direct equations, so it trusts neither the equation reduction
nor a numerical solver's status.

The remaining cases carry closed-sign proof trees. The checker first
verifies exact row-space equality of their compressed systems and the
direct equations. It then checks both signs at every branch and every
rational contradiction. An independent global reversal of each
preactivation is valid because all equations involve absolute values.

The positive control `overnight_fixed_bowtie_control.py` substitutes the
known four-free-neuron construction into all 48 independently rebuilt
equations. Its check passes. The original global cone verifier
`cert.py` checks the six-neuron upper bound separately.

The independent check passed all 240,328 cases in 214.25 seconds. The
3.4 MiB compressed proof contains 240,144 cone certificates and 184
closed-sign trees. The latter have 139,512 binary splits, 8,474 constant
contradictions, and 131,222 rational Farkas contradictions; the cone
certificates use 18,157 explicitly verified circuit inequalities.
The proof SHA-256 is
`8509278c66a6791361c06f8cc06cf04467c4ff33359a9d713d61958f61be5b5f`.
The complete receipt is `overnight_fixed_bowtie_check.json`.

The upper verifier also passed again: all 120 braid cells and all 392
refined linear regions, with 3,658 exact Fourier–Motzkin calls and no
failure. See `overnight_fixed_bowtie_upper_check.log`.

Reproduce the independent gate from this directory:

```
python3 overnight_fixed_bowtie_coverage.py
python3 overnight_fixed_bowtie_verify.py
python3 overnight_fixed_bowtie_control.py
python3 cert.py netB_10_6.json
```

To reproduce the proof producer, use the existing research environment
and run bounded chunks until its completion receipt is written:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  ../dfs/h4-general-neurons/venv/bin/python \
  overnight_fixed_bowtie_certify.py --budget 1200
```

Archived search-verdict logs are optional method-selection hints only.
Without them the producer tries the basic cone, the ray/circuit cone,
and then the closed-sign tree. The independently checked proof artifact
and the checker do not depend on those logs. A completed producer rerun
preserves the existing proof bytes.

This is an exact finite certificate plus the written model reduction,
not a Lean-verified unrestricted width theorem.

## What this does and does not settle for eight first-layer neurons

The natural eight-row layer retains `sigma(u),sigma(v),sigma(s),sigma(t)`,
`sigma(u-v),sigma(s-t)`, and the two reference-coordinate carriers.
Its invariant feature span is a subspace of `W`, so the matching fixed10
lower bound also proves that this layer requires second width at least
six. The independent first-width classification in
`../frontierN/overnight_general_six.md` identifies every possible
eight-row first layer with this form, up to positive scaling and
relabeling. This transfers the lower bound to the entire `h1=8` slice.

It does not supply a network with `h1=8`. Whether that layer can realize
the target at any finite second width, and in particular at width six,
remains open. The established upper construction has first width ten.

For construction search, the image of each three-feature group
`(a,b,p)=(sigma(u),sigma(v),sigma(u-v))` is the union of the cones

```
a=b+p, b,p>=0;     p=0, 0<=a<=b;     b=0, 0<=a<=p.
```

The group maximum is `a+b-sigma(a-p)`. The product of two such images
has nine four-dimensional cones. The structured dictionary instrument
equates exact local gradient jumps on every cone, allowing unwanted
bends to cancel, and includes the Boolean-ray equations. A rational
solution would therefore be a global identity, subject to independent
verification. Primitive integer coefficient boxes through `[-4,4]^6`
have yielded numerical residuals, not a construction. Those residuals
are not an arbitrary-real or arbitrary-width impossibility proof.
