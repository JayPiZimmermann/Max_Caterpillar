# Seven-neuron lower bound for the fixed nine-row P4 first hidden layer

**Certified, independently checked, not Lean verified.** For the fixed
first hidden layer below, every exact two-hidden-layer representation of
`max(x0,...,x4)` needs at least seven neurons in the second hidden layer,
with arbitrary real weights, signed output weights, and biases. The known
construction has fourteen neurons in that layer. Thus the current fixed
layer interval is **7 <= h2 <= 14**. This is not a statement about every
first hidden layer of width nine and is not a matching optimum. It stays
in research notes under the user's publication criterion.

Put `u=x1-x0`, `v=x2-x0`, `s=x3-x0`, `t=x4-x0`. The first hidden layer is

```
σ(u), σ(v), σ(v-u), σ(s), σ(t), σ(s-t), σ(v-t), σ(x0), σ(-x0).
```

It is exactly the first layer of the certified network
`overnight_fixed_cross_net9_14_simple.json`. The first seven functions
span a space W. Write `f=max(x0,...,x4)-x0` and let k_W be the minimum
number of terms in

```
f = R + sum_j d_j σ(g_j),   R,g_j in W.
```

The result proved here is **k_W >= 5**. All real coefficients and either
output sign are covered, with arbitrary remainder R in W.

## Translation carriers and biases

For this fixed first hidden layer, `h2_min = k_W+2`, as in the earlier
fixed-layer notes. Briefly, write each second-layer preactivation as
`v_j+a_j σ(x0)+b_j σ(-x0)`, where v_j belongs to W. At positive common
translation infinity, only the zero a_j slopes remain nonlinear, so there
are at least k_W such neurons and one positive passing slope. The negative
end similarly requires at least k_W zero b_j slopes and one passing slope.
Width k_W+1 would force unique passing neurons n,m at the two ends. Their
output signs are respectively positive and negative, so they are distinct;
the other slope of each is zero. Subtracting the two tail identities gives

```
d_n σ(-v_n) = d_m σ(-v_m),   d_n>0>d_m.
```

Both sides vanish, so the two passing terms can be absorbed into R,
leaving k_W-1 nonlinear terms, a contradiction. Conversely two opposite
ReLUs encode `x0+R`. This argument does not assume W contains all linear
functions. Taking the recession limit `F(tx)/t` removes arbitrary biases
without changing the first-layer directions or either width.

## The complete real-parameter certificate

The standalone checker rebuilds the necessary equations directly from the
actual first-layer rows: 26 generic top-tie mixed-difference equations and
23 Boolean-ray equations eliminating R. Its coefficient-flat inventory is
regenerated from all subsets of ten relevant hyperplanes. It has 383 flats
including zero; every real preactivation has one exact vanishing profile.
Each assigned exact profile is relaxed to its whole closed linear flat.
All boundary points are still included under their own exact profile.

Nonzero output magnitudes are absorbed into their preactivations. Four
nonzero terms therefore have sixteen sign assignments. The checker covers
repeated flats as well as distinct ones. Fewer terms are covered by splitting
a nonzero term into positive copies; zero nonlinear terms already contradict
the full mixed-difference equation. No coefficient bound, strict margin,
integer-weight assumption, or finite input sample is used.

There are 296,861 unordered covering quadruples and 4,749,776 sign cases.
The independent coverage algorithm joins two sorted pair lists; a separate
Burnside count agrees. Each flat's complete absolute-form arrangement fan
is checked exactly: 13,066 unoriented primitive integer rays covering
270,850 subsets of normals. On each chamber the absolute-value map is
linear, so these rays generate a cone containing every actual absolute
value vector.

The final certificate contains 266 rational combinations of the necessary
equations, each with right-hand side one. In 4,749,756 cases a combination
is nonpositive on every generator of every signed block, giving a direct
contradiction. The other twenty cases have closed triangle-facet trees,
with 449 nodes altogether: 143 branches and 306 rational-cone leaves.

The branch rule is simple. If three nonzero linear forms have an exact
relation `c0 f0+c1 f1+c2 f2=0`, their weighted absolute values
`v_j=|c_j| |f_j|` satisfy one of

```
v0=v1+v2, or v1=v0+v2, or v2=v0+v1.
```

All generators satisfy the three nonnegative triangle slacks. A zero slack
in a nonnegative conic combination forces every generator with positive
weight to have zero slack. Hence each closed branch retains just those
rays. All three branches are checked, including their overlaps and zero
boundaries. Each leaf is a rational equation combination with positive
right-hand side and nonpositive value on every retained generator. It
therefore excludes the whole retained nonnegative cone. An independent
mathematical review confirmed this conic-cover and closed-boundary argument.

The standalone checker imports no numerical solver or proof producer. It
independently checks the flat bases, cover masks, fan completeness, circuit
relations, every branch, every rational leaf, every template bit, and all
quadruple/sign cases. The replay passed in about twelve seconds. This is an
exact finite certificate with the geometric generic-tie and translation
bridges above; it is not a Lean theorem.

```
python3 research/sN/best5/overnight_fixed_p4_k4_verify.py
```

The positive-control checker also verifies that the existing twelve-free-
term construction satisfies all 49 necessary equations exactly:

```
python3 research/sN/best5/overnight_fixed_p4_k4_control.py
```

The main data are `overnight_fixed_p4_k4_certificate.json` and
`overnight_fixed_p4_flat_rays.jsonl`; the receipt is
`overnight_fixed_p4_k4_check.json`. The adjacent manifest lists every frozen
input and source dependency. Checkers write fixed receipt filenames, so run
in a copied directory when preserving frozen receipt hashes. The earlier
partial-stage manifests and proofs remain unchanged.

## Next matching construction target

An exact five-free-term identity in W would compile to a `(9,7)` network
and match this fixed-first-layer bound. The twelve-free-term upper bound
remains the best certified construction at this checkpoint. The lower
bound does not classify other seven-zero-sum-row first layers, nor the
possible `(2,2,5)` first-layer row-sum split at total width nine.
