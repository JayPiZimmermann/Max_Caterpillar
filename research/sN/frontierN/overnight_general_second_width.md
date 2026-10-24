# Unrestricted second width at least four for five inputs

**Status (2026-10-24): mathematical proof, independently reviewed by the parent and fixed-layer proof agent. Uses existing Lean-verified asymptotic and max/min subspace results. The complete new theorem is not yet Lean verified.**

Every exact two-hidden-layer ReLU network computing `max_N` on all of `R^N`, with arbitrary real weights and biases, no skip connections, and `N>=5`, has `h2>=4`. At `N=5` this combines with the independently checked first-width result in `overnight_general.md` to give `h1>=8`, `h2>=4`, and total width at least twelve. The `(10,6)` construction remains the known upper bound; the Pareto frontier is not determined.

## Reduction to three second-hidden-layer neurons

Biases can be removed by homogeneity without changing widths. Existing lower bounds exclude `h2<=2`. Suppose `h2=3`, initially with `N=5` or `N=6`.

For the two diagonal translation limits, write the established identities as

```
max_N(x) = sum_k d_k pi(T_k^+,G_k^+(x)),
max_N(x) = sum_k d_k pi(T_k^-,G_k^-(x)),
```

where `pi(T,G)` is `G`, `0`, or `sigma(G)` according as `T` is positive, negative, or zero. Every `G_k^±` is a continuous one-hidden-layer function, and `G_k^+ - G_k^-` is linear: their zero-sum first-row ReLU terms coincide.

The free-neuron lower bound forces at least two zero slopes in each identity. The diagonal slope identity supplies a positive-slope neuron `n` at positive infinity with `d_n>0`, and a positive-slope neuron `m` at negative infinity with `d_m<0`. Therefore `n!=m`; each is the unique nonzero-slope neuron at its respective end, and the remaining neuron `r` has slope zero at both ends. In particular there are no negative-slope second neurons in either limit.

If `d_r=0`, either identity writes the maximum as a one-hidden-layer function plus only one free outer neuron, contradicting the established free-neuron bound for `N>=5`. Thus `d_r!=0`.

Put

```
u = d_n G_n^-,                  alpha = d_n (G_n^+ - G_n^-),
v = -d_m G_m^+,                 beta  = d_m (G_m^+ - G_m^-),
w = |d_r| G_r^-,                delta = |d_r| (G_r^+ - G_r^-),
s = sign(d_r) in {-1,+1}.
```

Then `u,v,w` are continuous one-hidden-layer functions and `alpha,beta,delta` are linear. The identities become exactly

```
max_N = u + alpha - sigma(v) + s sigma(w+delta),
max_N = -v - beta + sigma(u) + s sigma(w).
```

Subtracting, and putting `L=alpha+beta`, gives the crucial global positivity identity

```
sigma(-u) + sigma(-v)
    = L + s [sigma(w+delta) - sigma(w)] >= 0.                 (1)
```

## Transverse positivity lemma

Assume first `delta!=0`, and let `H=ker(delta)`. On `H`, the right side of (1) equals `L`. Since a linear form nonnegative on a vector space is zero, `L|H=0`, and (1) gives `u,v>=0` on `H`.

We claim that `w` has one weak sign throughout `H`. Otherwise choose `z_+,z_- in H` with `w(z_+)>0>w(z_-)`, and fix `y` with `delta(y)=1`.

For all sufficiently small positive and negative `t`, continuity makes both `w(z_++t*y)` and `w(z_++t*y)+t` positive. Equation (1) then says

```
0 <= t [L(y)+s].
```

Both signs of `t` are allowed, so `L(y)=-s`. At `z_-`, both preactivations remain negative for both signs of sufficiently small `t`; (1) instead says `0<=t L(y)`, hence `L(y)=0`. This contradicts `s!=0`.

Thus either `w>=0` everywhere on `H` or `w<=0` everywhere on `H`. Consequently `sigma(w)|H` equals `w|H` or zero, respectively. The first asymptotic identity on `H` is therefore a one-hidden-layer function:

```
max_N|H = (u + alpha - v + s sigma(w))|H.
```

Every one-hidden-layer function has linear odd part. Thus `max_N(x)+min_N(x)` is linear for `x in H`. The existing max/min subspace theorem gives

```
N-1 = dim(H) <= floor(N/2)+1,
```

which is false for both `N=5` and `N=6`.

If `delta=0`, equation (1) gives `L>=0` globally, so `L=0` and `u,v>=0` globally. The first identity then expresses the maximum as a one-hidden-layer function plus only the single free neuron `s sigma(w)`, again contradicting the free-neuron lower bound.

This excludes `h2=3` at `N=5,6`. For `N>=7`, the already verified bound `h2>=ceil(N/2)` is at least four. Alternatively, restricting an `N`-input network by setting every input beyond the first five equal to the first input gives a five-input network with the same hidden widths.

## Why the previous cancellation route stopped too early

Restricting (1) only to `H` shows `u,v>=0`, leaving one free neuron on a codimension-one space; the ordinary free-neuron dimension bound permits this. The new step uses positivity at points *transverse* to `H`. It forces that last neuron's preactivation to have a uniform sign on `H`, eliminating it there. No coefficient grid, optimization, finite-dimensional sample, or first-width assumption is involved.

## Scope and formalization boundary

The proof requires the no-skip network model to force the positive and negative diagonal-pass neurons. It does not assert the same second-width bound with a free linear output or arbitrary skip connections. Arbitrary biases are covered by the bias-removal argument.

The existing Lean results supply the two asymptotic identities, the free-neuron count, the first-layer odd-linearity facts, and the max/min subspace dimension bound. The new parts are the transverse positivity lemma and its assembly with the exact three-neuron slope partition. The independent reviews explicitly checked normalization signs, the `d_r=0` case, both signs of the perturbation, and restriction to the subspace.
