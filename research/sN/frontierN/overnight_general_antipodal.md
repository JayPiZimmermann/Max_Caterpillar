# Uniform unrestricted second-width lower bound

**Result:** every exact two-hidden-layer ReLU network computing `max_N` on `R^N`, for every positive `N`, satisfies

```
N + 2 <= 2 h2,    equivalently h2 >= ceil(N/2) + 1.
```

The first hidden layer is arbitrary. All real weights and biases are allowed, every neuron counts, and there are no skip connections. This improves the previous unrestricted bound by one and removes the singleton-sign-row hypothesis of `second_width_half_succ`. It agrees with the attained second width three at `N=3,4`; at `N=5` it gives four, where a matching unrestricted construction remains open.

The direct opposite-input proof below supersedes the longer successful transverse-positivity route in `overnight_general_second_width.md` and `overnight_general_transverse.lean`. The latter remains a checked checkpoint, not the preferred proof route.

## Proof

Remove biases using the existing homogeneity reduction. Let `G_k^+` and `G_k^-` be the one-hidden-layer intercepts in the two diagonal asymptotic identities, with `G_k^-(x)=net.negIn.Gp k (-x)` in the repository convention. Their free neurons are those with zero asymptotic slope. The established free-neuron bound gives at least `ceil(N/2)-1` such neurons at either end.

If either end has at least two nonzero slopes, the desired bound follows immediately. Otherwise there is exactly one nonzero slope at each end. Both slopes are positive, because each end must contribute the nonzero diagonal output slope. Call the positive-end neuron `n` and the negative-end neuron `m`. The diagonal output slopes are `+1` and `-1`, respectively, so `d_n>0>d_m` and `n!=m`. Every other neuron belongs to the common free set `R`, of size `h2-2`.

For every second-hidden-layer neuron, the intercepts at *opposite* inputs satisfy

```
G_k^+(x) - G_k^-(-x) = b_k dot x,
b_k = sum_j W_kj a_j.                                      (1)
```

Indeed, a positive-sum first row appears linearly only at the positive end, a negative-sum row appears with opposite sign only at the negative end, and a zero-sum row contributes `sigma(a_j dot x)-sigma(-a_j dot x)=a_j dot x`. Thus every row contributes `W_kj a_j dot x` to (1).

Let `V` be the intersection of the kernels of `b_k`, for `k in R`. Its codimension is at most `|R|`. For `x in V`, compare the positive asymptotic identity at `x` with the negative one at `-x`. All terms in `R` cancel by (1), giving

```
max_N(x) - max_N(-x)
  = (d_n b_n + d_m b_m) dot x
      - d_n sigma(-G_n^-(-x)) + d_m sigma(-G_m^+(x))
  <= (d_n b_n + d_m b_m) dot x.                              (2)
```

Both the left side and the linear right side are odd functions on the vector space `V`. Applying (2) at `-x` therefore gives the reverse inequality. Hence `max_N+min_N` is linear on `V`.

The established max/min subspace theorem gives `dim V <= floor(N/2)+1`. Since `dim V >= N-|R|`, we obtain

```
|R| >= ceil(N/2)-1,
h2 = |R|+2 >= ceil(N/2)+1.
```

This also handles arities one and two. No continuity argument, coefficient case split, first-width assumption, or finite computation is needed beyond the existing max/min dimension theorem.

## Lean artifact and verification contract

The owned leaf `overnight_general_antipodal.lean` contains:

```
Gp_sub_negIn_same
second_width_half_plus_one
network_second_width_half_plus_one
```

The last declaration has the complete actual-network type, including arbitrary biases:

```
[NeZero N] -> (net : Network N h1 h2) ->
(forall x, net.eval x = Maximum N x) -> N + 2 <= 2*h2.
```

Reproduce from the repository root with one thread:

```
lake env lean -j1 research/sN/frontierN/overnight_general_antipodal.lean
```

The adjacent log records the compile and axiom outputs. The new leaf is research-owned and does not change a production import root or public verification manifest. The parent and independent fixed-layer agent reviewed the exact opposite-input identity, the negative output-weight sign, the odd-majorant step, both nonzero-slope cases, and the dimension count.
