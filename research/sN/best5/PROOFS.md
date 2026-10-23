# Proofs of the lower bounds and reductions (max_5, two hidden layers)

Notation. σ = ReLU. A network is `F(x) = Σ_k d_k σ(g_k(x))`, `g_k(x) = Σ_j W_kj σ(a_j·x)`,
zero biases, **no** linear or skip term at the output or inside the second layer.
Biases are no restriction for positively homogeneous targets (Hertrich–Basu–Di Summa–Skutella,
SIAM J. Discrete Math. 37 (2023), Prop. 2.3; Haase–Hertrich–Loho, ICLR 2023, Lemma 7), and all
statements below are about zero-bias networks with the same widths.

Translation behaviour. Split the first-layer rows by `s_j = 1·a_j`:
`J+ = {s_j > 0}`, `J- = {s_j < 0}`, `J0 = {s_j = 0}` (translation-invariant rows).

## Lemma 0 (one hidden layer cannot compute max_3)

`max(z_1,z_2,z_3)` is not of the form `ℓ(z) + Σ_k c_k σ(b_k·z)` (any linear ℓ, any rows b_k).
Proof. Such a function is smooth off finitely many hyperplanes `b_k·z = 0`, and across each
hyperplane `H` its gradient jumps by the same vector at every point of `H` outside the other
hyperplanes (the jump of `c σ(b·z)` across `b·z = 0` is `c b`, other terms are smooth there).
`max_3` is non-differentiable on `{z_1 = z_2 > z_3}` but differentiable on `{z_1 = z_2 < z_3}`,
both open parts of the hyperplane `z_1 = z_2`; the gradient jump is `e_1 - e_2` on the first and
`0` on the second. Contradiction. ∎

## Lemma 1 (germs)

If `F = max_N` on `R^N` and `p ∈ R^N`, then for `z` near 0, `max_N(p+z) - max_N(p)` equals
`ℓ_p(z) + Σ_{j: a_j·p = 0} c_j σ(a_j·z) + Σ_{k: g_k(p) = 0} d_k σ(μ_k·z + Σ_{j: a_j·p=0} W_kj σ(a_j·z))`
with suitable linear `ℓ_p`, `μ_k` and reals `c_j`. All terms are positively homogeneous in `z`,
so the identity holds for all `z ∈ R^N`.
Proof. Rows with `a_j·p > 0` are linear near `p`, rows with `a_j·p < 0` vanish near `p`;
second-layer neurons with `g_k(p) > 0` are equal to `g_k` near `p` (contributing linear terms and
`σ(a_j·z)` terms with `a_j·p = 0`), those with `g_k(p) < 0` vanish near `p`. ∎

## Theorem H1 (first width, any first layer): h1 ≥ 7 for max_5

(i) `|J+| ≥ 1` and `|J-| ≥ 1`: on the diagonal `x = t·1`, rows in `J0` are 0, rows in `J+` vanish
for `t < 0`, rows in `J-` vanish for `t > 0`. If `J- = ∅`, `F(t1) = F(0) = 0 ≠ t` for `t < 0`;
symmetrically for `J+`.

(ii) `|J0| ≥ 5`. Apply Lemma 1 at `p = 1`: only `J0` rows survive, giving
`max_5(z) = ℓ(z) + Σ_{J0} c_j σ(a_j·z) + Σ_k d_k σ(μ_k·z + Σ_{J0} W_kj σ(a_j·z))` on `R^5`. (∗)
For `I ⊂ [5]` apply Lemma 1 to (∗) at `q = (0 on I, -M_o off I)` with `M_o > 0` generic, so that
`a_j·q ≠ 0` for every `J0` row whose support is not inside `I`. Near `q` the maximum is attained
in `I`, so (setting `z_o = 0` off `I`)
`max_{i∈I} z_i = ℓ'(z_I) + Σ_{supp a_j ⊆ I} c'_j σ(a_j·z) + Σ_k d_k σ(μ'_k·z + Σ_{supp a_j ⊆ I} W_kj σ(a_j·z))`. (∗∗)

(C3) `|I| = 3`: if no `J0` row has support in `I`, (∗∗) writes `max_3` with one hidden layer,
contradicting Lemma 0. So every 3-set contains the support of a `J0` row.

(C4) `|I| = 4`, `a ∈ I`, `Y = I \ {a}`: suppose no `J0` row `S` satisfies `a ∈ supp S ⊆ I`.
Then all rows in (∗∗) live on `Y`, and (∗∗) reads
`max(z_a, max_Y z) = ℓ'(z) + S(z_Y) + Σ_k d_k σ(m_k z_a + M_k(z_Y))`
with `S, M_k` one-hidden-layer functions of `z_Y` (linear part included). Fix generic `z_Y`. As a
function of `z_a` the left side is convex piecewise linear with one slope jump `+1` at
`t* = max_Y z`; the right side has slope jumps `w_k = d_k |m_k|` at `τ_k = -M_k(z_Y)/m_k`
(`m_k ≠ 0`). Equating jumps at every point and taking the first moment,
`t* = Σ_k w_k τ_k`, i.e. `max_Y z = -Σ_k d_k sgn(m_k) M_k(z_Y)`, a one-hidden-layer function of
three variables — contradicting Lemma 0. So for every 4-set `I` and `a ∈ I` some `J0` row has
`a ∈ supp ⊆ I`. (This is the claw argument of Lu, Lemma D.6, in this simpler homogeneous setting.)

(iii) Supports of `J0` rows have size ≥ 2 (sum zero, nonzero). Exhaustive enumeration
(`supports.py`, log `logs/supports.log`) of families of subsets of [5] of size 2–4 shows that
(C3)+(C4) need at least 5 sets; the minimal families are, up to S_5,
`C_5 = {01,02,13,24,34}`, `{01,02,034,13,24}`, `{01,02,123,124,34}`.

Hence `h1 = |J+| + |J-| + |J0| ≥ 1 + 1 + 5 = 7`. ∎

Remarks. (a) The bound uses no assumption on the second width. (b) If a free linear output term
were allowed, (i) would fail and the argument gives `h1 ≥ 5`. (c) Lu, Thm 2.13, gives
`C(5,2) - ⌊20/3⌋ = 4` for `d = 5`; the gain here comes from (i) and from the exact enumeration
for `d = 5`.

## Theorem H2 (second width, any first layer): h2 ≥ 2, and h2 ≥ k_B + 1

On `x + t1`, `t → +∞`: rows in `J+` become `a_j·x + s_j t`, rows in `J-` vanish, `J0` rows are
unchanged. So `g_k(x+t1) = T⁺_k t + G⁺_k(x)` for `t ≥ t_0(x)`, with `T⁺_k = Σ_{J+} W_kj s_j` and
`G⁺_k` translation invariant (linear part plus `J0` rows). Let `P+ = {T⁺_k > 0}`,
`Z+ = {T⁺_k = 0}`. Comparing with `max_5(x) + t`:
`Σ_{P+} d_k T⁺_k = 1` and `max_5 = Σ_{P+} d_k G⁺_k + Σ_{Z+} d_k σ(G⁺_k)`. (+∞)
Symmetrically at `t → -∞` with `T⁻_k = -Σ_{J-} W_kj s_j`, `P- = {T⁻_k > 0}`:
`Σ_{P-} d_k T⁻_k = -1`.
A neuron in `P+ ∩ P-` contributes `d T⁺ > 0` and `d T⁻ < 0` with `T^± > 0`, impossible for a
single neuron, so `P+ ∪ P-` has ≥ 2 neurons: `h2 ≥ 2`.
(+∞) is a representation `max_5 = (one-hidden-layer function) + Σ_{Z+} d_k σ(G⁺_k)`; if `k_B` is
the least number of such free neurons, `|Z+| ≥ k_B`, `|P+| ≥ 1`, so `h2 ≥ k_B + 1`. ∎

## Theorem A (model A: the paper's first layer): h2 = k(5) + 2 exactly, hence h2 ≥ 4

Model A: `Φ = (σ(x_0), σ(-x_0), σ(x_i-x_0)_{i>0}, σ(x_i-x_j)_{i<j})` (16 features for N = 5).
Because `σ(-x_0) = σ(x_0) - x_0` and `σ(x_j - x_i) = σ(x_i - x_j) - (x_i - x_j)`, every second-layer
input is `g = l·x + Σ_{i<j} a_ij σ(x_i-x_j) + α σ(x_0)`, and every such `g` is realized.
Let `k(5)` be the least `K` with `max_5 = R + Σ_{k<K} d_k σ(G_k)`, `R, G_k ∈ span{x_i, σ(x_i-x_j)}`
("free remainder", as in research/sN/NOTE.md).

Upper bound: `R = σ(R) - σ(-R)`, so `h2 ≤ k(5) + 2`.

Lower bound. With `T = Σ_i l_i`: `g(x+t1) = (T+α)t + G⁺(x)` for large `t`, `G⁺ = l·x + α x_0 + Σ a σ`,
and `g(x+t1) = T t + G⁻(x)` for very negative `t`, `G⁻ = l·x + Σ a σ`. By (+∞), `|Z+| ≥ k(5)` and
`|P+| ≥ 1`, so `h2 ≥ k(5) + 1`. Suppose `h2 = k(5) + 1`. Then `|Z+| = k(5)`, `|P+| = 1`, no neuron
is inactive at `+∞`, and likewise `|Z-| = k(5)`, `|P-| = 1`. The `P+` neuron `n` and the `P-` neuron
`m` differ (Theorem H2). So `n ∈ Z-` (`T_n = 0`, `α_n > 0`), `m ∈ Z+` (`T_m + α_m = 0`, `T_m < 0`),
and all other neurons have `T = α = 0` (fully translation invariant, `σ(G_k)`). With
`G'_n := l_n·x + Σ a σ` and `G'_m := l_m·x + α_m x_0 + Σ a σ` (both translation invariant):
- `+∞`: `max_5 = d_n G'_n + x_0 + d_m σ(G'_m) + Σ_other d_k σ(G_k)`, with `d_n α_n = 1`;
- `-∞`: `max_5 = d_n σ(G'_n) + d_m G'_m + x_0 + Σ_other d_k σ(G_k)`, with `-d_m α_m = 1`.
Subtracting, `d_n σ(-G'_n) = d_m σ(-G'_m)`; `d_n > 0 > d_m` forces both sides to vanish, so
`G'_n ≥ 0`, `σ(G'_n) = G'_n`, and the `-∞` identity is a free-remainder representation with
`k(5) - 1` neurons. Contradiction. Hence `h2 = k(5) + 2`. ∎

`k(5) ≥ 2`: a single free neuron would have to vanish identically on every 3-locality cell
`C_{T,ρ} = {x_t = s (t∈T), s > x_{ρ1} > x_{ρ2}}` (research/sN/NOTE.md, locality lemma: the third
mixed difference in the `T` coordinates kills `R` and every neuron not vanishing on the cell, and
equals `δ ≠ 0` on `max_5`). The vanishing equations have only the zero solution
(`k1_vanish.py`, exact, log `logs/k1_vanish.log`: nullspace dimension 0 for N = 5; the same as
`dfs/h4-general-neurons/r2_k1.py`). So `k(5) ≥ 2` and model A needs `h2 ≥ 4`.

## Theorem C (total): h1 + h2 ≥ 9 for any first layer

From H1 and H2. ∎
