# General-N width bounds for exact two-hidden-layer ReLU networks computing max_N

Model and notation as in `research/sN/frontier4/PROOFS.md`: `F(x) = Σ_k d_k σ(g_k(x))`,
`g_k(x) = Σ_j W_kj σ(a_j·x)`, no biases (no loss for max_N), no skip term.
`s_j = a_j·1`; `J+, J-, J0` = rows with `s_j > 0, < 0, = 0`. `supp a = {i : a_i ≠ 0}`.
By Lemma T (`(+∞)`): for all `x`,

    max_N(x) = R(x) := Σ_k d_k π(T_k, G_k(x)),   G_k(x) = Σ_j W_kj ρ_j(x),

with `π(T, G) = G` if `T > 0`, `0` if `T < 0`, `σ(G)` if `T = 0`, and `ρ_j(x) = a_j·x` (`j ∈ J+`),
`0` (`j ∈ J-`), `σ(a_j·x)` (`j ∈ J0`). (Lean: `ZNet.max_plus`, `ZNet.rest`.)

## Lemma C4 (claw lemma, every N)

Let `I ⊆ [N]`, `a ∈ I`, `Y = I \ {a}` with `|Y| ≥ 3`, and let `q` satisfy `q_i = 0` (`i ∈ I`),
`q_o ≤ -1` (`o ∉ I`). Then some row `j ∈ J0` has `a_j·q = 0` and `a_j(a) ≠ 0`.

Proof. Suppose every `j ∈ J0` with `a_j·q = 0` has `a_j(a) = 0`. Write `e = e_a`.

*Row expansion.* Let `γ_j = a_j` if `j ∈ J+` or (`j ∈ J0`, `a_j·q > 0`), else `γ_j = 0`; let
`r_j(z) = σ(a_j·z)` if `j ∈ J0` and `a_j·q = 0`, else `0`. If `|a_j·z| < |a_j·q|` for every
`j ∈ J0` with `a_j·q ≠ 0`, then `ρ_j(q+z) = ρ_j(q) + γ_j·z + r_j(z)` for every `j` (case check).
Moreover `r_j(z + τe) = r_j(z)` (as `a_j(a) = 0` for the rows in question), `r_j(εz) = ε r_j(z)`
(`ε > 0`), and `r_j(z) - r_j(-z)` is linear. Hence, with `u_k = G_k(q)`,
`c_k = Σ_j W_kj γ_j`, `m_k = c_k(a)` and `g_k(z) = c_k·z + Σ_j W_kj r_j(z)`:

    G_k(q + z + τe) = u_k + τ m_k + g_k(z),  g_k(εv) = ε g_k(v) (ε > 0),  g_k(v) - g_k(-v) linear in v,

whenever `z + τe` satisfies the smallness condition.

*Choice of δ.* Fix `0 < δ < 1/2` with `δ|a_j(a)| < |a_j·q|/2` for the `J0` rows with `a_j·q ≠ 0`
and `δ|m_k| < |u_k|/2` for every `k` with `u_k ≠ 0`. Put `H(x) = R(x + δe) - R(x - δe)`.

*Network side: `H(q+εv) - H(q-εv) = ε·C·v` for a fixed covector `C`, for each `v` and all small
`ε > 0`.* For small `ε` the smallness condition holds at `z = ±εv`, `τ = ±δ`. Neuron `k`
contributes `d_k Q_k` with

    Q_k = [π(u+δm+εα) - π(u-δm+εα)] - [π(u+δm+εβ) - π(u-δm+εβ)],  α = g_k(v), β = g_k(-v)

(indices `k` dropped, `π = π(T_k, ·)`). If `T_k > 0`: `Q_k = 2δm - 2δm = 0`. If `T_k < 0`: `0`.
If `T_k = 0` and `u ≠ 0`: all four arguments have the sign of `u` once `ε|α|, ε|β| < |u|/2`,
so `Q_k = 0`. If `T_k = 0`, `u = 0`: `m = 0` gives `0`; `m > 0` gives (for `ε|α|, ε|β| < δm`)
`Q_k = (δm+εα) - (δm+εβ) = ε(α-β)`; `m < 0` gives `Q_k = -ε(α-β)`. Since `α - β = g_k(v) - g_k(-v)`
is linear in `v`, the claim follows.

*Maximum side.* `H = max_N(· + δe) - max_N(· - δe)`. For `i ∈ Y` and small `ε` (`ε < δ`):
`H(q + εe_i) = δ - ε`, `H(q - εe_i) = δ - 0` (some other `Y` coordinate is 0), so `C_i = -1`.
For `v = 1_Y`: `H(q + ε1_Y) = δ - ε`, `H(q - ε1_Y) = δ + ε`, so `-2ε = ε Σ_{i∈Y} C_i = -|Y| ε`,
contradicting `|Y| ≥ 3`. ∎

(This is the "claw" condition of Lu, Lemma D.6, and best5 H1 (C4); here for every `N` with
the two-point difference `H` in place of slope-jump moments.)

## Lemma G (generic point)

For finitely many rows `a_j` and `I ⊆ [N]` there is `q` with `q_I = 0`, `q_o ≤ -1` (`o ∉ I`), such
that `a_j·q = 0` implies `supp a_j ⊆ I`. Proof: `q_o = -t^{o+1}`; `a_j·q = -P_j(t)`,
`P_j = Σ_{o∉I} a_j(o) X^{o+1}`, which is a nonzero polynomial unless `supp a_j ⊆ I`; take `t ≥ 1`
outside the finitely many roots. ∎

Corollary (C4'). For every 4-set `I` and `a ∈ I` some `j ∈ J0` has `a ∈ supp a_j ⊆ I`; since
`s_j = 0`, `|supp a_j| ≥ 2`.

## Lemma K (covering count)

Let `S_1, …, S_M ⊆ [N]` (repetitions allowed) satisfy: for every 4-set `I` and `a ∈ I` some `S_j`
has `a ∈ S_j ⊆ I` and `|S_j| ≥ 2`. Then `6M ≥ N(3N - 11)`, i.e. `M ≥ C(N,2) - ⌊4N/3⌋`
(tight for N = 4..9 by `cover_ilp.py`).

Proof. Fix `a`. `D_a = {b ≠ a : some S_j = {a,b}}`, `U_a = [N] \ ({a} ∪ D_a)`, `m = |U_a|`, so
`|D_a| = N - 1 - m`. Let `R3_a` (`R4_a`) be the indices `j` with `|S_j| = 3` (`4`), `a ∈ S_j`,
`S_j \ {a} ⊆ U_a`. For a 3-set `Y ⊆ U_a`, apply the hypothesis to `I = Y ∪ {a}`: the set `S_j` found
is not `{a,b}` (then `b ∈ Y ∩ D_a = ∅`), so `j ∈ R3_a ∪ R4_a` and `S_j \ {a} ⊆ Y`. A `j ∈ R3_a`
serves at most `m - 2` sets `Y` (`Y = (S_j\{a}) ∪ {y}`), a `j ∈ R4_a` at most one. So
`C(m,3) ≤ (m-2)p + t` with `p = |R3_a|`, `t = |R4_a|`, which implies `4p + 3t ≥ 6m - 16`
(`m ≤ 5`: finite check; `m ≥ 6`: `3(m-2)(4p+3t) ≥ 12(m-2)p + 12t ≥ 2m(m-1)(m-2)` and
`2m(m-1) - 3(6m-16) = 2(m-4)(m-6) ≥ 0`). Hence `6|D_a| + 4p + 3t ≥ 6N - 22`.
Summing over `a`: a 2-set is counted in at most 2 sets `D_a` (and `|D_a|` is at most the number of
indices with `S_j = {a,b}`), a 3-set index in at most 3 sets `R3_a`, a 4-set index in at most 4
sets `R4_a`, so `12M ≥ Σ_a (6|D_a| + 4|R3_a| + 3|R4_a|) ≥ N(6N - 22)`. ∎

## Theorem Q (first width, every N)

Every two-hidden-layer network computing `max_N` exactly on `R^N` (biases allowed) has
`6 h1 ≥ 3N² - 11N + 12`, i.e. `h1 ≥ C(N,2) - ⌊4N/3⌋ + 2`.
Proof. Lemma K applied to the supports of the `J0` rows (Corollary C4') gives `6|J0| ≥ N(3N-11)`;
`J+` and `J-` are nonempty (Lemma T). ∎

Comparison: the construction of the paper has `h1 = C(N,2) + N + 1`, so the minimal first width is
`N²/2 + Θ(N)`. Lu (Thm 2.13, cube domain) has the same leading term `C(N,2) - ⌊4N/3⌋` for cores.

---

## Lemma 3 (subspaces on which max + min is linear)

Let `s` be a finite index set, `V ⊆ R^ι` a linear subspace and `L` a linear functional with
`max_s x + min_s x = L(x)` for all `x ∈ V`. Then `dim V ≤ dim(V ∩ {x|_s = 0}) + ⌊|s|/2⌋ + 1`.
In particular (`s = ι = [N]`): **`dim V ≤ ⌊N/2⌋ + 1`**. Tight: `V = {x_0+x_1 = x_2+x_3 = …}`
(N even; on V the maximum and the minimum always lie in one pair, so max + min = x_0 + x_1),
and for N odd add `x_{N-1} = (x_0+x_1)/2`.

Proof (induction on `n = |s|`; write `K_s(V) = V ∩ {x|_s = 0}`).
(A) If `i ≠ j ∈ s` with `x_i = x_j` on all of V: max/min over `s` and over `s \ {j}` agree on V,
`K_{s\{j}}(V) = K_s(V)`, and `⌊(n-1)/2⌋ ≤ ⌊n/2⌋`; apply the induction hypothesis.
(B) `n ≤ 2`: `dim V ≤ dim K_s(V) + n ≤ dim K_s(V) + ⌊n/2⌋ + 1`.
(C) `n ≥ 3`, coordinates of `s` pairwise distinct on V. A generic `v ∈ V` (perturb `v + t u`, finitely
many bad `t`) has pairwise distinct coordinates on `s`; let `a`, `b` be its unique maximal / minimal
coordinate on `s` (`a ≠ b`). For `x ∈ V` and large `t`, `x + tv` has unique max `a` and unique min `b`
on `s`, so `L(x) + tL(v) = x_a + x_b + t(v_a + v_b)` and `L(v) = v_a + v_b`; hence `L(x) = x_a + x_b`
on V. Let `V' = V ∩ {x_a = x_b}` (`dim V ≤ dim V' + 1`) and `s' = s \ {a,b}` (nonempty). For
`x ∈ V'`, `max_s x + min_s x = 2x_a`; if `x_a` is the max or the min on `s` then `x` is constant on
`s`, otherwise both extremes are attained in `s'`; either way `max_{s'} x + min_{s'} x = 2x_a`, a
linear function. Induction: `dim V' ≤ dim K_{s'}(V') + ⌊(n-2)/2⌋ + 1`. Finally
`K_{s'}(V') ⊆ K_s(V)`: if `x ∈ V`, `x_a = x_b = t`, `x = 0` on `s'`, then
`max_s x + min_s x = max(t,0) + min(t,0) = t` and `= L(x) = 2t`, so `t = 0`. Hence
`dim V ≤ dim K_s(V) + ⌊(n-2)/2⌋ + 2 = dim K_s(V) + ⌊n/2⌋ + 1`. ∎

## Theorem H (second width, every N): `h2 ≥ ⌈N/2⌉`

Every two-hidden-layer network computing `max_N` exactly on `R^N` has `2 h2 ≥ N`.

Proof. Zero biases WLOG. Use `(+∞)`: `max = Σ_k d_k π(T_k, G_k)`. Each `G_k` is a one-hidden-layer
function, so `G_k(x) - G_k(-x) = c_k·x` is linear (`σ(u) - σ(-u) = u`). Let `Z = {k : T_k = 0}` and
`V = {x : c_k·x = 0 for all k ∈ Z}`, so `dim V ≥ N - |Z|`. For `x ∈ V`:
`max(x) - max(-x) = Σ_k d_k [π(T_k, G_k(x)) - π(T_k, G_k(-x))]`; the terms with `T_k < 0` vanish, the
terms with `T_k > 0` equal `d_k c_k·x`, and the terms with `T_k = 0` vanish because
`G_k(x) = G_k(-x)` on V. So `max x + min x = max(x) - max(-x)` is linear on V, and by Lemma 3
`N - |Z| ≤ dim V ≤ ⌊N/2⌋ + 1`, i.e. `|Z| ≥ ⌈N/2⌉ - 1`. The slope identity `Σ_{T_k>0} d_k T_k = 1`
gives a neuron with `T_k > 0`, which is not in `Z`. Hence `h2 ≥ |Z| + 1 ≥ ⌈N/2⌉`. ∎

Remarks. (a) The proof shows more: in any exact representation
`max_N = (one-hidden-layer function) + Σ_{k∈Z} d_k σ(G_k)` with one-hidden-layer `G_k` (skip
connections of any kind allowed), `|Z| ≥ ⌈N/2⌉ - 1`. For N = 3, 4 this is 1, matching
`max_4 = m23 + σ(m01 - m23)`; the N = 4 network attains equality in Lemma 3
(`V = {x0 + x1 = x2 + x3}`). (b) Combined with Theorem 1: `h2 ≥ max(3, ⌈N/2⌉)`, which improves
Theorem 1 from N = 7 on. (c) The argument is the "odd part" of Lemma 0′ applied on the subspace
where all free neurons are even.
