# Growth of k(N): proofs

Model. `Φ` is the paper's first hidden layer (`σ(x_0), σ(−x_0), σ(x_i − x_0), σ(x_i − x_j)`).
`k(N)` is the least `K` with `max_N = R + Σ_{k<K} d_k σ(G_k)` on `R^N`, `R, G_k ∈ span Φ`
(second width with this first layer is `k(N) + 2`, research/sN/best5/PROOFS.md, Theorem A).
On the open positive orthant `σ(x_0) = x_0`, `σ(−x_0) = 0`, so there every `G ∈ span Φ` reads
`g = Σ_v γ_v x_v + Σ_{u<v} c_uv max(x_u, x_v)` with real `γ, c`.

## Theorem L (growing lower bound). `k(N) ≥ C(N,3)/B(N) ≥ √N / 2` for every `N ≥ 3`

where `B(3) = 1`, `B(4) = 4`, `B(m) = max( (m−1)/(m−3)·B(m−1), m(m−2)/((m−3)(m−4))·B(m−2) )`.
Status: proof on paper (below); every finite ingredient checked exactly (`locf.py`,
`check_lemmas.py`). Not in Lean.

### Step 1 (locality lemma; research/sN/dfs/h4-any-network/r3/NOTE.md, re-derived)

A 3-locality is `(T, ρ)`, `T` a 3-set, `ρ` an order of `O = [N] ∖ T`; its cell is
`C_{T,ρ} = {x_t = s (t ∈ T), s > x_{ρ1} > … > x_{ρ(N−3)} > 0}`. There are `C(N,3)(N−3)!` cells.
Take `p ∈ C_{T,ρ}` off the zero sets of all neurons not vanishing identically on the cell, and let
`Λ h = Σ_{U⊆T} (−1)^{3−|U|} h(p + δ 1_U)` (small `δ`). `Λ` kills every function that near `p`
does not depend on some coordinate of `T`: `R`, and every neuron with `G_k(p) ≠ 0` (near `p`
these are linear plus `σ(x_i − x_j)` with `i, j ∈ T`, or zero). `Λ max_N = δ`. Hence some neuron
with `G_k ≡ 0` on the cell has `Λ σ(G_k) ≠ 0`; call such a cell *seen* by that neuron. So
`k(N) ≥ C(N,3)(N−3)! / max_neuron #seen`.

A cell is seen by `g` iff (coefficients of `g` on the cell, and the 8-corner sum of the germ):
- (a) every `o ∈ O` has down-weight `c(o, {u ∈ O below o}) = −γ_o`;
- (c) `Σ_{t∈T} γ_t + c(T, O) + c(E(T)) = 0`;
- (Λ) `Σ_{t∈T} [σ(Γ_t) − σ(d_t − Γ_t)] ≠ 0`, `Γ_t = γ_t + deg(t)`, `d_t = c(t, T∖t)`.
(Germ `G(z) = Σ_T v_t z_t + Σ_{e⊆T} c_e max(z_e)`, `v_t = γ_t + c(t,O)`; (c) makes it translation
invariant, so `G(e_t) = Γ_t`, `G(1_{T∖t}) = d_t − Γ_t`.)

Remark. If no pair inside `T` has `c ≠ 0`, then `d_t = 0` and `Λ = Σ_T Γ_t = c(E(T)) = 0` by (c).

### Step 2 (peeling)

For an *instance* `(X, c, γ)` (vertex set `X`, `|X| = m ≥ 3`) let `f(X) = #seen/(m−3)!`.
The bottom vertex `b` of `O` has down-weight 0, so it needs `γ_b = 0`; deleting it leaves every
other condition unchanged after replacing `γ_o` by `γ_o + c_ob`. Hence, with
`R(X) = {b : γ_b = 0}` (the *removable* vertices),

`f(X) = (1/(m−3)) Σ_{b ∈ R(X)} f(X − b)`, `X − b` carrying `γ' = γ + c(·, b)`; `f(T) ∈ {0, 1}` for `|T| = 3`.

(`Γ_t` is unchanged by the update, so (Λ) and (c) are evaluated correctly in the sub-instance.)
Checked against brute-force enumeration of all `(T, ρ)` on 700 random instances (`locf.py`,
`check_lemmas.py`).

### Step 3 (two kinds of states)

*P-state*: some `γ_o ≠ 0`. Then `|R(X)| ≤ m − 1` and `f(X) ≤ (m−1)/(m−3) · max_b f(X − b)`.

*Q-state*: `γ ≡ 0` on `X`. Call `o` isolated if `c(o, u) = 0` for all `u ∈ X`.
- Isolated vertices are inert: an isolated `o` satisfies (a) at every position and does not change
  any other condition; and a `T` containing an isolated `t` has `d_t = Γ_t = 0`, so with
  (c) `Γ_u + Γ_v = c_uv` the remaining terms of (Λ) cancel: `Λ = 0`. Therefore
  `f(X) = f(X ∖ I)` (`I` the isolated set; interleaving `I` into an order multiplies counts by
  `(m−3)!/(m'−3)!`). Checked exactly (`check_lemmas.py`).
- Without isolated vertices, every child `X − b` has `γ'_o = c_ob ≠ 0` for each neighbour `o` of
  `b`, so it is a P-state with at most `m − 1 − deg(b) ≤ m − 2` removable vertices. Two peeling
  steps give `f(X) ≤ m(m−2)/((m−3)(m−4)) · max f(grandchild)` (`m ≥ 5`).

### Step 4 (induction)

By strong induction every instance on `m` vertices has `f ≤ B(m)` (`B` nondecreasing; base
`m = 3`: `f ≤ 1`; `m = 4`: `f ≤ |R| ≤ 4`). Moreover `B(m) ≤ (m−1)(m−2)√m/3`: true for `m = 3, 4`,
and the two recursion branches give `(m−1)(m−2)√(m−1)/3` and `m(m−2)√(m−2)/3`, both at most
`(m−1)(m−2)√m/3` (the second because `m(m−2) ≤ (m−1)²`). Checked exactly up to `m = 2000`.

Hence one neuron sees at most `B(N)(N−3)!` cells and
`k(N) ≥ C(N,3)/B(N) ≥ N(N−1)(N−2)/6 · 3/((N−1)(N−2)√N) = √N/2`. ∎

Numbers: the exact bound `⌈C(N,3)/B(N)⌉` gives 2 for `N ≤ 19` (no improvement on the known
`k(N) ≥ 2` there), 3 at `N = 20`, 6 at `N = 100`, 17 at `N = 1000`.

### Where the √ is lost, and the conjectured linear bound

Only Q-states cost more than the factor `(m−1)/(m−3)` that keeps `(m−1)(m−2)` invariant. If
`H[X]` (pairs with `c ≠ 0`) has at least `m − 1` edges, the two-step factor is
`(m(m−1) − 2e)/((m−3)(m−4)) ≤ (m−1)(m−2)/((m−3)(m−4))` and nothing is lost. So `F(N) = O(N²)`
(hence `k(N) = Ω(N)`, which is the ceiling of the locality method: the signed star sees
`⌊(N−1)/2⌋⌈(N−1)/2⌉ (N−3)!` cells) follows from: *every Q-state without isolated vertices and with
at most `m − 2` edges (necessarily disconnected) has `f ≤ a(m−1)(m−2)`*. Useful facts for it: in a
Q-state the order conditions factor over components; a component `K` disjoint from `T` is valid
with probability at most 1/2 if some vertex has nonzero weighted degree in `K` (reversing the order
maps valid orders to invalid ones), and the remaining ("balanced") components have `e(K) ≥ |K|`.
Measured maxima of `f` (hill climbing, exact values): 6, 8, 9.75, 12 for `N = 5..8`, against the
star value 4, 6, 9, 12 (`climb_n*.log`). Open.

## U1 (reformulation used for the upper-bound search)

Every `G ∈ V = span{x_i, max(x_i,x_j)}` is the Lovász extension of its set function
`g(S) = G(1_S)`, a multilinear polynomial of degree ≤ 2 with `g(∅) = 0`. On a braid cell
`x_{π1} > … > x_{πN}`, `G = Σ_j (x_{πj} − x_{πj+1}) g(S_j) + x_{πN} g([N])`, `S_j = {π1..πj}`.
For translation-invariant neurons (`g([N]) = 0`), `G` changes sign inside the cell iff the chain
vector `(g(S_1), …, g(S_{N−1}))` has both strict signs; two such neurons share their zero
hyperplane in the cell iff their chain vectors are proportional; `σ(λL) ≡ |λ|σ(L)` modulo linear
functions. Therefore:

**Lemma U1.** `max_N = R + Σ d_k σ(G_k)` (translation-invariant `G_k`, `R ∈ V`) holds on `R^N` iff
(i) for every chain and every proportionality class of neurons cutting it, `Σ d_k |λ_k| = 0`, and
(ii) `Σ d_k σ(g_k(S)) + r(S) = [S ≠ ∅]` for all `S ⊆ [N]`.
[(i) ⟺ the sum is linear on every cell, i.e. a Lovász extension; then (ii) compares values on the
rays `1_S`, which generate the cells.] For a fixed dictionary both are linear in `(d, r)`.

Corollary. A neuron whose chain vectors never change sign ("chain-separated" `g`) gives
`σ(G) = Lovász(σ∘g)`. Sampling shows these alone cannot represent `max_5`: their positive parts
together with `V` span a hyperplane of the 16-dimensional quotient, annihilated by the top Möbius
coefficient `Σ_S (−1)^{|S|} f(S)` (`bs_explore.py --ann`, measured). In `max_5 = …` (Max5General4)
the neuron `σ(m_de − m_ac)` is chain-separated and the other three cancel pairwise on 32 cells
(`cut_pattern.py`).
