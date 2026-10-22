# Lower bounds on s_N (current note)

## MAIN ROUTE (current): s_N ≥ C(N,k)/6^k for 3 ≤ k ≤ N, hence s_N ≥ (7/6)^N/(N+1)

Status: complete human proof (below); every finite ingredient checked
(`spine_F.py`, `check_spine_bound.py`: all 59 104 hinge components of all
units for N ≤ 8 satisfy G_C(1/6) ≤ F(L_C) ≤ 1). Lean: not started.

Proof. Fix `k ≥ 3`, `x := 1/6`.
1. *Functional* (E1): for a `k`-locality `L = (T, ρ)` let `Λ_L` be the k-th mixed
   finite difference in the `T` coordinates at `p_L` (box side `δ` small).
   `Λ_L` kills every function that near `p_L` is independent of some `y_t`,
   `t ∈ T`: affine functions, auxiliary functions, hinges inside `T`.
   `Λ_L max_N = ±δ`.
2. *Units* (E2): `Λ_L U ≠ 0` ⇒ (a) every `o ∉ T` has exactly `κ_o` hinge
   neighbours above it, and (s) every `t ∈ T` with no hinge neighbour in `T`
   has `κ_t ≠ 0`. [Germ `σ(⟨v_T, z⟩ + Σ_{M(T)} σ(z_i − z_j))` with
   `v_t = κ_t − |N⁺(t) ∩ T|`; base-`B` digits for (a).]
3. *Structure* (caterpillar keys): the hinge forest `F` has components of three
   kinds: isolated vertices; and components `C` consisting of a path of spine
   vertices `s_1 … s_L` (`L ≥ 1`, consecutive spine vertices joined by hinge
   spine edges) with pendant non-spine vertices ("leaves", hinge edge to their
   spine vertex, no other hinge, `κ = 0`).
4. *Admissible sets*: under (a) and (s), for each component `C`, `T ∩ C` is
   `A ∪ leaves(A)` for some `A ⊆ spine(C)` [a leaf outside `T` has no
   neighbour above, so its spine vertex is outside; a leaf in `T` without its
   spine vertex is inactive]. Isolated `o`: `o ∈ T` iff `κ_o ≠ 0`.
5. *Order count*: all orders of `O = V \ T` satisfying (a) induce the same
   orientation of `F[O]` (a forest orientation is determined by in-degrees),
   so they agree on every hinge edge inside `O`. Choose in every maximal run
   of outside spine vertices of length `n` a set of `⌊n/2⌋` disjoint
   consecutive pairs (spine edges): `m(T) = Σ ⌊n/2⌋`. Orders with `m` disjoint
   pairs in prescribed relative order number exactly `(N−k)!/2^m`. Hence
   `#{orders passing} ≤ (N−k)!/2^{m(T)}`.
6. *Generating function*: `W_k ≤ (N−k)! Σ_{T admissible, |T|=k} 2^{−m(T)}
   ≤ (N−k)! x^{−k} Π_C F_C(x)` with
   `F_C(x) = Σ_{A ⊆ spine(C)} x^{|A|} Π_{runs} 2^{−⌊n/2⌋}` (leaves only lower
   the weight, `x^{|leaves(A)|} ≤ 1`) and `F_{iso} ≤ max(1, x) = 1`.
   For `L ≥ 2`: `F_C(1/6) = F(L) ≤ 0.9213 < 1` (max at `L = 3`; for all `L` by
   a finite check plus the potential `u = (1, 3/5, 4/5)` on the states
   {after A, odd run, even run}). For `L = 1` (spine vertex with `λ ≥ 1`
   leaves): orders need the spine vertex below a leaf, `≤ 1/2`, so
   `F_C ≤ 1/2 + x^{1+λ} < 1`.
7. *Count*: every k-locality is passed by some unit of any expansion, so
   `C(N,k)(N−k)! ≤ |K| · 6^k (N−k)!`, i.e. **`|K| ≥ C(N,k)/6^k`**.
   With `k = ⌈N/7⌉`: `|K| ≥ (7/6)^N/(N+1)` (largest term of
   `Σ_k C(N,k) 6^{−k} = (7/6)^N`, for `N` large enough that this `k ≥ 3`).

For small N the quadratic/cubic bounds are stronger; the theorem should state
`|K| ≥ C(N,k)/6^k` for every `3 ≤ k ≤ N`.

**Main live claim E (exponential, 2026-10-22): `s_N ≥ max_{3≤k≤N} C(N,k)/3^k
≥ (4/3)^N/(N+1)`.** Status: reduction proved on paper (below); one
combinatorial inequality (E3) verified exactly for every hinge component of
every unit with N ≤ 8, open in general; Lean not started.

E1. *k-localities.* `L = (T, ρ)`, `|T| = k ≥ 3`, `T` ties at 0, the other
coordinates at `−B^{ρ(o)}`. Functional: the k-th mixed finite difference in
the `T` coordinates (box of side `δ` at `p_L`). It vanishes on every function
that, near `p_L`, does not depend on some coordinate of `T`: affine functions,
all auxiliary functions (≤ 2 coordinates, k ≥ 3), and hinges inside `T`. On
`max_N` it equals `±δ` (`max_N = max_k(y_T)` near `p_L`).
E2. *Units.* As in Q step 3, `Λ U_k ≠ 0` implies (a) [every outside `o` has
exactly `κ_o` hinge-neighbours above it] and (s) [every `t ∈ T` has a
hinge-neighbour in `T` or `κ_t − |N⁺(t) ∩ T| ≠ 0`; if `t` has no
hinge-neighbour in `T` this is `κ_t ≠ 0`]. Hence `s_N ≥ (#k-localities)/
max_u W_k(u)`, `W_k(u) = #{passing L}`, and `#k-localities = C(N,k)(N−k)!`.
E3. *Factorization.* Conditions (a), (s) and the order probability factor over
the components `C` of the hinge forest:
`W_k(u)/(N−k)! = [x^k] Π_C G_C(x)`,
`G_C(x) = Σ_{S⊆C, (s)} q_C(S) x^{|S|}`, `q_C(S)` = probability that a random
order of `C \ S` satisfies (a). For `|C| ≥ 2`, `q_C(∅) ≤ 1/2` (forced
orientation has an edge); isolated vertices give `G ≤ max(1, x)`.
**Inequality E3:** `G_C(1/3) ≤ 1` for every hinge component of every unit.
Then `W_k(u) ≤ 3^k (N−k)! · Π_C G_C(1/3) ≤ 3^k (N−k)!`, so
`s_N ≥ C(N,k)/3^k` for every `k ≥ 3`.
Evidence: `component_G.py` gives `max_C G_C(1/3) = 25/27` for N = 5..8 (a
3-vertex hinge path, all κ = 1). Direct per-unit maxima `W_k/(N−k)!`
(`mixed_k.py`): k = 3: 2; k = 4: 4; k = 5: 8; k = 6: 8 (N ≤ 8), all ≤ 3^k.
The abstract inequality (all trees, all κ) is false (star with κ ≡ 1, 4
vertices: 91/81, `abstract_G.py`); caterpillar property P (each vertex has
at most two neighbours with κ ≥ 1, since tree-leaves have κ ≤ 0) is needed.
Mechanism: a spine vertex with hinge leaves enters `S` together with all its
leaves or not at all (leaves have κ = 0); long arms force chains.

**Earlier claims (2026-10-22).**

- **Q (quadratic) — LEAN VERIFIED** (`MaxCaterpillar.caterpillar_count_lower`,
  `MaxCaterpillar/CountLower*`, axioms propext/Classical.choice/Quot.sound). If
  `max_N = Σ_{k∈K} d_k U_k + R` with `K` a set of normalized caterpillar face
  descriptions and `R` in the auxiliary span, then `6|K| ≥ N(N−1)`.
  Hence `s_N ≥ N(N−1)/6`.
- **C (cubic, conjecture).** The same with `12|K| ≥ N(N−1)(N−2)`, i.e.
  `s_N ≥ C(N,3)/2`. Verified for the per-unit locality count at N = 4..7
  (`count_ab.py`, `lemmas.py`), not proved.

Evidence levels follow `~/.claude/skills/formalization-research`: Q is a
mathematical argument with all finite facts checked for N ≤ 6
(`key_facts.py`); C is measured.

## Notation

Coordinates `y_0, …, y_{N−1}`, `σ = relu`. A normalized description `k = (h, M)`
has an integer head `h ∈ ℤ^N` (full coordinates, `Σ h = 0`) and a set `M` of
pairs `(i, j)`, `i < j`; `U_k(y) = σ(A_k(y))`,
`A_k(y) = ⟨h, y⟩ + Σ_{(i,j)∈M} σ(y_i − y_j)`. Auxiliary functions:
`σ(±y_i)`, `σ(y_i − y_j)`.
`N⁺(o) = {j > o : (o,j) ∈ M}`, `N⁻(o) = {i < o : (i,o) ∈ M}`,
`κ_o := h_o + |N⁺(o)|`.

Key facts (checked on all keys for N ≤ 6, provable from the word construction):
- **K1** `Σ_o h_o = 0`, hence `Σ_o κ_o = |M|`.
- **K2** there is an apex `a` with `h_a = −1` and no pair of `M` containing `a`
  (head `e_last − e_apex`; linear and reversed labels are tree edges between
  non-apex vertices). Then `κ_a = −1`.
- **K4** `|M| ≤ N − 2` (a word has `N − 2` labels).
- Integrality: `h ∈ ℤ^N`.

## Localities and the test functional

A locality is `L = (T, ρ)`: `T` a 3-set `{a < b < c}` (fixed labels), and `ρ` a
bijection from the `N − 3` other coordinates to `{1, …, N−3}`. There are
`C(N,3)(N−3)! = N!/6` localities. Point `p = p_L`: `p_t = 0` for `t ∈ T` and
`p_o = −B^{ρ(o)}` for `o ∉ T`, with `B` larger than twice every
`|h_o| + N` (any uniform bound over the finite key set).

Stencil: `ε = 1/(8C)`, `δ = ε/2`, `C ≥ 1 + max_k Σ_t |h_t| + 2N`;
`q± = p ± ε(e_a + e_b)`, `d = e_a − e_b`,
`J g(q) = g(q + δd) + g(q − δd) − 2 g(q)`,
`Λ_L g = J g(q₊) − J g(q₋)` (six point evaluations).

1. **Λ kills the auxiliary span.** On the stencil only `y_a, y_b` move, by at most
   `ε + δ < 1/2`; `y_c = 0` and the outside coordinates are fixed.
   `σ(±y_c)` and all functions of outside coordinates are constant; `σ(±y_a)`,
   `σ(±y_b)` are linear near `q₊` and near `q₋` (sign of `±ε ± δ` fixed);
   `σ(y_i − y_j)` with one end outside is linear (`|p_i − p_j| ≥ 1`);
   `σ(y_a − y_c)`, `σ(y_b − y_c)` are linear near `q±`; `σ(±(y_a − y_b))`
   has `J = 2δ` at both `q₊` and `q₋`, so `Λ = 0`. Linear functions have `J = 0`.
2. **Λ max_N = 2δ.** Near `q₊` the maximum is `max(y_a, y_b)` (the others are
   `≤ 0 < ε − δ`), `J = 2δ`; near `q₋` it is `y_c = 0`, `J = 0`.
3. **Units.** On the stencil, hinges with an end outside `T` are linear, so
   `A_k(p + z) = A_k(p) + ⟨v_T, z⟩ + Σ_{(i,j)∈M(T)} σ(z_i − z_j)`, where
   `M(T)` are pairs inside `T` and `v_t = h_t + |N⁺(t) \ T| = κ_t − |N⁺(t) ∩ T|`
   (a hinge `(t,o)`, `t ∈ T`, `o ∉ T`, is active iff `t < o`).
   `A_k(p)` is an integer. If `A_k(p) ≥ 1` then `U_k = A_k` on the stencil (the
   perturbation is `< 1`), a linear function plus hinges in `T`: `Λ = 0`. If
   `A_k(p) ≤ −1`, `U_k = 0` there. If `A_k(p) = 0` and `M(T) = ∅`, then
   `U_k = σ(⟨v_T, z⟩)`; when `v_T = c(e_i − e_j)` (including `c = 0`) this is
   `|c|` times a hinge in `T`: `Λ = 0`.
   **Hence `Λ_L U_k ≠ 0` implies `Pass(k, L)`:** `A_k(p_L) = 0` and
   (`M(T) ≠ ∅` or `v_T` is not a multiple of a root `e_i − e_j`, `i, j ∈ T`).
4. **Base-`B` digits.** `A_k(p_L) = −Σ_{o∉T} c_o B^{ρ(o)}` with
   `c_o = κ_o − #{M-neighbours of o above o}` ("above" = in `T` or smaller
   `ρ`), `|c_o| < B/2`. So `A_k(p_L) = 0` iff every `c_o = 0` (condition (a)).
5. **Triples.** Under (a): summing `c_o = 0` over `o ∉ T` counts every pair of
   `M` with an end outside `T` once (at its lower end), so with K1
   `Σ_{t∈T} κ_t = |M(T)|`, and every `o` with `κ_o < 0` lies in `T` (since
   `c_o = 0` forces `κ_o ≥ 0`). By K2, `a ∈ T`.
   - If two vertices have negative `κ`, `T` contains both: `≤ N − 2` triples.
   - Otherwise `T = {a, u, w}`, `κ_u, κ_w ≥ 0`, and `M(T) ⊆ {uw}` (no pair at
     `a`). If `uw ∉ M`, then `κ_u + κ_w = 1` and `v_T = (−1, κ_u, κ_w)` on
     `(a, u, w)` is `e_u − e_a` or `e_w − e_a`: (b') fails. So `uw ∈ M`: at most
     `|M| ≤ N − 2` triples (K4).
   Each triple has at most `(N−3)!` orders: **every key passes at most
   `(N−2)(N−3)!` localities.**
6. **Count.** Applying `Λ_L` to the expansion: `2δ = Σ_{k∈K} d_k Λ_L U_k`, so
   every locality is passed by some `k ∈ K`:
   `N!/6 ≤ |K| (N−2)(N−3)!`, i.e. `N(N−1) ≤ 6|K|`.

## Cubic claim C — human proof sketch (to be verified)

Goal: every key passes at most `2(N−3)!` localities, i.e.
`W(k) := Σ_T p_T ≤ 2`, `p_T := #{valid orders for T}/(N−3)!` (probability that
a uniformly random order of the outside vertices satisfies (a)).

Caterpillar data (tree on the `N−1` non-apex labels, root `π(1)`, spine
`π(1) … π(q+1) = last`, non-spine positions are leaves of the latest spine
vertex; each non-root vertex has a parent edge with state omit/lin/hinge).
`F` = hinge edges. On the tree,
`κ_o = #active children + [o = last] − [o = apex] − [parent edge linear]`
(active = lin or hinge); this equals `h_o + |N⁺(o)|` of the normalized key.
Hence: **tree-leaves have κ ∈ {0, −1}** (−1 iff linear parent edge), κ ≥ −1
everywhere, κ_apex = −1, Σκ = |F|.

1. Under (a), `Neg := {κ < 0} ⊆ T`, `Σ_{t∈T} κ_t = |F(T)|` (proved in Q, step 5).
   For a component `C` of `F` not meeting `T`, (a) forces
   `Σ_C κ = |C| − 1` (each edge counted once at its lower end); define the
   defect `D(C) = Σ_C κ − (|C| − 1)`; `Σ_C D(C) = 0` over all components
   including the apex singleton (`D = −1`). Components with `D ≠ 0` must meet `T`.
2. `p_T` factorizes over components of `F − T` (disjoint posets):
   `p_T = Π_C p_C(T)`; components not meeting `T` contribute a factor ≤ 1 that
   does not depend on `T` within a case; we bound it by 1.
3. **Case I, `Neg = {apex}`.** `T = {apex} ∪ e`, `e = uw ∈ F`, `κ_u + κ_w = 2`
   (from Q). Every non-apex component other than the one of `e` has `D = 0`,
   so `e` lies in the unique component `C*` with `D = 1`. Orientation of
   `C* − e`: each outside vertex `o` has exactly `κ_o` neighbours above it; on a
   forest an orientation is determined by its in-degree vector, so it is unique.
   `C*` is a subtree of a caterpillar: a spine subpath `s_1 … s_L` with
   tree-leaves attached by hinge edges (κ = 0 since the parent edge is hinge).
   A leaf outside `T` has no neighbour above, so it lies above its spine
   vertex; hence a spine vertex in `T` has no leaf outside `T`. For a spine
   vertex `s_j ∉ T` put `t_j := κ_{s_j} − #leaves(s_j)` = number of spine
   neighbours above `s_j` ∈ {0,1,2}: 0 = local top, 2 = local bottom, 1 =
   monotone. Tops and bottoms alternate along the path; `T` must be a top
   (its endpoints are above all neighbours). So `e` lies in a maximal stretch
   between consecutive bottoms (or path ends) that contains no prescribed top,
   and all valid `e` lie in one such stretch `s_1 … s_k` (all `t = 1`); two
   such stretches would need two tops. Valid `e`: a spine edge `s_j s_{j+1}`
   with both ends leafless, or a leaf edge `s_j ℓ` with `ℓ` the only leaf of
   `s_j`. Then the arms `s_{j−1} > … > s_1` and `s_{j+2} > … > s_k` (resp.
   `s_{j+1} > … > s_k`) are forced chains, so
   `p_e ≤ 1/((j−1)!(k−j−1)!)` (spine edge) or `≤ 1/((j−1)!(k−j)!)` (leaf edge).
   `stretch_sum.py`: the maximum over all leaf patterns of the sum is 2.
4. **Case II, `Neg = {apex, z}`.** `κ_z = −1` forces a linear parent edge and
   no active children, so `z` has no hinge edge; `T = {apex, z, x}`,
   `κ_x = 2`, (b') holds. `D(comp(x)) = 2`, all others 0. `x` is a source with
   no leaf outside `T`, so a leafless spine vertex in the unique top-free
   stretch: `p_x ≤ 1/((j−1)!(k−j)!)`, sum `2^{k−1}/(k−1)! ≤ 2`.
5. **Case III, `|Neg| = 3`.** One triple, `p ≤ 1`. `|Neg| ≥ 4`: none.

Hence `W(k) ≤ 2` and `s_N ≥ (N!/6)/(2(N−3)!) = N(N−1)(N−2)/12`.
Verified per unit for N = 4..8 by exact enumeration (`count_ab.py`, N = 8 in `count_ab_8.log`,
`lemmas.py`); exhaustive abstract check under property
"each vertex has ≤ 2 neighbours with κ ≥ 1" for N = 6 (`exhaustive_P.py`).

Old note: weighting by orders: `Σ_T e_T/(N−3)! ≤ 2` per unit (`e_T` = valid orders).
Extremal units: a hinge path whose inner `κ` are 1; edges of the path are the
valid triples, weights `1/(a! b!)` with `a + b = j − 2`.
Formula on the caterpillar tree: `κ_o = #active children + [o = last]
− [o = apex] − [parent edge linear]`; leaves have `κ ∈ {0, −1}`.
Abstract version (arbitrary forest, arbitrary κ) is **false** (star with all
`κ = 1` gives 4, `abstract_test.py`), so the proof must use caterpillar
structure.

## Failed / weaker routes

- **Covering by 3-ties without the class test**: `(2N−5)(N−3)!` per unit,
  quadratic `≈ N²/12` (`count_a.py`). Superseded by Q.
- **k-ties for k ≥ 4** (`localk.py`): weaker (N=6: 3 for k=4, 2 for k=5).
- **Exact local linear algebra at 3-ties** (`localeq.py`): same values as
  covering (2, 5 for N = 4, 5); the triple-tie method cannot beat covering.
- **Quotient dimension** `q_N ≥ (N−2)!`: bounds the vocabulary, not `s_N`;
  removed from paper and Lean (user decision).
- Reopening condition for a superpolynomial bound: a global argument; local
  tie-germs give at most cubic.
