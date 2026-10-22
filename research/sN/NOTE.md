# Lower bounds on s_N (current note)

**Live claims (2026-10-22).**

- **Q (quadratic, human proof complete, Lean in progress).** If
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
