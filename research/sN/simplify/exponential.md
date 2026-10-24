# The exponential lower bound, simplified and unified

Status: human proof below (self-checked, see the end). Lean: complete, sorry-free,
axioms `propext, Quot.sound, Classical.choice` only, in `MaxCaterpillar/Simplify/`
(StarCover 174, BlockSum 202, Reduced 517, TreeUnits 396, Brunck 153 lines):
`card_passes_le_red` (per-unit count), `tree_reduced_choose_le` / `_exponential` /
`_exponential_two` (general Δ), `brunck_expansion_choose_le` / `_exponential`
(caterpillar functions + rooted-star faces, all counted, base 6, no quadratic bound).

## Setting

Coordinates `x_0, …, x_{N-1}`, `σ = relu`, `N ≥ 3`. A **unit** is
`U = σ(A)`, `A(x) = Σ_o h_o x_o + Σ_{(i,j)∈M} σ(x_i − x_j)` with an integer head
`h ∈ ℤ^N` and a set `M` of ordered pairs. Its **hinge graph** `F` has an edge
`{i,j}` for every `(i,j) ∈ M`. For a label `o` let
`κ_o := h_o + #{j : (o,j) ∈ M}`; this is the slope of `A` in `x_o` where `x_o` lies
above all hinge neighbours of `o` (so it does not depend on how the functions
`σ(x_i − x_j)` are oriented: `σ(t) = t + σ(−t)`).

A **pendant** is a vertex of `F`-degree 1 with `κ = 0`. The **reduced forest**
`F°` is `F` minus its pendants (when `F` is a forest).

The auxiliary span is `A_N = span{σ(±x_i), σ(x_i − x_j)}`.

## Theorem (one statement)

Let `Δ ≥ 2` and `b := 2Δ + 2`. Let `max_N = Σ_{k∈K} d_k U_k + R` on `ℝ^N` with
`R ∈ A_N` and units `U_k` whose hinge graphs are forests with reduced forests of
maximum degree `≤ Δ`. Then

    C(N, m) ≤ b^m |K|      for every 3 ≤ m ≤ N,

hence `|K| ≥ (1 + 1/b)^N / (N+1)` (for every `N ≥ 3` when `b = 6`; for
`N ≥ 3b + 2` in general).

**Δ = 2, b = 6** covers in one statement, *all units counted*:
* the caterpillar face functions (the paper's `U_k`): `F` = spine links plus pendant
  edges to tree leaves, which have `κ = 0`; `F°` ⊆ spine path, degree ≤ 2;
* the pyramids `pyr(B_{v,π,M})` of Brunck–Hertrich–Rueß–Stade–Yehudayoff: `M ≠ ∅`
  are caterpillar polytopes; `M = ∅` gives the rooted star
  `σ(x_c − x_a + Σ_l σ(x_c − x_l))` and its faces
  `σ(x_c − x_a + Σ_{l∈Lin}(x_c − x_l) + Σ_{l∈Hng} σ(x_c − x_l))` (each leaf omitted,
  linear, or hinge): `F` is a star at `c` whose leaves have `κ = 0`, so `F°` has no
  edge. (No case distinction "omitted leaf ⇒ caterpillar face" is needed.)
  Faces of the zonotope part are sums of ≤2-coordinate functions, i.e. in `A_N`.

So `|K| ≥ (7/6)^N/(N+1)` for caterpillars + rooted stars + faces together, the same
constant as the old caterpillar-only theorem.

**General Δ**: units over arbitrary trees of hinge degree `≤ Δ` (and, more generally,
trees whose high-degree vertices have only pendant hinge neighbours beyond `Δ`):
`C(N,m) ≤ (2Δ+2)^m |K|` (old: `2(12Δ−6)^m |K|`, `Trees/BoundedDegreeMain`).

## Proof

Fix `3 ≤ m ≤ N`. Encode a locality by a permutation `ρ` (position of each label;
smaller = higher); `T := {o : ρ(o) < m}` is the tie set. Base point
`p_o = 0` on `T`, `p_o = −B^{ρ(o)}` off `T`; `Δ_ρ g := Σ_{S⊆T} (−1)^{|T∖S|} g(p + δ1_S)`.
Choose `δ` and the integer `B` as in the paper (`δ · (Σ|h| + 2|M|) < 1` and
`Σ|h| + |M| < B` for every unit of `K`).

**S1 (functional).** If `g` does not depend on some `x_t`, `t ∈ T`, on the cube, then
`Δ_ρ g = 0`. Every function of at most two coordinates misses a tied coordinate
(`m ≥ 3`), so `Δ_ρ A_N = 0`; and `Δ_ρ max_N = ±δ` (off-tie coordinates are `≤ −1`).
Hence some `k ∈ K` has `Δ_ρ U_k ≠ 0`.

**S2 (seen ⇒ pass).** `A(p)` is an integer and `A` moves by `< 1` on the cube. If
`A(p) ≠ 0`, then `U = 0` or `U = A` (a sum of ≤2-coordinate functions) on the cube:
`Δ_ρ U = 0`. If `t ∈ T` has no hinge neighbour in `T` and `κ_t = 0`, raising `x_t` by
`δ` does not change `A` (its hinges go to coordinates `≤ −1`), so `Δ_ρ U = 0`.
**S3 (digits).** `A(p) = −Σ_{o∉T} (κ_o − u_ρ(o)) B^{ρ(o)}`, `u_ρ(o)` = number of hinge
neighbours of `o` at a smaller position; the digits are smaller than `B` in absolute
value, so `A(p) = 0` forces every digit to vanish.
So `Δ_ρ U ≠ 0` implies that `U` **passes** `ρ`:

    (a) u_ρ(o) = κ_o for every o ∉ T;  (s) κ_t ≠ 0 for every t ∈ T without hinge neighbour in T.

From now on fix one unit `U` (forest `F`, reduced forest `F°` of max degree `≤ Δ`) and
count the `ρ` it passes. Let `Φ` be the set of vertices of `F°` that are not isolated
in `F`.

**S4 (forced vertices).** Let `U` pass `ρ` with tie set `T`.
* An isolated vertex `o` of `F` lies in `T` iff `κ_o ≠ 0` (by (s), resp. (a): `0 = κ_o`).
* A pendant `p` with neighbour `v` lies in `T` iff `v` does: if `p ∈ T`, `v ∉ T`,
  (s) fails at `p`; if `p ∉ T`, `v ∈ T`, then `u_ρ(p) = 1 ≠ 0 = κ_p`.
  If `v` is a pendant too (component `{p, v}`), both lie in `T`: otherwise both are
  outside and the lower one has `u = 1 ≠ 0`.
Hence two passed tie sets that agree on `Φ` are equal: `T ↦ T ∩ Φ` is injective, and
`|T ∩ Φ| ≤ |T| = m`.

**S5 (orders).** Fix `T`. For `o ∉ T` all its hinge neighbours in `T` lie above it, so
(a) prescribes how many of its hinge neighbours outside `T` lie above `o`, i.e. the
out-degrees of the orientation "towards the higher end" of the forest `F − T`.
A forest orientation is determined by its out-degrees (peel a leaf: its edge is
oriented by its out-degree; remove it and repeat). So all passed `ρ` with tie set `T`
orient each edge of `F − T` in the same way, and if `P` is a matching of edges of
`F − T`, the passed `ρ` with tie set `T` number at most `m! (N−m)! / 2^{|P|}`
(swapping the two ends of one edge of `P` is a bijection between permutations with
tie set `T`).

**S6 (blocks).** Cover the vertices of `Φ` by disjoint *blocks*:
* every vertex `v ∈ Φ` isolated in `F°` is a block `{v}`; all its `F`-neighbours are
  pendants; fix one, `p_v`;
* the non-isolated part of `F°` is covered by vertex-disjoint stars of `F°` (a
  minimal edge cover of a forest without isolated vertices contains no path with three
  edges, so it is a star forest); a star has a centre and `1 ≤ s ≤ Δ` leaves.
Given `A = T ∩ Φ`, each block chooses at most one edge of `F − T`, depending only on
`A ∩ block`: the block `{v}` chooses `v p_v` if `v ∉ A` (then `p_v ∉ T` by S4); a star
chooses a centre–leaf edge if its centre and some leaf are outside `A`. Chosen edges
lie in disjoint blocks (plus private pendants), so they form a matching `P(A)`.

With `y := 1/b`, by S4 and S5 the number of passed permutations is at most

    m!(N−m)! Σ_T 2^{−|P(T∩Φ)|} ≤ m!(N−m)! y^{−m} Σ_{A⊆Φ} y^{|A|} 2^{−|P(A)|}
                               = m!(N−m)! y^{−m} Π_blocks W_block(y),

(`y^{−m} y^{|A|} ≥ 1`; the sum over `A ⊆ Φ` contains every `T ∩ Φ` at most once and
factorises because `|A|` and `|P(A)|` are sums over blocks), where

    W_{v}(y) = 1/2 + y,
    W_star(s)(y) = y(1+y)^s + ((1+y)^s − y^s)/2 + y^s = (1/2 + y)(1+y)^s + y^s/2.

(Star: centre in `A`: `y(1+y)^s`; centre out and some leaf out: factor `1/2`; centre
out, all leaves in: `y^s`.) **All block weights are `≤ 1`** at `y = 1/(2Δ+2)`:
`1/2 + y ≤ 2/3`; for `s = 1`, `W = 1/2 + 2y + y² ≤ 31/36`; for `2 ≤ s ≤ Δ`,
`(1+y)^s ≤ e^{Δy} = e^{1/2 − y}`, and `t ↦ e^{1/2−t}(1/2+t)` increases on `[0,1/2]`, so
`(1/2+y)(1+y)^s ≤ e^{1/3}·2/3 < 0.931` and `y^s/2 ≤ 1/72`: `W < 0.945`.
Hence **each unit passes at most `m!(N−m)! b^m` permutations.**

**S7 (count).** By S1–S3 the `N!` permutations are covered by the passed sets of the
units of `K`: `N! ≤ |K| m!(N−m)! b^m`, i.e. `C(N,m) ≤ b^m |K|`.

**Corollary.** `t_m := C(N,m) b^{−m}` sums to `(1+1/b)^N`. If `N ≥ 3b+2` then
`t_0 ≤ t_1 ≤ t_2 ≤ t_3` (`t_{m+1}/t_m = (N−m)/(b(m+1))`), so the largest term has
`m ≥ 3` and `|K| ≥ max_m t_m ≥ (1+1/b)^N/(N+1)`. For `b = 6` and `N ≤ 19`,
`(7/6)^N ≤ N+1` and `|K| ≥ 1` (from `m = 3`), so the bound holds for all `N ≥ 3`
(Lean: `seven_pow_le_of_choose_le`, no quadratic bound needed).

## Remarks (constants)

* **Base 5 for Δ = 2** (not in Lean): `F°` is a linear forest, its star blocks are
  paths with 2 or 3 vertices. For a 3-vertex block with all vertices outside `T` use the
  exact order count (a fixed orientation of a 3-vertex path is met by at most 2 of the
  6 orders) instead of one matched edge: `W = 1/3 + 2y + 3y² + y³`. At `y = 1/5`:
  `W_pair = 47/50`, `W_triple = 323/375`, `W_{v} = 7/10`. Hence
  `C(N,m) ≤ 5^m |K|` and `|K| ≥ (6/5)^N/(N+1)` (for `N ≥ 17`). The pair block limits
  this method to `y ≤ (√6 − 2)/2`, i.e. base `≈ 4.45`.
* With the exact star order count (`≤ 1/(s+1)` when the whole star is outside) the
  general base improves to `O(Δ/log Δ)`; not worked out.
* Old proof (paper `app:lower`, steps "greedy matching" + "potential `7/9, 7/6, 1`"):
  a transfer induction along the spine with five cases; here the weight factorises
  over blocks and each block is one line. Same constant 6, wider class.

## Comparison with the out-leaf theorem (`coverage.md`, `Simplify/Coverage*.lean`)

* Classes are incomparable. Out-leaf class (≤ s hinge leaves with κ = 1 at every vertex)
  allows unbounded degree through κ ≤ 0 vertices and through leaves with κ ∉ {0,1};
  the reduced-degree class allows unbounded degree only through pendants (κ = 0 leaves),
  but does not care how many κ ≥ 1 neighbours a vertex has as long as Δ bounds them.
* Common part (bounded hinge degree Δ, rooted stars, caterpillars): base here 2Δ+2
  (rooted stars and caterpillars: 6) vs 16(s+1)/3 (rooted stars: 32/3; Δ: 16(Δ+1)/3).
* Caterpillars: here one theorem through tree faces (`Brunck.lean`); the out-leaf mixed
  theorem still needs the old caterpillar per-unit count (`CountExp.card_passSet_le`)
  and the quadratic bound.
* Subsuming the out-leaf class by this route would need Φ = {κ ≥ 1} (their L1) and a
  block system for untied H-vertices whose neighbours have κ ≤ 0; the star cover gives
  weight (1/2+y)(1+y)^deg, which is unbounded in the degree, so a child-directed block
  (their L2/L3) is needed there. Not done; the two arguments remain separate.

## What the per-unit lemma needs (for reuse, e.g. larger tree classes)

Per-unit lemma, abstract form. Let `U` have a forest hinge graph `F`. Suppose
`Φ ⊆ V` is such that every passed tie set `T` is determined by `T ∩ Φ`, and `Φ` is
partitioned into blocks `β`; for each block and each `S ⊆ β` let `e_β(S)` be either
nothing or an edge of `F` with both ends outside every passed `T` with `T ∩ β = S`,
the edges of different blocks being vertex-disjoint. Then

    #{ρ passed, |T_ρ| = m} ≤ m!(N−m)! y^{−m} Π_β Σ_{S⊆β} y^{|S|} 2^{−[e_β(S) exists]}   (0 < y ≤ 1).

(Exact order counts of a forced orientation of a whole block may replace `1/2`.)
A class of units has base `1/y` as soon as every block weight is `≤ 1`.

## Self-check (adversarial)

1. *S1 with `m = N`*: there are no off-tie coordinates; `Δ_ρ max_N = ±δ` still holds
   (`max = δ` at nonempty corners, `0` at the origin). ✓
2. *S2 at `t` with `κ_t = 0`, no hinge neighbour in `T`*: hinges `σ(x_t − x_o)` with
   `o ∉ T` have argument `≥ 1 − δ > 0` (slope 1 in `x_t`, counted in `κ_t`), hinges
   `σ(x_o − x_t)` stay 0; head coefficient `h_t`. Total slope `κ_t` ✓ (orientation of
   pairs arbitrary: `κ_t` counts pairs with `t` first ✓).
3. *S3 digits*: `σ(p_i − p_j) = p_i − p_j` iff `i` is higher. Collecting `p_o`:
   coefficient `h_o + #{(o,j)∈M, o higher than j} − #{(i,o)∈M... }`; rewriting each
   pair in the "κ" form gives `−(κ_o − u_ρ(o))` up to the sign convention (paper
   eq. preactivation-digits, Lean `descr_balanced_of_arg_eq_zero` for arbitrary
   descriptions with `i < j`; any description can be normalised to `i < j` without
   changing `A`, `F`, `κ`). ✓
4. *S4, pendant whose neighbour is isolated in `F°`*: handled by the block `{v}`. Pendant
   whose neighbour is also a pendant: forced into `T`; such components contribute no
   block and no choice. ✓ A degree-1 vertex with `κ < 0` is *not* a pendant; it stays
   in `F°` (always in `T`, which only removes terms). ✓
5. *S5 needs `F` (not only `F°`) to be a forest* — tree units and caterpillars ✓.
6. *S6 factorisation*: the sum is over all `A ⊆ Φ` (superset of the realised
   `T ∩ Φ`); terms nonnegative ✓. `P(A)` is a matching: star edges inside disjoint
   stars; `v p_v` uses a pendant private to `v` ✓. Edge outside `T`: centre and leaf
   `∉ A` and both in `Φ`, so `∉ T` ✓; `p_v ∉ T` by S4 ✓.
7. *Star cover*: a minimal edge cover `E'` of a forest without isolated vertices: if
   `E'` contained a path `a–b–c–d`, the middle edge `bc` could be dropped (b, c stay
   covered) — contradiction; no cycles in a forest; so every component of `E'` is a
   star `K_{1,s}`, `s ≥ 1`, and `s ≤ deg(centre) ≤ Δ` ✓ (for `K_{1,1}` either end is
   the centre).
8. *Weights*: numerically `W_star(s)(1/(2Δ+2)) ≤ 0.9214` for all `1 ≤ s ≤ Δ ≤ 200`
   (maximum at `Δ = s = 2`); `check_shape.py` (3) checks the block constants.
9. *Caterpillar shape*: tree leaves attached by a hinge have `κ = 0` (paper,
   step "hinge graph lies on a caterpillar"; Lean `exists_hingeCat`) ✓. Rooted-star
   hinge leaves: `σ(x_c − x_l)` gives `κ_l = 0` ✓ (`check_shape.py` (1): the exact
   mixed difference of every rooted-star face, N = 4, 5, is nonzero only where the
   unit passes).
10. *Brute force*: random units of caterpillar shape (N ≤ 7) pass at most
    `5.5 · m!(N−m)!` permutations (`check_shape.py` (2), (4)), far below `5^m`.
