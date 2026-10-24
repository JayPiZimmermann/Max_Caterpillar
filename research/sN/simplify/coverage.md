# Which trees does the exponential count cover?

Status: proof below (paper); Lean in `MaxCaterpillar/Simplify/Coverage.lean`,
`MaxCaterpillar/Simplify/CoverageMain.lean` (see the last section for the exact
names and the verification status). Numerical checks: `coverage_check.py`,
`coverage_climb.py`.

## Result

Setting (as in `trees/PROGRESS.md`): `max_N = Σ_{F∈K} d_F U_F + R`, where `R` is in
the span of `σ(±x_i)`, `σ(x_i − x_j)` and every `U_F` is the face function of a
pyramid over a tree, `U_F = σ(x_root − x_apex + Σ_edges ℓ_e)`, with each edge
term `ℓ_e` equal to `0`, `x_i − x_j` or `σ(x_i − x_j)`. The hinge forest `M_F` of
`F` consists of the edges with the term `σ(x_i − x_j)`. Normalise the unit as
`σ(⟨h, x⟩ + Σ_{(i,j)∈M, i<j} σ(x_i − x_j))` (this is `TreeFace.descr`), and put

    κ_o = h_o + #{j > o : (o, j) ∈ M}            (an integer).

**Out-leaf.** A vertex `u` of degree 1 in `M_F` with `κ_u = 1`.
For a unit whose edges are all hinges this means: `u` is a hinge leaf whose
function is `σ(x_u − x_p)` (with `p` its neighbour), and `u` is not the root or
the apex, or `u` is the root and its function is `σ(x_p − x_u)`. Linear edge
terms at `u` shift `κ_u` by `±1`.

**Theorem (coverage).** Let `s ≥ 0`. If in every unit of `K` every vertex is
adjacent to at most `s` out-leaves, then for every `N ≥ 3` and `3 ≤ k ≤ N`

    C(N, k) ≤ c_s^k |K|,       c_s = 16(s+1)/3,

and therefore `(c_s + 1)^N ≤ (N + 1) c_s^N |K|`, i.e.

    |K| ≥ (1 + 3/(16(s+1)))^N / (N + 1)        for every N ≥ 3.

The same holds when caterpillar face functions (the vocabulary of the main
theorem) are added to `K`, for `s ≥ 1`.

Classes contained in the hypothesis:

| class | `s` | base `1 + 1/c_s` |
|---|---|---|
| no out-leaves at all (e.g. every hinge leaf has `κ ≤ 0`, as in rooted stars and all their faces) | 0 | `1 + 3/16` |
| rooted stars of Brunck et al. (`starFace`, via `HubOK 1`) | 1 | `1 + 3/32` |
| caterpillar trees (tree-leaves have `κ ∈ {0, −1}`, so out-leaves are spine vertices; paper argument, not in Lean — in Lean caterpillars enter as `K₁` of `IsMixedExpansion`) | 2 | `1 + 1/16` |
| hinge degree `≤ Δ` (old base `1 + 1/(12Δ − 6)`) | Δ | `1 + 3/(16(Δ+1))` |
| hub class `HubOK Δ` (old: `2^{N/(144(2Δ−1)²+1)}`, `N ≥ 10803`) | Δ | `1 + 3/(16(Δ+1))` |
| every vertex has at most `s` neighbours with `κ ≥ 1` | ≤ s | `1 + 3/(16(s+1))` |
| arbitrary trees, `s = s(N) = o(N / log N)` | s(N) | superpolynomial |

So bounded degree, rooted stars, the hub class and every mixture of them with
caterpillars are now covered by one statement, with base `1 + 3/(16(s+1))`
instead of `2^{1/(144(2Δ−1)²+1)}`, and without a threshold on `N`.

**Not covered:** trees in which some vertex carries many out-leaves. Concrete
example, the *out-star*

    S⁺_{a,c}(x) = σ(x_c − x_a + Σ_{l ≠ a,c} σ(x_l − x_c))

(all `N − 2` leaves are out-leaves of `c`, `s = N − 2`). It passes every
`k`-locality whose tie set contains `a` and `c`, in every order of the other
coordinates (each untied leaf has exactly one neighbour above it, the tied `c`),
i.e. a fraction `k(k−1)/(N(N−1))` of all `k`-localities. Hence `N²` out-stars
(with suitable apexes and centres) pass every locality, and no counting of passed
localities can prove more than a quadratic bound for vocabularies containing
out-stars. The same holds for the "double out-star" (two adjacent centres, each
with `~N/2` out-leaves), and for the in-star with a centre of `κ ≥ 2`: a centre
`h` with `κ_h = 3` and `n` leaves with `κ = 1` passes `~C(n, 3)/n` tie sets per
order class. These are exactly the configurations the twin/out-leaf germ
functionals (`trees/PROGRESS.md`, steps 10–13) try to eliminate. Up to that
obstruction the locality count covers all trees: the only property of the unit
used below is the out-leaf bound.

## Proof

Notation as in the main route: a `k`-locality is a tie set `T`, `|T| = k`, and
an order of `O = V \ T`. The `k`-th mixed difference at the locality kills the
auxiliary span and is `±δ` on `max_N`; a unit with nonzero value **passes** the
locality, which forces (`DescrPass`):

* (a) every `o ∈ O` has exactly `κ_o` hinge neighbours above it (tied vertices
  are above all of `O`);
* (s) every `t ∈ T` with no hinge neighbour in `T` has `κ_t ≠ 0`.

Every locality is passed by some unit, so `C(N,k) k! (N−k)! ≤ Σ_F pass_k(F)`
and it suffices to show, for one unit,

    pass_k ≤ c_s^k k! (N − k)!.                                   (★)

Fix the unit; `F = M` is a forest, rooted so that each edge has a *child*
endpoint (the child map is injective on the edges). Let `H = {κ ≥ 1}`.

**Step 1 (L1: the tie set is determined by `T ∩ H`).** Let `κ_v ≤ 0`. Then

    v ∈ T  ⟺  κ_v ≠ 0, or v has a neighbour w with κ_w ≤ 0 or w ∈ T.

(⟹) by (s). (⟸) If `v ∉ T`, (a) gives `κ_v = 0` and no neighbour above `v`;
so no neighbour is tied, and a neighbour `w ∉ T` with `κ_w ≤ 0` also has no
neighbour above it, so `v` and `w` are each below the other — impossible. The
right-hand side only involves `T ∩ H`, so `T ↦ T ∩ H` is injective on the tie
sets of passed localities.

**Step 2 (L2).** Let `Y` be the set of untied vertices with an untied child.
Then

    |H \ T| ≤ (s + 1)(|T| + |Y|).

An untied `u ∈ H` either has an untied child (`u ∈ Y`), or has a tied child (at
most `|T|` such `u`, since the child determines its parent), or has no child.
In the last case all its edges are the edge to its parent `p`; by (a) `u` has
`κ_u ≥ 1` neighbours above it, so `u` has degree 1, `κ_u = 1` (an out-leaf) and
`p` is above `u`; `p ∈ T` or `p ∈ Y`, and each `p` has at most `s` out-leaves:
at most `s(|T| + |Y|)` such `u`.

**Step 3 (L3).** There is a matching `P` of hinge edges outside `T` with
`|Y| ≤ 2|P|`. For `y ∈ Y` choose the edge to an untied child. These `|Y|` edges
have maximum degree 2 (a vertex is on its own chosen edge and on at most one
edge as a child), and a forest of maximum degree `Δ` has a matching `P` with
`|E| ≤ Δ|P|` (take an edge at a leaf; it meets at most `Δ` edges).

**Step 4 (orders).** All orders passing with tie set `T` orient the forest
outside `T` in the same way (an orientation of a forest is determined by its
in-degrees), so prescribing the order of the `|P|` disjoint pairs gives at most
`k!(N − k)!/2^{|P|}` passed permutations with tie set `T`.

**Step 5 (generating function).** Let `β = 1 − 1/(4(s+1))`; Bernoulli gives
`β^{2(s+1)} ≥ 1/2` and `β^{s+1} ≥ 3/4`. By Steps 2–3,
`2(s+1)|P| ≥ |H| − |T ∩ H| − (s+1)k`, so

    2^{−|P|} ≤ β^{2(s+1)|P|} ≤ β^{|H| − |T∩H|} (4/3)^k.

By Step 1 the sets `X = T ∩ H` are distinct subsets of `H` with `|X| ≤ k`, and

    Σ_{X ⊆ H, |X| ≤ k} β^{|H|−|X|} ≤ (1−β)^{−k} Σ_{X ⊆ H} (1−β)^{|X|} β^{|H|−|X|}
                                  = (1−β)^{−k} = (4(s+1))^k.

Together: `pass_k ≤ k!(N−k)! (4/3)^k (4(s+1))^k`, which is (★). ∎

**Exponential form.** `(c+1)^N = Σ_m C(N,m) c^{N−m}`; for `m ≥ 3` each term is
`≤ c^N |K|` by the theorem, and for `m ≤ 2` by the quadratic count
`N(N−1) ≤ 6|K|` (valid for all tree units, and for caterpillars plus trees),
since `c ≥ 3`. Hence `(c+1)^N ≤ (N+1)c^N|K|` for every `N ≥ 3`.

**Sharper constant (paper only, not in Lean).** Taking `β = 2^{−1/(2(s+1))}`
exactly gives `c_s = √2 / (1 − 2^{−1/(2s+2)}) ≈ 4.08 (s+1)` (`4.83, 8.89, 12.96`
for `s = 0, 1, 2`). The worst bases observed numerically (hill-climbing over
forests with `n ≤ 7` vertices and all `κ`, `coverage_climb.py`) are much
smaller: about `1.44, 2.50, 2.83, 3.24` for `s = 0, 1, 2, 3`.

## Adversarial self-check

1. *Is `κ` integral, and is `κ ≤ 0` vs `κ ≥ 1` a dichotomy?* Yes: `κ_o = h_o +`
   (a count), `h` integral (`dkappa_le_zero_of_lt_one`).
2. *Does Step 1 use that the forest is a tree, or the apex?* No; only (a), (s)
   and the absence of loops (`m.1 < m.2`). It holds for an arbitrary hinge
   graph. Checked exhaustively in `coverage_check.py` (every instance).
3. *Step 2, "no child" case: could `u` have two parents?* No: every edge at `u`
   has child `u`, and the child map is injective, so there is at most one edge
   at `u`. The bound `up(u) ≤ deg(u)` needs no loops.
4. *Step 2: the parent `p ∉ T` is in `Y`?* `p` is untied and its child `u` is
   untied, so yes (no orientation needed). Isolated vertices of `H` are tied
   (they would need `κ ≥ 1` neighbours above), so they are in `X`.
5. *Step 3: is the chosen-edge graph a forest of degree ≤ 2?* It is a subset of
   `M` (a forest); a vertex `o` lies on the edge chosen by `o` and on edges whose
   child is `o` (at most one). The matching lemma needs only the leaf property of
   forests (`LeafProp`), which every subset of `M` inherits.
6. *Step 4: the matching edges are outside `T`?* Both ends are untied (`y ∈ Y`
   and its chosen child are untied).
7. *Step 5: exponent with `|H| − |X| < (s+1)k`?* Then the bound
   `2^{−|P|} ≤ 1 ≤ β^{|H|−|X|} β^{−(s+1)k}` holds trivially; the Lean proof
   multiplies through by `β^{(s+1)k}` and needs only
   `|H| − |X| ≤ 2(s+1)|P| + (s+1)k`.
8. *Is the hypothesis really weaker than "≤ s neighbours with κ ≥ 1"?* Yes: a
   vertex may have arbitrarily many neighbours with `κ ≥ 1` that are not leaves
   (e.g. long arms of a spider with `κ = 1` everywhere: `s ≤ 1` but unbounded
   degree), and arbitrarily many leaves with `κ ≤ 0` or `κ ≥ 2`.
9. *Numerics.* `coverage_check.py n trials seed`: random forests with random
   `κ ∈ {−1,…,3}`, exact enumeration of all `T` and all orders of `O`; asserts
   L1, L2 and `Σ_T x^{|T|} q(T) ≤ 1` at `x = 1/c_s`. Runs `n = 5` (400 trials),
   `n = 6` (300), hill-climb `n = 7` (6 × 250 steps): no failure.

## Lean status

Files (new, not imported by the root `MaxCaterpillar.lean`):
`MaxCaterpillar/Simplify/Coverage.lean` (654 lines: class, L1–L3, generating function,
per-unit count `card_dpasses_le_of_outLeaf`) and `MaxCaterpillar/Simplify/CoverageMain.lean`
(285 lines: class inclusions, assembly, public theorems). `lake build
MaxCaterpillar.Simplify.CoverageMain` succeeds.

Definitions: `Simplify.IsOutLeaf D u := (incid D.M u).card = 1 ∧ DKappa D u = 1`,
`Simplify.OutLeafBound D s := ∀ v U, (∀ u ∈ U, DAdj D v u ∧ IsOutLeaf D u) → U.card ≤ s`.

Public theorems (exact types in `coverage_claims.json`; re-elaborated and axiom-audited by
`CoverageStatements.lean`, log `coverage_statements.log`: all depend only on
`propext`, `Quot.sound`, `Classical.choice`):
* `tree_outLeaf_choose_le`: `C(N,k) ≤ (16(s+1)/3)^k |K|`, `3 ≤ k ≤ N`;
* `tree_outLeaf_exponential`: `(16(s+1)/3 + 1)^N ≤ (N+1)(16(s+1)/3)^N |K|`, `N ≥ 3`;
* `mixed_outLeaf_choose_le`, `mixed_outLeaf_exponential`: the same for `IsMixedExpansion`
  (caterpillar keys plus tree faces), `s ≥ 1`, with `|K₁| + |K₂|`;
* `outLeafBound_of_hubOK`, `outLeafBound_of_hingeDeg_le`, `starFace_outLeafBound`.
Helpers of note: `exists_matching_of_leaf` (forest matching `|E| ≤ Δ|P|`),
`tieSet_eq_of_inter_eq` (L1), `card_high_untied_le` (L2), `pow_le_of_choose_le`.

Not done (main session): the root does not import these files, so
`scripts/verify.py` cannot see them; to promote, add
`import MaxCaterpillar.Simplify.CoverageMain` to the root and append the entries of
`coverage_claims.json` to `verification/main.json`.
