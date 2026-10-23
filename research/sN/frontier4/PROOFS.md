# Width frontier of two-hidden-layer ReLU networks for max_4 (and max_3): proofs

Model. `σ = ReLU`. A network of widths `(h1, h2)` on `R^N` is
`F(x) = Σ_{k<h2} d_k σ(g_k(x))`, `g_k(x) = Σ_{j<h1} W_kj σ(a_j·x)`,
with zero biases and **no** linear or skip term anywhere; every neuron counts. Biases are no
restriction because `max_N` is positively homogeneous (Hertrich–Basu–Di Summa–Skutella, SIAM J.
Discrete Math. 37 (2023), Prop. 2.3). Padding with zero rows/neurons shows that the feasible set
of widths is up-closed, so `h2*(h1)` is non-increasing.

Notation (as in `research/sN/best5/PROOFS.md`). `1 = (1,…,1)`, `s_j = a_j·1`,
`J+ = {s_j > 0}`, `J- = {s_j < 0}`, `J0 = {s_j = 0}` (translation-invariant first-layer rows;
WLOG no row is zero). For a neuron `k`:
`λ⁺_k = Σ_{j∈J+} W_kj a_j`, `λ⁻_k = Σ_{j∈J-} W_kj a_j`, `C_k(x) = Σ_{j∈J0} W_kj σ(a_j·x)`,
`T⁺_k = λ⁺_k·1`, `T⁻_k = -λ⁻_k·1`. A "1HL function" is `ℓ(x) + Σ_j c_j σ(b_j·x)` with `ℓ` linear.
`1^⊥ = {covectors v : v·1 = 0}` (dimension `N-1`).

**Result.** For `N = 4` the feasible widths are exactly `{h1 ≥ 6, h2 ≥ 3}`. The Pareto
frontier is the single point `(6, 3)`: `h2*(h1) = 3` for `h1 ≥ 6`, and no network exists for
`h1 ≤ 5`. For `N = 3` the feasible widths are exactly `{h1 ≥ 4, h2 ≥ 3}` (frontier `(4, 3)`).
So for `N = 3, 4` both widths can be minimal at once; there is no trade-off.

---

## Lemma 0 (best5/PROOFS.md) and Lemma 0′

Lemma 0: `max(z_1,z_2,z_3)` is not a 1HL function on `R^3` (proof in best5/PROOFS.md: gradient
jump across `z_1 = z_2` is `e_1 - e_2` on `{z_1 = z_2 > z_3}` and `0` on `{z_1 = z_2 < z_3}`,
while a 1HL function has a constant jump along each of its hyperplanes).

Lemma 0′: for `N ≥ 3`, `max_N` is not a 1HL function on `R^N`.
Proof. Suppose `max_N = ℓ + Σ c_j σ(b_j·x)`. Let `p = (0,0,0,-1,…,-1)`. Near `p`, terms with
`b_j·p > 0` are linear, terms with `b_j·p < 0` vanish, and `max_N(p+z) = max(z_0,z_1,z_2)`.
So for small `z`, `max(z_0,z_1,z_2) = ℓ'(z) + Σ_{b_j·p=0} c_j σ(b_j·z)`; both sides are
positively homogeneous, so this holds for all `z`; restricting to `z ∈ span(e_0,e_1,e_2)`
contradicts Lemma 0. ∎

## Lemma T (behaviour along the diagonal)

For every `x`, for `t` large enough the rows in `J+` are active (`σ(a_j·(x+t1)) = a_j·x + s_j t`),
the rows in `J-` are inactive and `J0` rows are unchanged, so
`g_k(x+t1) = T⁺_k t + λ⁺_k·x + C_k(x)`. Let `P+ = {T⁺_k > 0}`, `Z+ = {T⁺_k = 0}`. For large `t`
neurons with `T⁺_k < 0` vanish, so comparing `F(x+t1) = max_N(x) + t` (both affine in `t` for
large `t`):

`(+∞)`  `Σ_{P+} d_k T⁺_k = 1`  and  `max_N(x) = Σ_{P+} d_k (λ⁺_k·x + C_k(x)) + Σ_{Z+} d_k σ(λ⁺_k·x + C_k(x))`.

Symmetrically for `t → -∞` (`g_k(x+t1) = T⁻_k |t| + λ⁻_k·x + C_k(x)`, `P- = {T⁻_k > 0}`,
`Z- = {T⁻_k = 0}`):

`(-∞)`  `Σ_{P-} d_k T⁻_k = -1`  and  `max_N(x) = Σ_{P-} d_k (λ⁻_k·x + C_k(x)) + Σ_{Z-} d_k σ(λ⁻_k·x + C_k(x))`.

For `k ∈ Z±`, `λ^±_k ∈ V± := span{a_j : j ∈ J±} ∩ 1^⊥`. Since `P+ ≠ ∅` some `T⁺_k ≠ 0`, so
`J+ ≠ ∅`; likewise `J- ≠ ∅`. As `span{a_j : j∈J±}` contains a vector with nonzero coordinate sum,
`dim V± ≤ |J±| - 1`. Also `Z± ≠ ∅`: otherwise `(±∞)` writes `max_N` as a 1HL function (Lemma 0′).

(This is the computation behind best5 Theorem H2, with the linear parts kept.)

## Lemma S (spanning): `|J0| + |J+| ≥ N` and `|J0| + |J-| ≥ N`

By `(+∞)`, `max_N - ℓ` (with `ℓ = Σ_{P+} d_k λ⁺_k`) is a function of the forms
`{a_j·x : j ∈ J0} ∪ {λ⁺_k·x : k ∈ Z+}`, all in `1^⊥`. Suppose their span `S` is a proper
subspace of `1^⊥`. Its annihilator in `R^N` has dimension `≥ 2`, so it contains a vector `w ∉ R1`.
Then `max_N(x + s w) - ℓ(x + s w)` is independent of `s`, so `s ↦ max_N(x + s w)` is affine for
every `x`. At `x = 0` it equals `s·max_i w_i` for `s > 0` and `s·min_i w_i` for `s < 0`, so
`max w = min w`, i.e. `w ∈ R1`: contradiction. Hence
`N - 1 ≤ dim S ≤ |J0| + dim V+ ≤ |J0| + |J+| - 1`. Same at `-∞`. ∎

In particular, if `|J+| = 1` then `V+ = 0`, every neuron in `Z+` has `λ⁺_k = 0`, and the `J0`
rows span `1^⊥`.

## Theorem 1 (second width): `h2 ≥ 3` for every `N ≥ 3` and every `h1`

Suppose `h2 = 2`. By Lemma T, `P+, Z+, P-, Z-` are all nonempty, so `|P+| = |Z+| = 1` and
`|P-| = |Z-| = 1`. If one neuron were in `P+ ∩ P-` it would have `d T⁺ = 1` and `d T⁻ = -1`
with `T^± > 0`, impossible. So the neurons are `n` with `P+ = {n} = Z-` and `m` with
`P- = {m} = Z+`, and `d_n > 0 > d_m`. Rescaling `W_n, W_m` by `|d_n|, |d_m|` (positive
homogeneity) we may take `d_n = 1`, `d_m = -1`. Write `C = C_n`, `D = C_m`,
`ℓ = λ⁺_n·x`, `ℓ' = λ⁻_m·x`, `G = λ⁺_m·x + D`, `H = λ⁻_n·x + C`. Then

`(+∞)`  `max_N = ℓ + C - σ(G)`,  `(-∞)`  `max_N = σ(H) - ℓ' - D`.

Subtracting and using `σ(u) = u + σ(-u)`:
`0 = ℓ + ℓ' + C + D - σ(G) - σ(H) = L(x) - σ(-G) - σ(-H)`, with
`L = ℓ + ℓ' - λ⁺_m·x - λ⁻_n·x` linear. Hence `L = σ(-G) + σ(-H) ≥ 0` everywhere; a
nonnegative linear function is `0`, so `σ(-G) ≡ 0`, i.e. `σ(G) = G`, and `(+∞)` reads
`max_N = ℓ + C - λ⁺_m·x - D`, a 1HL function. This contradicts Lemma 0′. ∎

Remarks. (a) `h2 ≥ 2` was best5 Theorem H2; Theorem 1 sharpens it for every `N ≥ 3`, in
particular `h2 ≥ 3` for `N = 5`. (b) No bound on `h1` is used. (c) A negative output weight
on the single free neuron is not itself the obstruction (`max_3 = a + σ(b-a) + σ(c-a)
- σ(b - a - σ(b - c))` is a valid 1HL-minus-one-neuron identity); what fails is satisfying
`(+∞)` and `(-∞)` simultaneously with the same `J0` parts `C, D`.

## Lemma C3 (best5 H1 (C3), for N = 4): every 3-set `I ⊂ [4]` contains the support of a `J0` row

Germ of `F` at `p = 1`: rows in `J±` have `a_j·1 ≠ 0` (linear or zero near `1`), `J0` rows vanish
at `1`. By positive homogeneity (best5 Lemma 1),
`max_4(z) = ℓ(z) + Σ_{J0} c_j σ(a_j·z) + Σ_{k: g_k(1)=0} d_k σ(μ_k·z + C_k(z))` for all `z`. (∗)
Let `{i} = [4] \ I` and `q = -e_i`. For a `J0` row, `a_j·q = -a_ji`, which is `0` iff
`supp a_j ⊆ I`. Taking the germ of (∗) at `q`, where `max_4(q + z) = max_{I} z` for small `z`,
rows with `supp ⊄ I` become linear or zero, so if no `J0` row had support in `I`, `max_I` would
be a 1HL function of `z_I`, contradicting Lemma 0. ∎
(`J0` supports have size `≥ 2`, so `|J0| ≥ 2`; two disjoint pairs suffice.)

## Lemma M (monomial lemma): `|J+| = 1` and `|J0| = 3` is impossible for N = 4

Assume `|J+| = 1` and `J0 = {r_1, r_2, r_3}`. By Lemma S, `r_1, r_2, r_3` is a basis of `1^⊥`
and every `k ∈ Z+` has `λ⁺_k = 0`, so `(+∞)` gives
`max_4(x) = ℓ(x) + Φ(σ(r_1·x), σ(r_2·x), σ(r_3·x))` (†)
with `ℓ = Σ_{P+} d_k λ⁺_k` linear and `Φ(s) = Σ_{P+} d_k W_k·s + Σ_{Z+} d_k σ(W_k·s)` a positively
homogeneous function of `s ∈ R^3_{≥0}` (`W_k·s := Σ_{J0} W_kj s_j`).
For `A ⊆ {1,2,3}` let `O_A = {x : r_j·x > 0 (j ∈ A), r_j·x < 0 (j ∉ A)}`; as the `r_j` are
independent, every `O_A` is a nonempty open cone. On `O_A` the right side of (†) depends on `x`
only through `ℓ(x)` and `(r_j·x)_{j∈A}`.

(i) `A = ∅`: `max_4 = ℓ + Φ(0) = ℓ` on `O_∅`. A maximum of linear functions that is linear on a
nonempty open convex set coincides there with one of them, so `O_∅ ⊆ B_i := {x_i ≥ x_k ∀k}` for
some `i` and `ℓ = x_i`. Put `g_k := x_k - x_i` (`k ≠ i`), a basis of `1^⊥`, and write
`g_k = Σ_j G_kj r_j`. Then `h := max_4 - x_i = max(0, g_k (k ≠ i))`.
Since `h = 0` on `O_∅`, `g_k ≤ 0` wherever all `r_j·x < 0`; as `(r_j·x)_j` ranges over the whole
open negative orthant on `O_∅`, all `G_kj ≥ 0`.

(ii) `A = {j}`: on `O_j`, `h(x) = Φ(0,…,r_j·x,…,0) = α_j (r_j·x)` (homogeneity in one positive
variable), so `h` is linear on the open cone `O_j`; hence `O_j` lies in one region `B_k` and
`h = g_k` (or `h = 0` if `k = i`) equals `α_j r_j` there.
If `k = i`: all `g_l ≤ 0` on `O_j`; but on `O_j` the value `r_j·x > 0` is arbitrary while the other
`r_l·x < 0` can be taken arbitrarily close to 0, so `g_l = Σ G_lj' r_j'·x ≤ 0` forces `G_lj = 0`
for all `l` — column `j` of the invertible matrix `G` would vanish. So `k = k(j) ≠ i` and
`g_{k(j)} = α_j r_j` with `α_j ≠ 0`.
Distinct `j` give distinct `k(j)` (row `k(j)` of `G` is a multiple of `e_j`), so `G` is a monomial
matrix with positive entries: the `J0` rows are positive multiples of `x_k - x_i`, `k ≠ i`.

(iii) Then no `J0` row has support in the 3-set `[4] \ {i}`, contradicting Lemma C3. ∎

## Theorem 2 (first width, N = 4): `h1 ≥ 6`

`h1 = |J+| + |J-| + |J0|`. Lemma C3: `|J0| ≥ 2`. Lemma S (`N = 4`): `|J+|, |J-| ≥ 4 - |J0|`.
- `|J0| = 2`: `|J±| ≥ 2`, `h1 ≥ 6`.
- `|J0| = 3`: `|J±| ≥ 1`; `|J+| = |J-| = 1` is excluded by Lemma M, so `h1 ≥ 3 + 1 + 2 = 6`.
- `|J0| ≥ 4`: `h1 ≥ 4 + 1 + 1 = 6`. ∎

In particular `h1 = 4` and `h1 = 5` are impossible for every `h2` (a stronger statement than
best5's H1 adapted to `N = 4`, which gives only `|J0| ≥ 2`, `h1 ≥ 4`).

## Theorem 3 (upper bound, N = 4): `(6, 3)` is attained — CERTIFIED

`m01 = σ(x_1) - σ(-x_1) + σ(x_0 - x_1) = max(x_0,x_1)`, `m23 = σ(x_3) - σ(-x_3) + σ(x_2 - x_3)`,
`F = σ(m23) - σ(-m23) + σ(m01 - m23) = m23 + σ(m01 - m23) = max_4`.
First layer (6 rows): `x_0-x_1, x_2-x_3, x_1, -x_1, x_3, -x_3`; second layer: `m23, -m23,
m01 - m23`; output `(1, -1, 1)`. File `net_N4_6_3.json`; `cert.py net_N4_6_3.json` →
`braid cells 24, leaf regions 84, failures 0 -> PASS` (exact rational cell decomposition,
copy of `best5/cert.py`). Shape: `|J+| = |J-| = |J0| = 2`, as Theorem 2 requires for `|J0| = 2`.

## Corollary (frontier, N = 4)

By Theorems 1–3 and padding, `(h1, h2)` is feasible iff `h1 ≥ 6` and `h2 ≥ 3`.
`h2*(h1) = 3` for `h1 ≥ 6`; infeasible for `h1 ≤ 5`. `(6, 3)` is minimal in both widths;
there is no trade-off. In particular `h2 = 1` and `h2 = 2` are impossible for every `h1`, and
`h1 + h2 ≥ 9` with equality only at `(6, 3)`.

## N = 3 (sanity check)

Lower bounds. Theorem 1: `h2 ≥ 3`. Lemma S (`N = 3`): `|J0| + |J±| ≥ 3`, so
`h1 ≥ min over |J0|` of `|J0| + 2 max(1, 3 - |J0|)` `= 4` (attained only at `|J0| = 2`,
`|J±| = 1`). (Lemma M's argument with `N = 3` forces the two `J0` rows to be the star
`x_k - x_i`, which now satisfies C3, so no further exclusion; consistent with the construction.)
Upper bound. First layer `x_0 - x_2, x_1 - x_2, x_2, -x_2`;
`F = σ(σ(x_2) + σ(x_0 - x_2)) - σ(σ(-x_2)) + σ(σ(x_1 - x_2) - σ(x_0 - x_2))
   = x_2 + max(σ(x_0-x_2), σ(x_1-x_2)) = max_3`
(the first neuron's input is nonnegative). File `net_N3_4_3.json`; `cert.py` → `braid cells 6,
leaf regions 12, failures 0 -> PASS`. Frontier for `N = 3`: the single point `(4, 3)`.
Note the J0 rows form the star at `x_2`, exactly as Lemma M's analysis predicts.

## What transfers to N = 5

1. Theorem 1 holds for all `N ≥ 3`: `h2 ≥ 3` for `max_5` (best5 had `h2 ≥ 2`), hence the total
   bound improves to `h1 + h2 ≥ 7 + 3 = 10`.
2. Lemma S for `N = 5`: `|J0| + |J±| ≥ 5`; with C3+C4 (`|J0| ≥ 5`) it adds nothing to `h1 ≥ 7`.
3. Lemma M generalizes to the **cell condition** (Lemma C): if `|J+| = 1`, then by `(+∞)`
   `max_N = ℓ + Φ(σ(r_j·x) : j ∈ J0)`, so on every open cell `K` of the `J0` arrangement with
   active set `A(K)` and every braid region `B_a` meeting `K`: `e_a - ℓ ∈ span{r_j : j ∈ A(K)}`.
   (Both sides of (†) restricted to `K` are functions of `(r_j·x)_{j∈A(K)}` plus `ℓ`; a
   function of these forms has gradient in their span.) For `N = 5`, `h1 = 7` forces
   `(|J+|,|J-|,|J0|) = (1,1,5)` (C3+C4 need 5 rows), so the cell condition applies.
   `cellcond.py` decides it exactly when all `J0` rows are roots `±(e_i - e_j)`:
   `N = 5, m = 5`: all 2304 oriented root families with C3+C4+rank 4 FAIL
   (`logs/cellcond_N5_m5.log`). Each failure is a proof: the sample points are exact witnesses
   of nonempty cells and the resulting linear system for `ℓ` is exactly inconsistent.
   Controls: for `N = 4, m = 3` all 96 C3+C4 families fail (agrees with Lemma M); the star
   `x_k - x_3` passes (positive control; it is excluded only by C3), the reversed star fails.
   Consequence: **a width-7 first layer for `max_5` must contain a translation-invariant row
   with support of size ≥ 3.** Whether such rows can pass is open (they carry continuous
   parameters, so the finite check does not cover them); `h1 ≥ 8` for `N = 5` is therefore
   not proved. Further evidence: all 2880 integer-coefficient instances (entries in [-3,3]) of
   the two families with 3-supports fail (`logs/cellcond_gen_B3.log`, measured), and with
   C3/C4 dropped the passing root families are exactly the stars (m = 4) and star + one root
   (m = 5) (`logs/cellcond_N5_noC3.log`).
   Conjecture (would give `h1 ≥ 8` for N = 5): the cell condition forces `J0` to contain a full
   star `{x_k - x_i : k ≠ i}`. Then C3 on the four 3-sets avoiding `i` needs two more rows, so
   `|J+| = 1` (or `|J-| = 1`) forces `|J0| ≥ 6` and `h1 ≥ min(1+1+6, 2+2+5) = 8`.
4. The two-level nesting that gives `(4,3)` and `(6,3)` needs a third hidden layer for `N = 5`,
   so the `N = 5` upper bounds (`best5`: `(10, 6)` certified) are of a different kind.
