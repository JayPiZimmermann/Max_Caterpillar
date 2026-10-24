import MaxCaterpillar.Simplify.Reduced

/-!
# One exponential count for tree units with a reduced forest of bounded degree

`research/sN/simplify/exponential.md`.  For tree face functions (`TreeFace`), the hinge
graph is a forest.  A *pendant* is a vertex with one hinge neighbour and `κ = 0`; removing
the pendants leaves the reduced forest.  If every unit of a tree expansion of `max_N` has a
reduced forest of maximum degree `≤ Δ` (`Δ ≥ 2`), then `C(N, k) ≤ (2Δ+2)^k |K|`
(`tree_reduced_choose_le`), hence `(2Δ+3)^N ≤ (N+1)(2Δ+2)^N |K|` for `N ≥ 6Δ + 8`, and
`7^N ≤ (N+1) 6^N |K|` for every `N ≥ 3` when `Δ = 2`.

Instances (`RedDeg`):
* `redDeg_of_isStar`: rooted stars of Brunck et al. and all their faces (every leaf
  omitted, linear, or hinge) have no reduced edge at all;
* `redDeg_of_isUpCaterpillar`: caterpillar trees whose leaves carry `σ(x_parent - x_leaf)`
  have reduced degree `≤ 2`;
* `redDeg_of_hingeDeg_le`: trees of hinge degree `≤ Δ`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Simplify

open MaxNN CountLower CountExp Trees

/-! ## The count for descriptions -/

/-- **Binomial count.** -/
theorem choose_le_of_red (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2) (hleaf : ∀ i ∈ K, LeafProp (D i).M)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hred : ∀ i ∈ K, RedDeg (D i) Δ)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ (2 * Δ + 2) ^ k * K.card := by
  classical
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆
      K.biUnion fun i => univ.filter (DPasses (D i) k) := by
    intro π _
    obtain ⟨i, hi, hp⟩ := exists_dpasses r K D hlt d a h hk hkN π
    exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ _, hp⟩⟩
  have h1 := (card_le_of_subset hcover).trans card_biUnion_le
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  set F := k ! * (r + 1 + 1 - k)!
  have h2 : ((r + 1 + 1)! : ℝ) ≤ K.card * ((F : ℝ) * (2 * Δ + 2 : ℝ) ^ k) := by
    have h1' : ((r + 1 + 1)! : ℝ) ≤ ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) := by
      exact_mod_cast h1
    refine h1'.trans ?_
    calc ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ)
        ≤ ∑ _i in K, (F : ℝ) * (2 * Δ + 2 : ℝ) ^ k :=
          sum_le_sum fun i hi => card_passes_le_red (D i) (hlt i hi) (hleaf i hi) hΔ (hred i hi) hkN
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) = ((r + 1 + 1).choose k : ℝ) * (F : ℝ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]; push_cast; ring
  have hpos : (0 : ℝ) < F := by exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  rw [hfac] at h2
  have h3 : ((r + 1 + 1).choose k : ℝ) ≤ ((2 * Δ + 2 : ℕ) : ℝ) ^ k * K.card := by
    have h4 : ((r + 1 + 1).choose k : ℝ) * (F : ℝ) ≤
        (((2 * Δ + 2 : ℕ) : ℝ) ^ k * K.card) * (F : ℝ) := by
      convert h2 using 1 <;> push_cast <;> ring
    exact le_of_mul_le_mul_right h4 hpos
  exact_mod_cast h3

/-- From the binomial count for every `3 ≤ k ≤ N`: `(b+1)^N ≤ (N+1) b^N Z` when
`N ≥ 3b + 2` (the terms `m ≤ 2` of `(b+1)^N = Σ_m C(N,m) b^(N-m)` are dominated by the
term `m = 3`). -/
theorem eventual_pow_le_of_choose_le {N Z b : ℕ} (hb : 1 ≤ b) (hN : 3 * b + 2 ≤ N)
    (hZ : ∀ k, 3 ≤ k → k ≤ N → N.choose k ≤ b ^ k * Z) :
    (b + 1) ^ N ≤ (N + 1) * b ^ N * Z := by
  have hstep : ∀ m, m < 3 → N.choose m * b ≤ N.choose (m + 1) := by
    intro m hm
    have e := Nat.choose_succ_right_eq N m
    have hle : b * (m + 1) ≤ N - m := by
      apply (Nat.le_sub_iff_add_le (by omega : m ≤ N)).mpr
      calc b * (m + 1) + m ≤ b * 3 + 2 :=
            Nat.add_le_add (Nat.mul_le_mul_left b (by omega)) (by omega)
        _ = 3 * b + 2 := by ring
        _ ≤ N := hN
    have : N.choose m * b * (m + 1) ≤ N.choose (m + 1) * (m + 1) := by
      rw [e, mul_assoc]; exact Nat.mul_le_mul_left _ hle
    exact le_of_mul_le_mul_right this (Nat.succ_pos m)
  have hdom : ∀ m, m ≤ 2 → N.choose m * b ^ (3 - m) ≤ N.choose 3 := by
    intro m hm
    have s0 := hstep 0 (by norm_num)
    have s1 := hstep 1 (by norm_num)
    have s2 := hstep 2 (by norm_num)
    interval_cases m
    · calc N.choose 0 * b ^ 3 = N.choose 0 * b * b * b := by ring
        _ ≤ N.choose 1 * b * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ s0)
        _ ≤ N.choose 2 * b := Nat.mul_le_mul_right _ s1
        _ ≤ N.choose 3 := s2
    · calc N.choose 1 * b ^ 2 = N.choose 1 * b * b := by ring
        _ ≤ N.choose 2 * b := Nat.mul_le_mul_right _ s1
        _ ≤ N.choose 3 := s2
    · simpa using s2
  have h3 := hZ 3 le_rfl (by omega)
  have hterm : ∀ m ∈ range (N + 1), N.choose m * b ^ (N - m) ≤ b ^ N * Z := by
    intro m hm
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hm)
    by_cases hm3 : 3 ≤ m
    · calc N.choose m * b ^ (N - m) ≤ b ^ m * Z * b ^ (N - m) :=
            Nat.mul_le_mul_right _ (hZ m hm3 hmN)
        _ = b ^ (m + (N - m)) * Z := by rw [pow_add]; ring
        _ = b ^ N * Z := by rw [Nat.add_sub_cancel' hmN]
    · push_neg at hm3
      have hd := hdom m (by omega)
      calc N.choose m * b ^ (N - m) = N.choose m * b ^ (3 - m) * b ^ (N - 3) := by
            rw [mul_assoc, ← pow_add]; congr 2; omega
        _ ≤ N.choose 3 * b ^ (N - 3) := Nat.mul_le_mul_right _ hd
        _ ≤ b ^ 3 * Z * b ^ (N - 3) := Nat.mul_le_mul_right _ h3
        _ = b ^ (3 + (N - 3)) * Z := by rw [pow_add]; ring
        _ = b ^ N * Z := by rw [Nat.add_sub_cancel' (by omega)]
  have hbin : (b + 1) ^ N = ∑ m in range (N + 1), N.choose m * b ^ (N - m) := by
    rw [add_comm, add_pow]
    refine sum_congr rfl fun m _ => ?_
    rw [one_pow, one_mul, mul_comm]
    rfl
  rw [hbin]
  calc ∑ m in range (N + 1), N.choose m * b ^ (N - m)
      ≤ ∑ _m in range (N + 1), b ^ N * Z := sum_le_sum hterm
    _ = (N + 1) * b ^ N * Z := by rw [sum_const, card_range, smul_eq_mul]; ring

/-- For `b = 6` the bound holds for every `N ≥ 3`: `7^N ≤ (N+1) 6^N Z`. -/
theorem seven_pow_le_of_choose_le' {N Z : ℕ} (hN : 3 ≤ N)
    (hZ : ∀ k, 3 ≤ k → k ≤ N → N.choose k ≤ 6 ^ k * Z) :
    7 ^ N ≤ (N + 1) * 6 ^ N * Z := by
  by_cases hbig : 20 ≤ N
  · exact eventual_pow_le_of_choose_le (b := 6) (by norm_num) (by omega) hZ
  have h3 := hZ 3 le_rfl hN
  have hZ1 : 1 ≤ Z := by
    by_contra h0
    have : Z = 0 := by omega
    rw [this, mul_zero] at h3
    exact absurd (Nat.choose_pos hN) (by omega)
  have hb : 7 ^ N ≤ (N + 1) * 6 ^ N := by
    push_neg at hbig
    interval_cases N <;> norm_num
  calc 7 ^ N ≤ (N + 1) * 6 ^ N := hb
    _ = (N + 1) * 6 ^ N * 1 := by ring
    _ ≤ (N + 1) * 6 ^ N * Z := Nat.mul_le_mul_left _ hZ1

/-! ## Tree faces -/

namespace TreeFaceR

open Classical

variable {N : ℕ} (F : TreeFace N)

/-- A pair of the description contains `u` iff it is the edge of `u` or of a child of `u`. -/
theorem mem_pair_iff {m : Fin N × Fin N} (hm : m ∈ F.descr.M) (u : Fin N) :
    (m.1 = u ∨ m.2 = u) ↔ ∃ v ∈ F.edgeVerts, F.state v = .hinge ∧
      m = TreeFace.normPair (F.gen v) ∧ (v = u ∨ F.parent v = u) := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
  obtain ⟨hvE, hvs⟩ := mem_filter.mp hv
  constructor
  · intro h
    exact ⟨v, hvE, hvs, rfl, (F.gen_mem v u).mp ((TreeFace.normPair_mem _ u).mp h)⟩
  · rintro ⟨w, hwE, -, he, hw⟩
    have hw' : v = w := F.normPair_inj hvE hwE he
    subst hw'
    exact (TreeFace.normPair_mem _ u).mpr ((F.gen_mem v u).mpr hw)

/-- Hinge neighbours come from hinge edges. -/
theorem dadj_iff {u x : Fin N} : DAdj F.descr u x ↔ ∃ v ∈ F.edgeVerts, F.state v = .hinge ∧
    ((v = u ∧ F.parent v = x) ∨ (v = x ∧ F.parent v = u)) := by
  constructor
  · intro h
    have hm : ∃ m ∈ F.descr.M, (m = (u, x) ∨ m = (x, u)) := by
      rcases h with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    obtain ⟨m, hmM, hmx⟩ := hm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hmM
    obtain ⟨hvE, hvs⟩ := mem_filter.mp hv
    refine ⟨v, hvE, hvs, ?_⟩
    have hp := F.parent_ne_self hvE
    unfold TreeFace.normPair TreeFace.gen at hmx
    split_ifs at hmx <;> simp only [Prod.mk.injEq] at hmx <;>
      rcases hmx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
        | exact Or.inl ⟨h1, h2⟩ | exact Or.inl ⟨h2, h1⟩
        | exact Or.inr ⟨h1, h2⟩ | exact Or.inr ⟨h2, h1⟩
  · rintro ⟨v, hvE, hvs, hv⟩
    have hmM : TreeFace.normPair (F.gen v) ∈ F.descr.M :=
      mem_image.mpr ⟨v, mem_filter.mpr ⟨hvE, hvs⟩, rfl⟩
    unfold DAdj
    unfold TreeFace.normPair TreeFace.gen at hmM
    split_ifs at hmM <;>
      rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact Or.inl hmM | exact Or.inr hmM

/-- A tree leaf with a hinge `σ(x_parent - x_v)` is a pendant. -/
theorem isPend_of_leaf {v : Fin N} (hvE : v ∈ F.edgeVerts)
    (hleaf : ∀ w ∈ F.edgeVerts, F.parent w ≠ v) (hs : F.state v = .hinge) (hup : F.up v = true) :
    IsPend F.descr v := by
  have hgen : F.gen v = (F.parent v, v) := by simp [TreeFace.gen, hup]
  have hpv := F.parent_ne_self hvE
  have hv' := (F.mem_edgeVerts).mp hvE
  -- the only pair at `v` is the edge of `v`
  have honly : ∀ m ∈ F.descr.M, (m.1 = v ∨ m.2 = v) → m = TreeFace.normPair (F.parent v, v) := by
    intro m hm hmv
    obtain ⟨w, hwE, -, rfl, hw⟩ := (mem_pair_iff F hm v).mp hmv
    rcases hw with rfl | hw
    · rw [hgen]
    · exact absurd hw (hleaf w hwE)
  have hmem : TreeFace.normPair (F.parent v, v) ∈ F.descr.M :=
    mem_image.mpr ⟨v, mem_filter.mpr ⟨hvE, hs⟩, by rw [hgen]⟩
  constructor
  · rw [card_eq_one]
    refine ⟨F.parent v, ?_⟩
    ext x
    rw [mem_nbrs, mem_singleton]
    constructor
    · intro hx
      obtain ⟨w, hwE, -, hw⟩ := (dadj_iff F).mp hx
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, hw⟩
      · rfl
      · exact absurd hw (hleaf _ hwE)
    · rintro rfl
      exact (dadj_iff F).mpr ⟨v, hvE, hs, Or.inl ⟨rfl, rfl⟩⟩
  · unfold DKappa
    have hh : F.descr.h v = if v < F.parent v then -1 else 0 := by
      show ((if v = F.root then 1 else 0) - (if v = F.apex then 1 else 0)) +
        ∑ w in F.edgeVerts, (if F.headShift w then
          ((if v = (F.gen w).1 then 1 else 0) - (if v = (F.gen w).2 then 1 else 0)) else 0) = _
      rw [if_neg hv'.1, if_neg hv'.2, sum_eq_single v]
      · have hhs : F.headShift v ↔ v < F.parent v := by
          unfold TreeFace.headShift; rw [hgen, hs]; simp
        rw [hgen]
        simp only [if_neg hpv.symm, if_pos rfl]
        by_cases h : v < F.parent v
        · rw [if_pos (hhs.mpr h), if_pos h]; norm_num
        · rw [if_neg (fun h' => h (hhs.mp h')), if_neg h]; norm_num
      · intro w hwE hwv
        have h1 : v ≠ (F.gen w).1 ∧ v ≠ (F.gen w).2 := by
          constructor <;> intro he
          · have := (F.gen_mem w v).mp (Or.inl he.symm)
            rcases this with h | h
            · exact hwv h
            · exact hleaf w hwE h
          · have := (F.gen_mem w v).mp (Or.inr he.symm)
            rcases this with h | h
            · exact hwv h
            · exact hleaf w hwE h
        simp [h1.1, h1.2]
      · intro h; exact absurd hvE h
    have hc : (F.descr.M.filter fun m => m.1 = v).card = if v < F.parent v then 1 else 0 := by
      by_cases h : v < F.parent v
      · rw [if_pos h, card_eq_one]
        refine ⟨TreeFace.normPair (F.parent v, v), ?_⟩
        ext m
        rw [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hm, hm1⟩; exact honly m hm (Or.inl hm1)
        · rintro rfl
          refine ⟨hmem, ?_⟩
          unfold TreeFace.normPair; rw [if_neg (not_lt.mpr h.le)]
      · rw [if_neg h, card_eq_zero, filter_eq_empty_iff]
        intro m hm hm1
        have := honly m hm (Or.inl hm1)
        rw [this] at hm1
        unfold TreeFace.normPair at hm1
        split_ifs at hm1 with h'
        · exact hpv hm1
        · exact hpv (le_antisymm (not_lt.mp h) (not_lt.mp h'))
    rw [hh, hc]
    split_ifs <;> norm_num

/-- The faces of the rooted-star pyramids of Brunck et al.: every edge joins a leaf to the
root `c` and carries `x_c - x_l` (omitted, linear, or as the hinge `σ(x_c - x_l)`). -/
def IsStarFace : Prop := ∀ v ∈ F.edgeVerts, F.parent v = F.root ∧ F.up v = true

/-- Caterpillar trees whose leaves carry `x_parent - x_leaf`: a spine `P` containing the root,
closed under `parent`, a path (no two spine vertices share a parent), every other vertex
except the apex a leaf of the spine with `up = true`. -/
def IsUpCaterpillar : Prop :=
  ∃ P : Finset (Fin N), F.root ∈ P ∧ F.apex ∉ P ∧
    (∀ v ∈ P, v ≠ F.root → F.parent v ∈ P) ∧
    (∀ u ∈ P, ∀ v ∈ P, u ≠ F.root → v ≠ F.root → F.parent u = F.parent v → u = v) ∧
    (∀ v, v ∉ P → v ≠ F.apex → F.parent v ∈ P ∧ F.up v = true)

/-- Rooted stars and all their faces have no reduced edge. -/
theorem redDeg_of_isStar (hF : IsStarFace F) (Δ : ℕ) : RedDeg F.descr Δ := by
  intro u
  rw [card_eq_zero.mpr]
  · exact Nat.zero_le _
  rw [filter_eq_empty_iff]
  intro x _ hR
  obtain ⟨v, hvE, hvs, hv⟩ := (dadj_iff F).mp hR.1
  have hleaf : ∀ w ∈ F.edgeVerts, F.parent w ≠ v := by
    intro w hwE h
    rw [(hF w hwE).1] at h
    exact ((F.mem_edgeVerts).mp hvE).1 h.symm
  have hp := isPend_of_leaf F hvE hleaf hvs (hF v hvE).2
  rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hR.2.1 hp
  · exact hR.2.2 hp

/-- Caterpillar trees with upward leaves have reduced degree `≤ 2`. -/
theorem redDeg_of_isUpCaterpillar (hF : IsUpCaterpillar F) : RedDeg F.descr 2 := by
  obtain ⟨P, hrP, haP, hclosed, hinj, hleafP⟩ := hF
  intro u
  set Ch := P.filter fun w => w ≠ F.root ∧ F.parent w = u
  have hCh : Ch.card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    obtain ⟨haP', ha1, ha2⟩ := mem_filter.mp ha
    obtain ⟨hbP', hb1, hb2⟩ := mem_filter.mp hb
    exact hinj a haP' b hbP' ha1 hb1 (ha2.trans hb2.symm)
  have hsub : univ.filter (RAdj F.descr u) ⊆ insert (F.parent u) Ch := by
    intro x hx
    have hR := (mem_filter.mp hx).2
    obtain ⟨v, hvE, hvs, hv⟩ := (dadj_iff F).mp hR.1
    have hv' := (F.mem_edgeVerts).mp hvE
    have hvP : v ∈ P := by
      by_contra hvP
      have hleaf : ∀ w ∈ F.edgeVerts, F.parent w ≠ v := by
        intro w hwE h
        by_cases hwP : w ∈ P
        · exact hvP (h ▸ hclosed w hwP ((F.mem_edgeVerts).mp hwE).1)
        · exact hvP (h ▸ (hleafP w hwP ((F.mem_edgeVerts).mp hwE).2).1)
      have hp := isPend_of_leaf F hvE hleaf hvs (hleafP v hvP hv'.2).2
      rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hR.2.1 hp
      · exact hR.2.2 hp
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, hpu⟩
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hvP, hv'.1, hpu⟩)
  calc (univ.filter (RAdj F.descr u)).card ≤ (insert (F.parent u) Ch).card := card_le_of_subset hsub
    _ ≤ Ch.card + 1 := card_insert_le _ _
    _ ≤ 2 := by omega

/-- Trees of hinge degree `≤ Δ` have reduced degree `≤ Δ`. -/
theorem redDeg_of_hingeDeg_le {Δ : ℕ} (h : ∀ u, F.hingeDeg u ≤ Δ) : RedDeg F.descr Δ := by
  intro u
  refine le_trans ?_ ((F.incid_descr_le u).trans (h u))
  unfold incid
  refine card_le_card_of_inj_on (fun x => ord2 u x) (fun x hx => ?_) (fun x hx x' _ he => ?_)
  · have hR := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨ord2_mem (F.descr_lt) hR.1, ?_⟩
    dsimp only [ord2]; split_ifs <;> simp
  · have hR := (mem_filter.mp hx).2
    have hxu : x ≠ u := fun e => dadj_irrefl F.descr_lt u (by rw [e] at hR; exact hR.1)
    simp only at he
    unfold ord2 at he
    split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> rcases he with ⟨h1, h2⟩ <;>
      first | exact h2 | exact h1 | exact absurd h2 hxu | exact absurd h1 hxu

end TreeFaceR

/-! ## Public statements -/

namespace TreeFaceR

theorem expansion_descr {r : ℕ} {K : Finset (TreeFace (r + 1 + 1))} (d : TreeFace (r + 1 + 1) → ℝ)
    (a : Fin (MaxNN.Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x =
      ∑ F in K, d F * F.unit x + ∑ j, a j * auxiliaryFunction (r + 1 + 1) j x) :
    ∀ x, Maximum (r + 1 + 1) x = ∑ F in K, d F * F.descr.unit x + auxiliary a x := by
  intro x
  rw [h x]
  simp only [TreeFace.descr_unit]
  rfl

end TreeFaceR

/-- **Binomial count for tree units with a reduced forest of degree `≤ Δ`.** -/
theorem tree_reduced_choose_le (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hred : ∀ F ∈ K, RedDeg F.descr Δ)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    (r + 1 + 1).choose k ≤ (2 * Δ + 2) ^ k * K.card := by
  obtain ⟨d, a, h⟩ := hK
  exact choose_le_of_red r K (fun F => F.descr) (fun F _ => F.descr_lt)
    (fun F _ => F.descr_leaf) hΔ hred d a (TreeFaceR.expansion_descr d a h) hk hkN

/-- **Exponential count, general `Δ`.** For `N ≥ 6Δ + 8`:
`(2Δ+3)^N ≤ (N+1) (2Δ+2)^N |K|`. -/
theorem tree_reduced_exponential (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 2 ≤ Δ) (hred : ∀ F ∈ K, RedDeg F.descr Δ)
    (hN : 6 * Δ + 8 ≤ r + 1 + 1) :
    (2 * Δ + 2 + 1) ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * (2 * Δ + 2) ^ (r + 1 + 1) * K.card :=
  eventual_pow_le_of_choose_le (by omega) (by omega) fun _k hk hkN =>
    tree_reduced_choose_le r hK hΔ hred hk hkN

/-- **Exponential count, `Δ = 2`** (caterpillars, rooted stars and all their faces):
`7^N ≤ (N+1) 6^N |K|` for every `N ≥ 3`. -/
theorem tree_reduced_exponential_two (r : ℕ) (hr : 1 ≤ r) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) (hred : ∀ F ∈ K, RedDeg F.descr 2) :
    7 ^ (r + 1 + 1) ≤ (r + 1 + 1 + 1) * 6 ^ (r + 1 + 1) * K.card :=
  seven_pow_le_of_choose_le' (by omega) fun _k hk hkN =>
    tree_reduced_choose_le r hK le_rfl hred hk hkN

end MaxCaterpillar.Simplify
