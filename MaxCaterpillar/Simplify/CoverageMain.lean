import MaxCaterpillar.Simplify.Coverage
import Mathlib.Data.Nat.Choose.Cast

/-!
# Coverage: exponential counts for trees with few out-leaves per vertex

`research/sN/simplify/coverage.md`.  Write `c_s = 16(s+1)/3`.

* `tree_outLeaf_choose_le`: if every tree unit of an expansion of `max_N` has at most `s`
  out-leaves at every vertex (`OutLeafBound`), then `C(N,k) ≤ c_s^k |K|` for `3 ≤ k ≤ N`;
* `tree_outLeaf_exponential`: `(c_s + 1)^N ≤ (N + 1) c_s^N |K|` for every `N ≥ 3`;
* `mixed_outLeaf_choose_le`, `mixed_outLeaf_exponential`: the same with caterpillar
  descriptions added to the vocabulary (`IsMixedExpansion`, `s ≥ 1`);
* the class contains the trees of hinge degree `≤ Δ` (`s = Δ`), the hub class `HubOK Δ`
  (`s = Δ`) and the rooted stars of Brunck et al. (`s = 1`).
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Simplify

open MaxNN CountLower CountExp Trees
open MaxNN.Caterpillar MaxNN.Caterpillar.Corrections CountCubic

variable {N : ℕ}

/-! ## The class contains bounded degree, the hub class and rooted stars -/

theorem mem_image_other {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) {v u : Fin N}
    (h : DAdj D v u) : u ∈ (incid D.M v).image fun m => if m.1 = v then m.2 else m.1 := by
  rw [mem_image]
  rcases h with h | h
  · exact ⟨(v, u), mem_filter.mpr ⟨h, Or.inl rfl⟩, by simp⟩
  · refine ⟨(u, v), mem_filter.mpr ⟨h, Or.inr rfl⟩, ?_⟩
    have huv : u ≠ v := ne_of_lt (hlt _ h)
    simp [huv]

/-- The hub class `HubOK Δ` has at most `Δ` out-leaves at every vertex. -/
theorem outLeafBound_of_hubOK {D : Descr N} (hlt : ∀ m ∈ D.M, m.1 < m.2) {Δ : ℕ}
    (hH : HubOK D Δ) : OutLeafBound D Δ := by
  classical
  intro v U hU
  by_cases hv : Δ < deg D v
  · rcases U.eq_empty_or_nonempty with hU0 | ⟨u, hu⟩
    · rw [hU0, card_empty]
      exact Nat.zero_le _
    · exfalso
      have h1 := hH v hv u (hU u hu).1
      have h2 := (hU u hu).2.2
      linarith
  · calc U.card ≤ ((incid D.M v).image fun m => if m.1 = v then m.2 else m.1).card :=
          card_le_of_subset fun u hu => mem_image_other hlt (hU u hu).1
      _ ≤ (incid D.M v).card := card_image_le
      _ ≤ Δ := not_lt.mp hv

/-- Trees of hinge degree `≤ Δ` have at most `Δ` out-leaves at every vertex. -/
theorem outLeafBound_of_hingeDeg_le (F : TreeFace N) {Δ : ℕ} (h : ∀ u, F.hingeDeg u ≤ Δ) :
    OutLeafBound F.descr Δ :=
  outLeafBound_of_hubOK F.descr_lt (F.hubOK_of_hingeDeg_le h)

/-- The rooted stars of Brunck et al. have at most one out-leaf at every vertex. -/
theorem starFace_outLeafBound (a c : Fin N) (hac : c ≠ a) :
    OutLeafBound (starFace a c hac).descr 1 :=
  outLeafBound_of_hubOK (starFace a c hac).descr_lt (starFace_hubOK a c hac le_rfl)

/-! ## From the per-unit count to the binomial count -/

open Classical in
/-- If every unit passes at most `c^k k! (N-k)!` localities of order `k`, then
`C(N, k) ≤ c^k |K|`. -/
theorem choose_le_of_unit_bound (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2) (c : ℝ) {k : ℕ} (hk : 3 ≤ k)
    (hkN : k ≤ r + 1 + 1)
    (hunit : ∀ i ∈ K, (((univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))).filter
      (DPasses (D i) k)).card : ℝ) ≤ c ^ k * (k ! * (r + 1 + 1 - k)! : ℕ))
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x) :
    ((r + 1 + 1).choose k : ℝ) ≤ c ^ k * K.card := by
  classical
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆
      K.biUnion fun i => univ.filter (DPasses (D i) k) := by
    intro π _
    obtain ⟨i, hi, hp⟩ := exists_dpasses r K D hlt d a h hk hkN π
    exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨mem_univ _, hp⟩⟩
  have h1 := card_le_of_subset hcover
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h2 : ((r + 1 + 1)! : ℝ) ≤
      ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) := by
    have := h1.trans card_biUnion_le
    exact_mod_cast this
  have h3 : ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ) ≤
      K.card * (c ^ k * (k ! * (r + 1 + 1 - k)! : ℕ)) := by
    calc ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ)
        ≤ ∑ _i in K, (c ^ k * (k ! * (r + 1 + 1 - k)! : ℕ) : ℝ) := sum_le_sum hunit
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) =
      ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]
    push_cast
    ring
  have hpos : (0 : ℝ) < (k ! * (r + 1 + 1 - k)! : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h4 := h2.trans h3
  rw [hfac] at h4
  have h5 : ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) ≤
      (c ^ k * K.card) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    linarith
  exact le_of_mul_le_mul_right h5 hpos

/-! ## From the binomial count to the exponential count -/

/-- `C(N, m) ≤ c^m Z` for `3 ≤ m ≤ N` and `N (N-1) ≤ 6 Z` give `(c + 1)^N ≤ (N + 1) c^N Z`
for `N ≥ 3` and `c ≥ 3`. -/
theorem pow_le_of_choose_le {N : ℕ} (hN : 3 ≤ N) {c Z : ℝ} (hc : 3 ≤ c)
    (hquad : (N : ℝ) * ((N : ℝ) - 1) ≤ 6 * Z)
    (hchoose : ∀ m, 3 ≤ m → m ≤ N → (N.choose m : ℝ) ≤ c ^ m * Z) :
    (c + 1) ^ N ≤ (N + 1) * c ^ N * Z := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hcpos : (0 : ℝ) < c := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hterm : ∀ m ≤ N, (N.choose m : ℝ) * c ^ (N - m) ≤ c ^ N * Z := by
    intro m hm
    have hcm : c ^ (N - m) * c ^ m = c ^ N := by rw [← pow_add, Nat.sub_add_cancel hm]
    have hp := pow_pos hcpos (N - m)
    have key : (N.choose m : ℝ) ≤ c ^ m * Z := by
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · interval_cases m
        · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul]
          exact hZ1
        · rw [Nat.choose_one_right, pow_one]
          nlinarith
        · rw [Nat.cast_choose_two]
          have hc2 : (9 : ℝ) ≤ c ^ 2 := by nlinarith
          have h9 : 9 * Z ≤ c ^ 2 * Z := mul_le_mul_of_nonneg_right hc2 (by linarith)
          linarith
      · exact hchoose m hm3 hm
    calc (N.choose m : ℝ) * c ^ (N - m) ≤ (c ^ m * Z) * c ^ (N - m) :=
          mul_le_mul_of_nonneg_right key hp.le
      _ = (c ^ (N - m) * c ^ m) * Z := by ring
      _ = c ^ N * Z := by rw [hcm]
  have hbin : (c + 1) ^ N = ∑ m in range (N + 1), (N.choose m : ℝ) * c ^ (N - m) := by
    rw [add_comm, add_pow]
    refine sum_congr rfl fun m _ => ?_
    rw [one_pow, one_mul, mul_comm]
  rw [hbin]
  calc ∑ m in range (N + 1), (N.choose m : ℝ) * c ^ (N - m)
      ≤ ∑ _m in range (N + 1), c ^ N * Z :=
        sum_le_sum fun m hm => hterm m (Nat.lt_succ_iff.mp (mem_range.mp hm))
    _ = (N + 1) * c ^ N * Z := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ## Public statements: tree expansions -/

/-- **Binomial count for trees with few out-leaves.** If every unit `F` of a tree expansion
of `max_N` (`N = r + 2`) has at most `s` out-leaves (hinge leaves with `κ = 1`) at every
vertex, then `C(N, k) ≤ (16(s+1)/3)^k |K|` for `3 ≤ k ≤ N`. -/
theorem tree_outLeaf_choose_le (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {s : ℕ} (hs : ∀ F ∈ K, OutLeafBound F.descr s) {k : ℕ}
    (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ (16 * ((s : ℝ) + 1) / 3) ^ k * K.card := by
  obtain ⟨d, a, h⟩ := hK
  have h' : ∀ x, Maximum (r + 1 + 1) x = ∑ F in K, d F * F.descr.unit x + auxiliary a x := by
    intro x
    rw [h x]
    congr 1
    exact sum_congr rfl fun F _ => by rw [TreeFace.descr_unit]
  exact choose_le_of_unit_bound r K (fun F => F.descr) (fun F _ => F.descr_lt) _ hk hkN
    (fun F hF => card_dpasses_le_of_outLeaf F.descr F.descr_lt F.descr_leaf F.child
      F.descr_child_spec F.descr_child_inj (hs F hF) hkN) d a h'

/-- **Exponential count for trees with few out-leaves.** With `c = 16(s+1)/3`,
`(c + 1)^N ≤ (N + 1) c^N |K|` for every `N = r + 2 ≥ 3`, i.e.
`|K| ≥ (1 + 3/(16(s+1)))^N / (N + 1)`. -/
theorem tree_outLeaf_exponential (r : ℕ) (hr : 1 ≤ r) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {s : ℕ} (hs : ∀ F ∈ K, OutLeafBound F.descr s) :
    (16 * ((s : ℝ) + 1) / 3 + 1) ^ (r + 1 + 1) ≤
      ((r + 1 + 1 : ℕ) + 1) * (16 * ((s : ℝ) + 1) / 3) ^ (r + 1 + 1) * K.card := by
  have hquad := tree_expansion_quadratic r hr hK
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  apply pow_le_of_choose_le (by omega) (by linarith)
  · have : (((r + 1 + 1) * (r + 1) : ℕ) : ℝ) ≤ ((6 * K.card : ℕ) : ℝ) := by exact_mod_cast hquad
    push_cast at this ⊢
    linarith
  · intro m hm3 hmN
    exact tree_outLeaf_choose_le r hK hs hm3 hmN

/-! ## Public statements: caterpillars together with trees -/

/-- The quadratic count for an expansion by caterpillar and tree face functions. -/
theorem mixed_quadratic (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) :
    (r + 1 + 1) * (r + 1) ≤ 6 * (K₁.card + K₂.card) := by
  obtain ⟨hsub, d₁, d₂, a, h⟩ := hK
  have := count_lower_of_good r hr (K₁.disjSum K₂)
    (Sum.elim (fun key => caterpillarFunction key) fun F => F.unit)
    (by
      rintro (key | F) hi
      · obtain ⟨D, apex, hD, hU⟩ := exists_descr (hsub (inl_mem_disjSum.mp hi))
        exact ⟨D, apex, hD, hU⟩
      · exact ⟨F.descr, F.apex, F.descr_good (by omega), fun y => (F.descr_unit y).symm⟩)
    (Sum.elim d₁ d₂) a
    (by
      intro x
      rw [sum_disj_sum]
      exact h x)
  rwa [card_disjSum] at this

/-- **Binomial count for caterpillars plus trees with few out-leaves** (`s ≥ 1`):
`C(N, k) ≤ (16(s+1)/3)^k (|K₁| + |K₂|)` for `3 ≤ k ≤ N`. -/
theorem mixed_outLeaf_choose_le (r : ℕ) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) {s : ℕ} (hs1 : 1 ≤ s)
    (hs : ∀ F ∈ K₂, OutLeafBound F.descr s) {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ (16 * ((s : ℝ) + 1) / 3) ^ k * (K₁.card + K₂.card) := by
  classical
  obtain ⟨hsub, d₁, d₂, a, h⟩ := hK
  set c : ℝ := 16 * ((s : ℝ) + 1) / 3 with hc
  set F := k ! * (r + 1 + 1 - k)!
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hc6 : (6 : ℝ) ≤ c := by rw [hc]; linarith
  have hcover : (univ : Finset (Equiv.Perm (Fin (r + 1 + 1)))) ⊆
      (K₁.biUnion fun key => passSet key k) ∪
        K₂.biUnion fun G => univ.filter (DPasses G.descr k) := by
    intro π _
    rcases exists_passes_mixed r K₁ hsub K₂ d₁ d₂ a h hk hkN π with
      ⟨key, hkey, hp⟩ | ⟨G, hG, hp⟩
    · refine mem_union_left _ (mem_biUnion.mpr ⟨key, hkey, ?_⟩)
      unfold passSet
      convert Finset.mem_filter.mpr ⟨Finset.mem_univ π, hp⟩
    · exact mem_union_right _ (mem_biUnion.mpr ⟨G, hG, mem_filter.mpr ⟨mem_univ _, hp⟩⟩)
  have h1 := card_le_of_subset hcover
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  have h1' := h1.trans ((card_union_le _ _).trans (add_le_add card_biUnion_le card_biUnion_le))
  have h2 : ((r + 1 + 1)! : ℝ) ≤ ∑ key in K₁, ((passSet key k).card : ℝ) +
      ∑ G in K₂, ((univ.filter (DPasses G.descr k)).card : ℝ) := by
    exact_mod_cast h1'
  have h6c : (6 : ℝ) ^ k ≤ c ^ k := pow_le_pow_left (by norm_num) hc6 _
  have h3 : ∑ key in K₁, ((passSet key k).card : ℝ) ≤ K₁.card * (c ^ k * F) := by
    calc ∑ key in K₁, ((passSet key k).card : ℝ) ≤ ∑ _key in K₁, (c ^ k * F : ℝ) :=
          sum_le_sum fun key hkey => by
            have := card_passSet_le (hsub hkey) hkN
            have : ((passSet key k).card : ℝ) ≤ ((k ! * (r + 1 + 1 - k)! * 6 ^ k : ℕ) : ℝ) := by
              exact_mod_cast this
            push_cast at this ⊢
            have hF0 : (0 : ℝ) ≤ (k ! : ℝ) * ((r + 1 + 1 - k)! : ℝ) := by positivity
            nlinarith
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have h4 : ∑ G in K₂, ((univ.filter (DPasses G.descr k)).card : ℝ) ≤ K₂.card * (c ^ k * F) := by
    calc ∑ G in K₂, ((univ.filter (DPasses G.descr k)).card : ℝ) ≤ ∑ _G in K₂, (c ^ k * F : ℝ) :=
          sum_le_sum fun G hG =>
            card_dpasses_le_of_outLeaf G.descr G.descr_lt G.descr_leaf G.child
              G.descr_child_spec G.descr_child_inj (hs G hG) hkN
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) = ((r + 1 + 1).choose k : ℝ) * F := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]
    push_cast
    ring
  have hpos : (0 : ℝ) < F := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h5 : ((r + 1 + 1).choose k : ℝ) * F ≤ (c ^ k * (K₁.card + K₂.card)) * F := by
    rw [← hfac]
    nlinarith
  exact le_of_mul_le_mul_right h5 hpos

/-- **Exponential count for caterpillars plus trees with few out-leaves** (`s ≥ 1`): with
`c = 16(s+1)/3`, `(c + 1)^N ≤ (N + 1) c^N (|K₁| + |K₂|)` for every `N = r + 2 ≥ 3`. -/
theorem mixed_outLeaf_exponential (r : ℕ) (hr : 1 ≤ r) {K₁ : Finset (FaceKey r)}
    {K₂ : Finset (TreeFace (r + 1 + 1))} (hK : IsMixedExpansion r K₁ K₂) {s : ℕ} (hs1 : 1 ≤ s)
    (hs : ∀ F ∈ K₂, OutLeafBound F.descr s) :
    (16 * ((s : ℝ) + 1) / 3 + 1) ^ (r + 1 + 1) ≤
      ((r + 1 + 1 : ℕ) + 1) * (16 * ((s : ℝ) + 1) / 3) ^ (r + 1 + 1) *
        ((K₁.card : ℝ) + K₂.card) := by
  have hquad := mixed_quadratic r hr hK
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  apply pow_le_of_choose_le (by omega) (by linarith)
  · have : (((r + 1 + 1) * (r + 1) : ℕ) : ℝ) ≤ ((6 * (K₁.card + K₂.card) : ℕ) : ℝ) := by
      exact_mod_cast hquad
    push_cast at this ⊢
    linarith
  · intro m hm3 hmN
    exact mixed_outLeaf_choose_le r hK hs1 hs hm3 hmN

end MaxCaterpillar.Simplify
