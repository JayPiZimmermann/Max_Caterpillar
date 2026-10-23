import MaxCaterpillar.Trees.BoundedDegree

/-!
# Exponential count for trees of bounded hinge degree: assembly

For every `3 ≤ k ≤ N`, every locality is passed by some unit of an expansion
(the mixed difference argument for general descriptions, `DescrPass`), and every unit
whose hinge forest has maximum degree `≤ Δ` passes at most
`2 (6(2Δ-1))^k k! (N-k)!` localities (`card_passes_le`).  Hence
`C(N, k) ≤ 2 (12Δ - 6)^k |K|`.
-/

open BigOperators Finset
open scoped Nat

namespace MaxCaterpillar.Trees

open MaxNN CountLower CountExp

/-! ## Every locality is passed by some unit -/

theorem exists_dpasses (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∃ i ∈ K, DPasses (D i) k π := by
  classical
  set c : ι → ℝ := fun i => ∑ o, |((D i).h o : ℝ)| + 2 * ((D i).M.card : ℝ) with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i =>
    add_nonneg (Finset.sum_nonneg fun o _ => abs_nonneg _)
      (mul_nonneg zero_le_two (Nat.cast_nonneg _))
  set C : ℝ := ∑ i in K, c i
  have hcC : ∀ i ∈ K, c i ≤ C := fun i hi => Finset.single_le_sum (fun i _ => hc0 i) hi
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => hc0 i
  set δ : ℝ := 1 / (C + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set B : ℕ := ⌈C⌉₊ + 1 with hB
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have hCB : C < B := by
    rw [hB]
    push_cast
    exact lt_of_le_of_lt (Nat.le_ceil C) (lt_add_one _)
  have hfun : Maximum (r + 1 + 1) = (∑ i in K, d i • (D i).unit) + auxiliary a := by
    funext x
    rw [h x, Pi.add_apply, Finset.sum_apply]
    rfl
  have hval := congrArg (mixedDiff k B δ π) hfun
  rw [mixedDiff_maximum (le_trans (by norm_num) hk) hkN hB1 hδ0.le, map_add,
    mixedDiff_auxiliary hk hkN B δ π a, add_zero, map_sum] at hval
  have hne : ∑ i in K, mixedDiff k B δ π (d i • (D i).unit) ≠ 0 := by
    rw [← hval]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hδ0.ne'
  obtain ⟨i, hi, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [map_smul, smul_eq_mul] at hi0
  have hU : mixedDiff k B δ π (D i).unit ≠ 0 := right_ne_zero_of_mul hi0
  have hδb : δ * c i < 1 := by
    calc δ * c i ≤ δ * C := mul_le_mul_of_nonneg_left (hcC i hi) hδ0.le
      _ < δ * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hδ0
      _ = 1 := by rw [hδ, one_div, inv_mul_cancel (by linarith)]
  obtain ⟨h0, hact⟩ := descr_pass_of_mixedDiff_ne (D i) hk hkN hB1 hδ0 hδb π hU
  have hBk : ∑ o, |((D i).h o : ℝ)| + ((D i).M.card : ℝ) < B := by
    have : ∑ o, |((D i).h o : ℝ)| + ((D i).M.card : ℝ) ≤ c i := by
      simp only [hc]
      have : (0 : ℝ) ≤ ((D i).M.card : ℝ) := Nat.cast_nonneg _
      linarith
    linarith [hcC i hi]
  exact ⟨i, hi, descr_balanced_of_arg_eq_zero (D i) (hlt i hi) hBk π h0, hact⟩

/-- **Binomial count for bounded hinge degree (descriptions).** -/
theorem choose_le_of_bounded (r : ℕ) {ι : Type*} (K : Finset ι) (D : ι → Descr (r + 1 + 1))
    {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hlt : ∀ i ∈ K, ∀ m ∈ (D i).M, m.1 < m.2) (hleaf : ∀ i ∈ K, LeafProp (D i).M)
    (hdeg : ∀ i ∈ K, ∀ o, (incid (D i).M o).card ≤ Δ)
    (d : ι → ℝ) (a : Fin (Width.W (r + 1 + 1)) → ℝ)
    (h : ∀ x, Maximum (r + 1 + 1) x = ∑ i in K, d i * (D i).unit x + auxiliary a x)
    {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ 2 * (6 * (2 * Δ - 1 : ℕ)) ^ k * K.card := by
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
      K.card * (2 * (6 * (2 * Δ - 1 : ℕ)) ^ k * (k ! * (r + 1 + 1 - k)! : ℕ)) := by
    calc ∑ i in K, ((univ.filter (DPasses (D i) k)).card : ℝ)
        ≤ ∑ _i in K, (2 * (6 * (2 * Δ - 1 : ℕ)) ^ k * (k ! * (r + 1 + 1 - k)! : ℕ) : ℝ) :=
          sum_le_sum fun i hi =>
            card_passes_le (D i) (hlt i hi) (hleaf i hi) hΔ (hdeg i hi) hkN
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hfac : ((r + 1 + 1)! : ℝ) = ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hkN]
    push_cast
    ring
  have hpos : (0 : ℝ) < (k ! * (r + 1 + 1 - k)! : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have h4 := h2.trans h3
  rw [hfac] at h4
  have h5 : ((r + 1 + 1).choose k : ℝ) * (k ! * (r + 1 + 1 - k)! : ℕ) ≤
      (2 * (6 * (2 * Δ - 1 : ℕ)) ^ k * K.card) * (k ! * (r + 1 + 1 - k)! : ℕ) := by
    linarith
  exact le_of_mul_le_mul_right h5 hpos

/-! ## Tree faces -/

namespace TreeFace

variable {N : ℕ} (F : TreeFace N)

/-- The hinge degree of `u`: the number of hinge edges of the tree at `u`. -/
noncomputable def hingeDeg (u : Fin N) : ℕ := by
  classical
  exact (F.edgeVerts.filter fun v => F.state v = .hinge ∧ (v = u ∨ F.parent v = u)).card

theorem normPair_mem (p : Fin N × Fin N) (u : Fin N) :
    ((normPair p).1 = u ∨ (normPair p).2 = u) ↔ (p.1 = u ∨ p.2 = u) := by
  unfold normPair
  split_ifs <;> simp only <;> tauto

theorem gen_mem (v u : Fin N) :
    ((F.gen v).1 = u ∨ (F.gen v).2 = u) ↔ (v = u ∨ F.parent v = u) := by
  unfold gen
  split_ifs <;> simp only <;> tauto

theorem incid_descr_le (u : Fin N) : (incid F.descr.M u).card ≤ F.hingeDeg u := by
  classical
  unfold hingeDeg incid
  have hsub : F.descr.M.filter (fun m => m.1 = u ∨ m.2 = u) ⊆
      (F.edgeVerts.filter fun v => F.state v = .hinge ∧ (v = u ∨ F.parent v = u)).image
        fun v => normPair (F.gen v) := by
    intro m hm
    obtain ⟨hmM, hmu⟩ := mem_filter.mp hm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hmM
    obtain ⟨hv1, hv2⟩ := mem_filter.mp hv
    refine mem_image.mpr ⟨v, mem_filter.mpr ⟨hv1, hv2, ?_⟩, rfl⟩
    exact (F.gen_mem v u).mp ((normPair_mem _ u).mp hmu)
  convert (card_le_of_subset hsub).trans card_image_le

theorem descr_lt : ∀ m ∈ F.descr.M, m.1 < m.2 := by
  intro m hm
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hm
  have hne := F.gen_ne (mem_filter.mp hv).1
  unfold normPair
  split_ifs with h
  · exact h
  · rcases lt_trichotomy (F.gen v).1 (F.gen v).2 with h' | h' | h'
    · exact absurd h' h
    · exact absurd h' hne
    · exact h'

theorem descr_leaf : LeafProp F.descr.M := by
  classical
  intro E hE hne
  set V := (F.edgeVerts.filter fun v => F.state v = .hinge).filter
    fun v => normPair (F.gen v) ∈ E
  have hVne : V.Nonempty := by
    obtain ⟨m, hm⟩ := hne
    obtain ⟨v, hv, rfl⟩ := mem_image.mp (hE hm)
    exact ⟨v, mem_filter.mpr ⟨hv, hm⟩⟩
  obtain ⟨v, hvV, hmax⟩ := exists_max_image V F.depth hVne
  obtain ⟨hv, hvE⟩ := mem_filter.mp hvV
  have hvEV := (mem_filter.mp hv).1
  refine ⟨normPair (F.gen v), hvE, v, ?_, ?_⟩
  · have := (normPair_mem (F.gen v) v).mpr ((F.gen_mem v v).mpr (Or.inl rfl))
    rcases this with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · intro m' hm' hm'u
    obtain ⟨v', hv', rfl⟩ := mem_image.mp (hE hm')
    have hv'V : v' ∈ V := mem_filter.mpr ⟨hv', hm'⟩
    have hv'E := (mem_filter.mp hv').1
    have hrel := (F.gen_mem v' v).mp ((normPair_mem _ v).mp hm'u)
    rcases hrel with h | h
    · rw [h]
    · exfalso
      have hv'm := (F.mem_edgeVerts).mp hv'E
      have hd := F.depth_lt v' hv'm.2 hv'm.1
      rw [h] at hd
      have := hmax v' hv'V
      omega

end TreeFace

/-! ## Public statements -/

/-- **Binomial count for trees of bounded hinge degree.** If every unit of a tree
expansion of `max_N` (`N = r + 2`) has hinge degree at most `Δ ≥ 1` at every vertex, then
`C(N, k) ≤ 2 (12Δ - 6)^k |K|` for `3 ≤ k ≤ N`. -/
theorem tree_bounded_choose_le (r : ℕ) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdeg : ∀ F ∈ K, ∀ u, F.hingeDeg u ≤ Δ) {k : ℕ} (hk : 3 ≤ k) (hkN : k ≤ r + 1 + 1) :
    ((r + 1 + 1).choose k : ℝ) ≤ 2 * (6 * (2 * Δ - 1 : ℕ)) ^ k * K.card := by
  obtain ⟨d, a, h⟩ := hK
  have h' : ∀ x, Maximum (r + 1 + 1) x = ∑ F in K, d F * F.descr.unit x + auxiliary a x := by
    intro x
    rw [h x]
    congr 1
    exact sum_congr rfl fun F _ => by rw [TreeFace.descr_unit]
  exact choose_le_of_bounded r K (fun F => F.descr) hΔ (fun F _ => F.descr_lt)
    (fun F _ => F.descr_leaf) (fun F hF u => (F.incid_descr_le u).trans (hdeg F hF u))
    d a h' hk hkN

/-- **Exponential count for trees of bounded hinge degree.** With `c = 6(2Δ - 1)`,
`(c + 1)^N ≤ 2 (N + 1) c^N |K|` for `N = r + 2 ≥ 3`; i.e.
`|K| ≥ (1 + 1/(12Δ - 6))^N / (2(N + 1))`. -/
theorem tree_bounded_exponential (r : ℕ) (hr : 1 ≤ r) {K : Finset (TreeFace (r + 1 + 1))}
    (hK : IsTreeExpansion r K) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hdeg : ∀ F ∈ K, ∀ u, F.hingeDeg u ≤ Δ) :
    ((6 * (2 * Δ - 1) + 1 : ℕ) : ℝ) ^ (r + 1 + 1) ≤
      2 * (r + 1 + 1 + 1) * ((6 * (2 * Δ - 1) : ℕ) : ℝ) ^ (r + 1 + 1) * K.card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = 6 * (2 * Δ - 1) := ⟨_, rfl⟩
  rw [← hc]
  have hc6 : 6 ≤ c := by omega
  have hc6r : (6 : ℝ) ≤ c := by exact_mod_cast hc6
  have hcpos : (0 : ℝ) < c := by linarith
  have hquad := tree_expansion_quadratic r hr hK
  have h6 : 6 ≤ (r + 1 + 1) * (r + 1) := by nlinarith
  have hK1n : 1 ≤ K.card := by omega
  have hK1 : (1 : ℝ) ≤ K.card := by exact_mod_cast hK1n
  have hNK : ((r + 1 + 1 : ℕ) : ℝ) ≤ 6 * K.card := by
    have : r + 1 + 1 ≤ 6 * K.card := le_trans (Nat.le_mul_of_pos_right (by omega)) hquad
    exact_mod_cast this
  have hN2K : (((r + 1 + 1).choose 2 : ℕ) : ℝ) ≤ 3 * K.card := by
    have : (r + 1 + 1).choose 2 ≤ 3 * K.card := by
      rw [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      calc (r + 1 + 1) * (r + 1 + 1 - 1) = (r + 1 + 1) * (r + 1) := rfl
        _ ≤ 6 * K.card := hquad
        _ = 2 * (3 * K.card) := by ring
    exact_mod_cast this
  have hterm : ∀ m ≤ r + 1 + 1, ((r + 1 + 1).choose m : ℝ) * (c : ℝ) ^ (r + 1 + 1 - m) ≤
      2 * (c : ℝ) ^ (r + 1 + 1) * K.card := by
    intro m hm
    have hcm : (c : ℝ) ^ (r + 1 + 1 - m) * (c : ℝ) ^ m = (c : ℝ) ^ (r + 1 + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hm]
    have hp := pow_pos hcpos (r + 1 + 1 - m)
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · rw [Nat.choose_zero_right, Nat.sub_zero]
        push_cast
        nlinarith [pow_pos hcpos (r + 1 + 1)]
      · rw [Nat.choose_one_right]
        rw [pow_one] at hcm
        have : ((r + 1 + 1 : ℕ) : ℝ) * (c : ℝ) ^ (r + 1 + 1 - 1) ≤
            (c * K.card) * (c : ℝ) ^ (r + 1 + 1 - 1) := by
          apply mul_le_mul_of_nonneg_right _ hp.le
          nlinarith
        nlinarith
      · have : (((r + 1 + 1).choose 2 : ℕ) : ℝ) * (c : ℝ) ^ (r + 1 + 1 - 2) ≤
            (c ^ 2 * K.card) * (c : ℝ) ^ (r + 1 + 1 - 2) := by
          apply mul_le_mul_of_nonneg_right _ hp.le
          calc (((r + 1 + 1).choose 2 : ℕ) : ℝ) ≤ 3 * K.card := hN2K
            _ ≤ c ^ 2 * K.card :=
              mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        nlinarith
    · have hb := tree_bounded_choose_le r hK hΔ hdeg hm3 hm
      have hcr : ((c : ℕ) : ℝ) = 6 * ((2 * Δ - 1 : ℕ) : ℝ) := by rw [hc]; push_cast; ring
      rw [← hcr] at hb
      calc ((r + 1 + 1).choose m : ℝ) * (c : ℝ) ^ (r + 1 + 1 - m)
          ≤ (2 * (c : ℝ) ^ m * K.card) * (c : ℝ) ^ (r + 1 + 1 - m) :=
            mul_le_mul_of_nonneg_right hb hp.le
        _ = 2 * ((c : ℝ) ^ (r + 1 + 1 - m) * (c : ℝ) ^ m) * K.card := by ring
        _ = 2 * (c : ℝ) ^ (r + 1 + 1) * K.card := by rw [hcm]
  have hbin : ((c + 1 : ℕ) : ℝ) ^ (r + 1 + 1) =
      ∑ m in range (r + 1 + 1 + 1), ((r + 1 + 1).choose m : ℝ) * (c : ℝ) ^ (r + 1 + 1 - m) := by
    push_cast
    rw [add_comm, add_pow]
    refine sum_congr rfl fun m _ => ?_
    ring
  rw [hbin]
  calc ∑ m in range (r + 1 + 1 + 1), ((r + 1 + 1).choose m : ℝ) * (c : ℝ) ^ (r + 1 + 1 - m)
      ≤ ∑ _m in range (r + 1 + 1 + 1), 2 * (c : ℝ) ^ (r + 1 + 1) * K.card :=
        sum_le_sum fun m hm => hterm m (Nat.lt_succ_iff.mp (mem_range.mp hm))
    _ = 2 * (r + 1 + 1 + 1) * (c : ℝ) ^ (r + 1 + 1) * K.card := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

end MaxCaterpillar.Trees
