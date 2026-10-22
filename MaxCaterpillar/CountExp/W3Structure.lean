import MaxCaterpillar.CountExp.Defs

/-!
# The caterpillar hinge forest of a normalized key, and admissible tie sets

Step 3 of the main route (`research/sN/NOTE.md`): the hinge forest of a normalized key
is a caterpillar hinge forest (`HingeCat`) whose pendant vertices have `κ = 0`
(`exists_hingeCat`).  Step 4: the pass conditions (a) and (s) force the tie set to be
admissible (`HingeCat.admissible_tieSet`), and an admissible tie set is determined by
its spine indices (`HingeCat.eq_of_spineIdx_eq`, `HingeCat.card_spineIdx_le`,
`HingeCat.spineIdx_mem_admissibleIdx`).
-/

open BigOperators Finset

namespace MaxCaterpillar.CountExp

open MaxNN MaxNN.Caterpillar MaxNN.Caterpillar.Corrections MaxNN.ParamidGeom
  MaxNN.ParamidChain CountCubic

/-! ## Admissible tie sets -/

namespace HingeCat

variable {N : ℕ} (H : HingeCat N)

/-- A vertex without neighbours is in the tie set exactly when `κ ≠ 0`. -/
theorem mem_tieSet_iff_of_isolated {adj : Fin N → Fin N → Prop} {κ : Fin N → ℝ} {k : ℕ}
    {π : Equiv.Perm (Fin N)} (hbal : Balanced adj κ k π) (hact : Active adj κ k π)
    {o : Fin N} (hiso : ∀ x, ¬ adj o x) : o ∈ tieSet k π ↔ κ o ≠ 0 := by
  classical
  unfold tieSet
  rw [mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact hact o h (fun x _ => hiso x)
  · intro hne
    refine ⟨mem_univ _, ?_⟩
    by_contra hk
    have hb := hbal o (not_lt.mp hk)
    have h0 : upCount adj π o = 0 := by
      unfold upCount
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro x - ⟨hx, -⟩
      exact hiso x hx
    rw [h0, Nat.cast_zero] at hb
    exact hne hb.symm

theorem onSpine_s {i : ℕ} (hi : i ≤ H.q) : H.OnSpine (H.s i) :=
  ⟨i, mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩

/-- The only neighbour of a pendant vertex is its spine vertex. -/
theorem eq_s_of_adj_pendant (hH : H.WF) {u x : Fin N} {i : ℕ} (hu : H.lp u = some i)
    (hadj : H.Adj u x) : x = H.s i := by
  have hns := hH.lp_not_spine u i hu
  rcases hadj with ⟨i', hi', ⟨he, -⟩ | ⟨he, -⟩⟩ | ⟨i', hi', he⟩ | ⟨i', hi', he⟩
  · have hq := mem_range.mp (hH.links_sub hi')
    rw [he] at hns
    exact absurd (H.onSpine_s (by omega)) hns
  · have hq := mem_range.mp (hH.links_sub hi')
    rw [he] at hns
    exact absurd (H.onSpine_s (by omega)) hns
  · rw [hu] at hi'
    cases hi'
    exact he
  · rw [he] at hns
    exact absurd (H.onSpine_s (hH.lp_le _ _ hi')) hns

/-- Step 4: conditions (a) and (s) force an admissible tie set. -/
theorem admissible_tieSet (hH : H.WF) (κ : Fin N → ℝ)
    (hleaf : ∀ u i, H.lp u = some i → κ u = 0) {k : ℕ} {π : Equiv.Perm (Fin N)}
    (hbal : Balanced H.Adj κ k π) (hact : Active H.Adj κ k π) :
    H.Admissible κ (tieSet k π) := by
  classical
  refine ⟨fun u i hu => ?_, fun i hi hiso => ?_, fun o hns hnone => ?_⟩
  · have hadj : H.Adj u (H.s i) := Or.inr (Or.inl ⟨i, hu, rfl⟩)
    unfold tieSet
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro huT
      by_contra hsT
      refine hact u huT (fun x hx hux => hsT ?_) (hleaf u i hu)
      rw [← H.eq_s_of_adj_pendant hH hu hux]
      exact hx
    · intro hsT
      by_contra huT
      have hb := hbal u (not_lt.mp huT)
      rw [hleaf u i hu] at hb
      have h0 : upCount H.Adj π u = 0 := by exact_mod_cast hb
      unfold upCount at h0
      rw [card_eq_zero, filter_eq_empty_iff] at h0
      exact h0 (mem_univ (H.s i)) ⟨hadj, Fin.lt_iff_val_lt_val.mpr (by omega)⟩
  · refine mem_tieSet_iff_of_isolated hbal hact (fun x hx => ?_)
    obtain ⟨⟨h0, hl⟩, hleafy⟩ := hiso
    rcases hx with ⟨i', hi', ⟨he, -⟩ | ⟨he, -⟩⟩ | ⟨i', hi', -⟩ | ⟨i', hi', he⟩
    · have hq := mem_range.mp (hH.links_sub hi')
      have := hH.s_inj i hi i' (by omega) he
      subst this
      exact hl hi'
    · have hq := mem_range.mp (hH.links_sub hi')
      have := hH.s_inj i hi (i' + 1) (by omega) he
      subst this
      rcases h0 with h0 | h0
      · omega
      · exact h0 (by simpa using hi')
    · exact hH.lp_not_spine _ _ hi' (H.onSpine_s hi)
    · have hle := hH.lp_le _ _ hi'
      have := hH.s_inj i hi i' hle he
      subst this
      exact hleafy (mem_filter.mpr ⟨mem_range.mpr (by omega), x, hi'⟩)
  · refine mem_tieSet_iff_of_isolated hbal hact (fun x hx => ?_)
    rcases hx with ⟨i', hi', ⟨he, -⟩ | ⟨he, -⟩⟩ | ⟨i', hi', -⟩ | ⟨i', hi', he⟩
    · have hq := mem_range.mp (hH.links_sub hi')
      rw [he] at hns
      exact hns (H.onSpine_s (by omega))
    · have hq := mem_range.mp (hH.links_sub hi')
      rw [he] at hns
      exact hns (H.onSpine_s (by omega))
    · rw [hnone] at hi'
      exact Option.noConfusion hi'
    · rw [he] at hns
      exact hns (H.onSpine_s (hH.lp_le _ _ hi'))

theorem mem_spineIdx {T : Finset (Fin N)} {i : ℕ} (hi : i ≤ H.q) :
    i ∈ H.spineIdx T ↔ H.s i ∈ T := by
  unfold spineIdx
  rw [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- An admissible tie set is determined by its spine indices. -/
theorem eq_of_spineIdx_eq (hH : H.WF) {κ : Fin N → ℝ} {T₁ T₂ : Finset (Fin N)}
    (h₁ : H.Admissible κ T₁) (h₂ : H.Admissible κ T₂)
    (he : H.spineIdx T₁ = H.spineIdx T₂) : T₁ = T₂ := by
  have key : ∀ i ≤ H.q, (H.s i ∈ T₁ ↔ H.s i ∈ T₂) := by
    intro i hi
    rw [← H.mem_spineIdx hi, ← H.mem_spineIdx hi, he]
  ext o
  by_cases hs : H.OnSpine o
  · obtain ⟨i, hi, rfl⟩ := hs
    exact key i (Nat.lt_succ_iff.mp (mem_range.mp hi))
  · cases hl : H.lp o with
    | none => rw [h₁.2.2 o hs hl, h₂.2.2 o hs hl]
    | some i =>
      rw [h₁.1 o i hl, h₂.1 o i hl]
      exact key i (hH.lp_le o i hl)

theorem card_spineIdx_le (hH : H.WF) (T : Finset (Fin N)) :
    (H.spineIdx T).card ≤ T.card := by
  refine card_le_card_of_inj_on H.s (fun i hi => (mem_filter.mp hi).2) ?_
  intro i hi j hj h
  have hi' := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp (mem_coe.mp hi)).1)
  have hj' := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp (mem_coe.mp hj)).1)
  exact hH.s_inj i hi' j hj' h

/-- The spine indices of an admissible tie set respect the forced isolated vertices. -/
theorem spineIdx_mem_admissibleIdx (_hH : H.WF) {κ : Fin N → ℝ} {T : Finset (Fin N)}
    (h : H.Admissible κ T) :
    H.spineIdx T ∈ admissibleIdx H.q H.links H.leafy (H.forcedIdx κ) := by
  unfold admissibleIdx
  rw [mem_filter, mem_powerset]
  refine ⟨filter_subset _ _, fun i hi hiso => ?_⟩
  have hi' := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [H.mem_spineIdx hi', h.2.1 i hi' hiso]
  unfold forcedIdx
  rw [mem_filter]
  exact ⟨fun h' => ⟨hi, h'⟩, fun h' => h'.2⟩

end HingeCat

/-! ## The caterpillar hinge forest of a word -/

section WordCat

variable {r : ℕ}

/-- The spine positions of a word. -/
abbrev spP (w : WordIndex r) : Finset (Fin (r + 1)) := insert 0 w.2.1

/-- The spine positions in increasing order. -/
noncomputable abbrev spE (w : WordIndex r) : Fin (spP w).card ≃o spP w :=
  (spP w).orderIsoOfFin rfl

/-- The `i`-th spine label. -/
noncomputable def spS (w : WordIndex r) (i : ℕ) : Fin (r + 1 + 1) :=
  if h : i < (spP w).card then baseV w (spE w ⟨i, h⟩).1 else apexV w

/-- The index of a spine position. -/
noncomputable def spRank (w : WordIndex r) (p : Fin (r + 1)) : ℕ :=
  if h : p ∈ spP w then ((spE w).symm ⟨p, h⟩ : ℕ) else 0

theorem spS_spE (w : WordIndex r) (k : Fin (spP w).card) :
    spS w k = baseV w (spE w k).1 := by
  unfold spS
  rw [dif_pos k.2]

theorem spRank_lt (w : WordIndex r) {p : Fin (r + 1)} (h : p ∈ spP w) :
    spRank w p < (spP w).card := by
  unfold spRank
  rw [dif_pos h]
  exact ((spE w).symm ⟨p, h⟩).2

theorem spS_spRank (w : WordIndex r) {p : Fin (r + 1)} (h : p ∈ spP w) :
    spS w (spRank w p) = baseV w p := by
  have e : spRank w p = (((spE w).symm ⟨p, h⟩ : Fin _) : ℕ) := by
    unfold spRank
    rw [dif_pos h]
  rw [e, spS_spE, OrderIso.apply_symm_apply]

/-- The parent of a spine position is the previous spine position. -/
theorem parent_spE (w : WordIndex r) (k : Fin (spP w).card) (hk : 0 < (k : ℕ)) :
    parent w.2.1 (spE w k).1 = (spE w ⟨k - 1, (Nat.sub_le _ _).trans_lt k.2⟩).1 := by
  set e := spE w
  have hlt : (⟨k - 1, (Nat.sub_le _ _).trans_lt k.2⟩ : Fin (spP w).card) < k := Fin.lt_iff_val_lt_val.mpr (by
    simp only
    omega)
  have hap : (e ⟨k - 1, (Nat.sub_le _ _).trans_lt k.2⟩).1 < (e k).1 := e.lt_iff_lt.mpr hlt
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    have hxP : x ∈ spP w := by
      rcases mem_insert.mp hx with h | h
      · rw [h]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_filter.mp h).1
    by_contra hcon
    have hcon' : e ⟨k - 1, (Nat.sub_le _ _).trans_lt k.2⟩ < e (e.symm ⟨x, hxP⟩) := by
      rw [OrderIso.apply_symm_apply]
      exact not_le.mp hcon
    have hb := e.lt_iff_lt.mp hcon'
    have hkb : k ≤ e.symm ⟨x, hxP⟩ := by
      rw [Fin.lt_iff_val_lt_val] at hb
      rw [Fin.le_iff_val_le_val]
      simp only at hb
      omega
    have hpx : (e k).1 ≤ x := by
      have := e.monotone hkb
      rw [OrderIso.apply_symm_apply] at this
      exact this
    rcases mem_insert.mp hx with h | h
    · rw [h] at hpx
      exact absurd (lt_of_lt_of_le hap hpx) (not_lt.mpr (Fin.zero_le _))
    · exact absurd (mem_filter.mp h).2 (not_lt.mpr hpx)
  · apply Finset.le_max'
    have hm := (e ⟨k - 1, (Nat.sub_le _ _).trans_lt k.2⟩).2
    rcases mem_insert.mp hm with h | h
    · rw [h]
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨h, hap⟩)

/-- The caterpillar hinge forest of the word `w` with face state `τ`. -/
noncomputable def wordCat (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    HingeCat (r + 1 + 1) := by
  classical
  exact
  { q := (spP w).card - 1
    s := spS w
    links := (range ((spP w).card - 1)).filter fun i =>
      ∃ j, edgeState w τ j = 2 ∧ parV w j = spS w i ∧ childV w j = spS w (i + 1)
    lp := fun u => if h : ∃ j, j.succ ∉ w.2.1 ∧ edgeState w τ j = 2 ∧ childV w j = u
      then some (spRank w (parent w.2.1 (Classical.choose h).succ)) else none }

theorem wordCat_q (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    (wordCat w τ).q = (spP w).card - 1 := rfl

theorem wordCat_s (w : WordIndex r) (τ : wordLabels w → Fin 3) :
    (wordCat w τ).s = spS w := rfl

theorem mem_wordCat_links (w : WordIndex r) (τ : wordLabels w → Fin 3) (i : ℕ) :
    i ∈ (wordCat w τ).links ↔ i < (spP w).card - 1 ∧
      ∃ j, edgeState w τ j = 2 ∧ parV w j = spS w i ∧ childV w j = spS w (i + 1) := by
  unfold wordCat
  simp only [mem_filter, mem_range]

theorem wordCat_lp_eq_some (w : WordIndex r) (τ : wordLabels w → Fin 3) {u : Fin (r + 1 + 1)}
    {i : ℕ} (h : (wordCat w τ).lp u = some i) :
    ∃ j, j.succ ∉ w.2.1 ∧ edgeState w τ j = 2 ∧ childV w j = u ∧ spS w i = parV w j ∧
      i < (spP w).card := by
  classical
  unfold wordCat at h
  simp only at h
  split_ifs at h with hex
  cases h
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hex
  refine ⟨Classical.choose hex, h1, h2, h3, ?_, spRank_lt w (parent_mem_insert _ _)⟩
  rw [spS_spRank w (parent_mem_insert _ _)]
  rfl

theorem wordCat_lp_pendant (w : WordIndex r) (τ : wordLabels w → Fin 3) {j : Fin r}
    (hj : j.succ ∉ w.2.1) (hst : edgeState w τ j = 2) :
    ∃ i, (wordCat w τ).lp (childV w j) = some i ∧ spS w i = parV w j := by
  classical
  have hex : ∃ j', j'.succ ∉ w.2.1 ∧ edgeState w τ j' = 2 ∧ childV w j' = childV w j :=
    ⟨j, hj, hst, rfl⟩
  have hc : Classical.choose hex = j := childV_injective w (Classical.choose_spec hex).2.2
  refine ⟨spRank w (parent w.2.1 j.succ), ?_, ?_⟩
  · unfold wordCat
    simp only
    rw [dif_pos hex, hc]
  · rw [spS_spRank w (parent_mem_insert _ _)]
    rfl

theorem wordCat_wf (w : WordIndex r) (τ : wordLabels w → Fin 3) : (wordCat w τ).WF := by
  have hpos : 0 < (spP w).card := card_pos.mpr (insert_nonempty _ _)
  refine ⟨fun i hi j hj he => ?_, fun i hi => ?_, fun u i hu => ?_, fun u i hu hs => ?_⟩
  · rw [wordCat_q] at hi hj
    rw [wordCat_s] at he
    have hi' : i < (spP w).card := by omega
    have hj' : j < (spP w).card := by omega
    have e1 := spS_spE w ⟨i, hi'⟩
    have e2 := spS_spE w ⟨j, hj'⟩
    simp only at e1 e2
    rw [e1, e2] at he
    have := (spE w).injective (Subtype.ext (baseV_injective w he))
    exact congrArg Fin.val this
  · rw [mem_wordCat_links] at hi
    rw [mem_range, wordCat_q]
    exact hi.1
  · obtain ⟨-, -, -, -, -, hlt⟩ := wordCat_lp_eq_some w τ hu
    rw [wordCat_q]
    omega
  · obtain ⟨j, hj, -, rfl, -, -⟩ := wordCat_lp_eq_some w τ hu
    obtain ⟨i', hi', he⟩ := hs
    rw [mem_range, wordCat_q] at hi'
    rw [wordCat_s] at he
    have hlt : i' < (spP w).card := by omega
    have e1 := spS_spE w ⟨i', hlt⟩
    simp only at e1
    rw [e1] at he
    exact childV_not_mem_spineV w hj (he ▸ mem_image.mpr ⟨_, (spE w ⟨i', hlt⟩).2, rfl⟩)

/-- Hinge neighbours of a word face key are the ends of its hinge edges. -/
theorem hingeNbr_wordFaceKey_iff (w : WordIndex r) (τ : wordLabels w → Fin 3)
    (u v : Fin (r + 1 + 1)) :
    HingeNbr (wordFaceKey w τ) u v ↔ ∃ j, edgeState w τ j = 2 ∧
      ((parV w j = u ∧ childV w j = v) ∨ (childV w j = u ∧ parV w j = v)) := by
  refine ⟨hingeNbr_wordFaceKey w τ, ?_⟩
  rintro ⟨j, hst, h⟩
  have hlh : (lowV w j = parV w j ∧ highV w j = childV w j) ∨
      (lowV w j = childV w j ∧ highV w j = parV w j) := by
    unfold lowV highV
    rcases le_total (parV w j) (childV w j) with h | h
    · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
    · exact Or.inr ⟨min_eq_right h, max_eq_left h⟩
  unfold HingeNbr
  simp only [hasPair_wordFaceKey_iff]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hlh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨j, hst, h1, h2⟩
  · exact Or.inr ⟨j, hst, h1, h2⟩
  · exact Or.inr ⟨j, hst, h1, h2⟩
  · exact Or.inl ⟨j, hst, h1, h2⟩

theorem wordCat_adj_iff (w : WordIndex r) (τ : wordLabels w → Fin 3) (u v : Fin (r + 1 + 1)) :
    (wordCat w τ).Adj u v ↔ ∃ j, edgeState w τ j = 2 ∧
      ((parV w j = u ∧ childV w j = v) ∨ (childV w j = u ∧ parV w j = v)) := by
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hu⟩)
    · rw [mem_wordCat_links] at hi
      obtain ⟨-, j, hst, hp, hc⟩ := hi
      rw [wordCat_s] at h
      refine ⟨j, hst, ?_⟩
      rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact Or.inl ⟨hp.trans hu.symm, hc.trans hv.symm⟩
      · exact Or.inr ⟨hc.trans hu.symm, hp.trans hv.symm⟩
    · obtain ⟨j, -, hst, hc, hs, -⟩ := wordCat_lp_eq_some w τ hi
      rw [wordCat_s] at hv
      exact ⟨j, hst, Or.inr ⟨hc, hs.symm.trans hv.symm⟩⟩
    · obtain ⟨j, -, hst, hc, hs, -⟩ := wordCat_lp_eq_some w τ hi
      rw [wordCat_s] at hu
      exact ⟨j, hst, Or.inl ⟨hs.symm.trans hu.symm, hc⟩⟩
  · rintro ⟨j, hst, h⟩
    by_cases hj : j.succ ∈ w.2.1
    · have hpP : j.succ ∈ spP w := mem_insert_of_mem hj
      obtain ⟨k, hek⟩ : ∃ k : Fin (spP w).card, ((spE w) k).1 = j.succ :=
        ⟨(spE w).symm ⟨j.succ, hpP⟩, by rw [OrderIso.apply_symm_apply]⟩
      have hk : 0 < (k : ℕ) := by
        by_contra hk0
        have h0P : (0 : Fin (r + 1)) ∈ spP w := mem_insert_self _ _
        have hle : k ≤ (spE w).symm ⟨0, h0P⟩ := by
          rw [Fin.le_iff_val_le_val]
          omega
        have := (spE w).monotone hle
        rw [OrderIso.apply_symm_apply] at this
        have h' : ((spE w) k).1 ≤ 0 := this
        rw [hek] at h'
        exact Fin.succ_ne_zero j (le_antisymm h' (Fin.zero_le _))
      have hpar := parent_spE w k hk
      rw [hek] at hpar
      have hsp : spS w (k - 1) = parV w j := by
        have := spS_spE w ⟨k - 1, (Nat.sub_le _ _).trans_lt k.2⟩
        simp only at this
        rw [this, ← hpar]
        rfl
      have hsc : spS w (k - 1 + 1) = childV w j := by
        have e : k - 1 + 1 = (k : ℕ) := by omega
        rw [e, spS_spE, hek]
        rfl
      have hlink : (k : ℕ) - 1 ∈ (wordCat w τ).links := by
        rw [mem_wordCat_links]
        exact ⟨Nat.pred_lt_pred (Nat.pos_iff_ne_zero.mp hk) k.2, j, hst, hsp.symm, hsc.symm⟩
      refine Or.inl ⟨(k : ℕ) - 1, hlink, ?_⟩
      rw [wordCat_s, hsp, hsc]
      rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact Or.inl ⟨hu.symm, hv.symm⟩
      · exact Or.inr ⟨hu.symm, hv.symm⟩
    · obtain ⟨i, hi, hs⟩ := wordCat_lp_pendant w τ hj hst
      rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [hv] at hi
        exact Or.inr (Or.inr ⟨i, hi, hu.symm.trans hs.symm⟩)
      · rw [hu] at hi
        exact Or.inr (Or.inl ⟨i, hi, hv.symm.trans hs.symm⟩)

end WordCat

/-- Step 3: the hinge forest of a normalized key is a caterpillar hinge forest
whose pendant vertices have `κ = 0`. -/
theorem exists_hingeCat {r : ℕ} {key : RealKey (r + 1)} (hkey : key ∈ normalizedKeys r) :
    ∃ H : HingeCat (r + 1 + 1), H.WF ∧ (∀ u v, HingeNbr key u v ↔ H.Adj u v) ∧
      ∀ u i, H.lp u = some i → kappa key u = 0 := by
  obtain ⟨w, τ, rfl⟩ := exists_word_of_mem_normalizedKeys hkey
  refine ⟨wordCat w τ, wordCat_wf w τ, fun u v => ?_, fun u i hu => ?_⟩
  · rw [hingeNbr_wordFaceKey_iff, wordCat_adj_iff]
  · obtain ⟨j, hj, hst, rfl, -, -⟩ := wordCat_lp_eq_some w τ hu
    rw [kappa_pendant_wordFaceKey w τ j hj, hst]
    rfl

end MaxCaterpillar.CountExp
