import MaxNN.Constructions.Paramid.Caterpillar.Block.Index
import MaxNN.Constructions.Paramid.Caterpillar.Words.Adjacent

/-! # The block-fibre involution on actual formula indices -/

namespace MaxNN.Caterpillar

variable {r : ℕ}

def nextIndex (j : Fin r) (h : j.succ.val < r) : Fin r := ⟨j.val + 1, h⟩

@[simp] theorem nextIndex_castSucc (j : Fin r) (h : j.succ.val < r) :
    (nextIndex j h).castSucc = j.succ := rfl

def liftedAdjacentSwap (k : Fin r) : Equiv.Perm (Fin (r + 1 + 1)) :=
  Equiv.swap k.castSucc.succ k.succ.succ

theorem liftedAdjacentSwap_zero (k : Fin r) : liftedAdjacentSwap k 0 = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.succ_ne_zero _).symm
  · exact (Fin.succ_ne_zero _).symm

theorem liftedAdjacentSwap_succ (k : Fin r) (i : Fin (r + 1)) :
    liftedAdjacentSwap k i.succ = (adjacentSwap k i).succ := by
  unfold liftedAdjacentSwap adjacentSwap
  by_cases hia : i = k.castSucc
  · subst i
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hib : i = k.succ
    · subst i
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun he => hia (Fin.succ_injective _ he))
          (fun he => hib (Fin.succ_injective _ he)),
        Equiv.swap_apply_of_ne_of_ne hia hib]

def suffixPerm (k : Fin r) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    Equiv.Perm (Fin (r + 1 + 1)) :=
  (liftedAdjacentSwap k).trans π

theorem suffixPerm_zero (k : Fin r) (π : Equiv.Perm (Fin (r + 1 + 1))) :
    suffixPerm k π 0 = π 0 := by
  rw [suffixPerm, Equiv.trans_apply, liftedAdjacentSwap_zero]

theorem suffixPerm_succ (k : Fin r) (π : Equiv.Perm (Fin (r + 1 + 1)))
    (i : Fin (r + 1)) :
    suffixPerm k π i.succ = π (adjacentSwap k i).succ := by
  rw [suffixPerm, Equiv.trans_apply, liftedAdjacentSwap_succ]

theorem suffixPerm_involutive (k : Fin r) : Function.Involutive (suffixPerm k) := by
  intro π
  ext i
  simp [suffixPerm, liftedAdjacentSwap]

theorem SplitValues.next_swap_invariant {w : Fin (r + 1) → ℝ} {j : Fin r}
    (hsplit : SplitValues w j) (hsize : j.succ.val < r) :
    ∀ i, w (adjacentSwap (nextIndex j hsize) i) = w i := by
  intro i
  let k := nextIndex j hsize
  have hka : k.castSucc = j.succ := nextIndex_castSucc j hsize
  have hab : k.castSucc < k.succ := Fin.castSucc_lt_succ k
  have hwa : w k.castSucc = w j.succ := by rw [hka]
  have hwb : w k.succ = w j.succ := by
    rw [hsplit.2 k.succ, if_neg]
    exact not_lt.mpr (le_trans (le_of_eq hka.symm) (le_of_lt hab))
  change w (adjacentSwap k i) = w i
  unfold adjacentSwap
  by_cases hia : i = k.castSucc
  · subst i
    rw [Equiv.swap_apply_left, hwa, hwb]
  · by_cases hib : i = k.succ
    · subst i
      rw [Equiv.swap_apply_right, hwa, hwb]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

noncomputable def prefixPairAt (q : BlockIndex r) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc) (hb : j.succ ∈ q.2.1) : BlockIndex r :=
  (q.1, ⟨toggleCut j.castSucc q.2.1,
    toggleCut_mem_admissible q.2.2 (ne_of_gt ha0) hb
      (ne_of_gt (Fin.castSucc_lt_succ j))⟩)

noncomputable def suffixPairAt (q : BlockIndex r) (j : Fin r)
    (hsize : j.succ.val < r) (ha : j.succ ∈ q.2.1) : BlockIndex r :=
  let k := nextIndex j hsize
  (suffixPerm k q.1, ⟨toggleCut k.succ q.2.1,
    toggleCut_mem_admissible q.2.2 (Fin.succ_ne_zero k) ha
      (ne_of_lt (Fin.castSucc_lt_succ k))⟩)

@[simp] theorem prefixPairAt_perm (q : BlockIndex r) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc) (hb : j.succ ∈ q.2.1) :
    (prefixPairAt q j ha0 hb).1 = q.1 := rfl

@[simp] theorem prefixPairAt_cuts (q : BlockIndex r) (j : Fin r)
    (ha0 : (0 : Fin (r + 1)) < j.castSucc) (hb : j.succ ∈ q.2.1) :
    (prefixPairAt q j ha0 hb).2.1 = toggleCut j.castSucc q.2.1 := rfl

@[simp] theorem suffixPairAt_perm (q : BlockIndex r) (j : Fin r)
    (hsize : j.succ.val < r) (ha : j.succ ∈ q.2.1) :
    (suffixPairAt q j hsize ha).1 = suffixPerm (nextIndex j hsize) q.1 := rfl

@[simp] theorem suffixPairAt_cuts (q : BlockIndex r) (j : Fin r)
    (hsize : j.succ.val < r) (ha : j.succ ∈ q.2.1) :
    (suffixPairAt q j hsize ha).2.1 = toggleCut (nextIndex j hsize).succ q.2.1 := rfl

theorem blockWordValues_prefixPairAt (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (j : Fin r) (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (hb : j.succ ∈ q.2.1) :
    blockWordValues x (prefixPairAt q j ha0 hb) = blockWordValues x q := rfl

theorem blockApexValue_prefixPairAt (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (j : Fin r) (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (hb : j.succ ∈ q.2.1) :
    blockApexValue x (prefixPairAt q j ha0 hb) = blockApexValue x q := rfl

theorem blockWordValues_suffixPairAt (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (j : Fin r) (hsize : j.succ.val < r)
    (ha : j.succ ∈ q.2.1) (hsplit : SplitValues (blockWordValues x q) j) :
    blockWordValues x (suffixPairAt q j hsize ha) = blockWordValues x q := by
  funext i
  change x (suffixPerm (nextIndex j hsize) q.1 i.succ) = x (q.1 i.succ)
  rw [suffixPerm_succ]
  exact hsplit.next_swap_invariant hsize i

theorem blockApexValue_suffixPairAt (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (j : Fin r) (hsize : j.succ.val < r)
    (ha : j.succ ∈ q.2.1) :
    blockApexValue x (suffixPairAt q j hsize ha) = blockApexValue x q := by
  change x (suffixPerm (nextIndex j hsize) q.1 0) = x (q.1 0)
  rw [suffixPerm_zero]

theorem activePrefix_prefixPairAt (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (j : Fin r) (ha0 : (0 : Fin (r + 1)) < j.castSucc)
    (hb : j.succ ∈ q.2.1) (hsplit : SplitValues (blockWordValues x q) j)
    (hapex : blockApexValue x q = blockWordValues x q j.succ) :
    ActivePrefix x (prefixPairAt q j ha0 hb) := by
  refine ⟨j, ha0, ?_, ?_, ?_⟩
  · exact (mem_toggleCut_of_ne (ne_of_gt (Fin.castSucc_lt_succ j))).mpr hb
  · rwa [blockWordValues_prefixPairAt]
  · rwa [blockApexValue_prefixPairAt, blockWordValues_prefixPairAt]

theorem activeSuffix_suffixPairAt (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (j : Fin r) (hsize : j.succ.val < r)
    (ha : j.succ ∈ q.2.1) (hsplit : SplitValues (blockWordValues x q) j)
    (hapex : blockApexValue x q = blockWordValues x q 0) :
    ActiveSuffix x (suffixPairAt q j hsize ha) := by
  refine ⟨j, hsize, ?_, ?_, ?_⟩
  · change (nextIndex j hsize).castSucc ∈
      toggleCut (nextIndex j hsize).succ q.2.1
    exact (mem_toggleCut_of_ne (ne_of_lt (Fin.castSucc_lt_succ _))).mpr ha
  · rwa [blockWordValues_suffixPairAt x q j hsize ha hsplit]
  · rw [blockApexValue_suffixPairAt]
    rwa [blockWordValues_suffixPairAt x q j hsize ha hsplit]

noncomputable def blockTransform (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r) :
    BlockIndex r := by
  classical
  exact if hp : ActivePrefix x q then
      prefixPairAt q (Classical.choose hp) (Classical.choose_spec hp).1
        (Classical.choose_spec hp).2.1
    else if hs : ActiveSuffix x q then
      suffixPairAt q (Classical.choose hs) (Classical.choose_spec hs).1
        (Classical.choose_spec hs).2.1
    else q

theorem blockTransform_eq_prefix (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r)
    (j : Fin r) (ha0 : (0 : Fin (r + 1)) < j.castSucc) (hb : j.succ ∈ q.2.1)
    (hsplit : SplitValues (blockWordValues x q) j)
    (hapex : blockApexValue x q = blockWordValues x q j.succ) :
    blockTransform x q = prefixPairAt q j ha0 hb := by
  have hp : ActivePrefix x q := ⟨j, ha0, hb, hsplit, hapex⟩
  rw [blockTransform, dif_pos hp]
  have hj : Classical.choose hp = j :=
    (Classical.choose_spec hp).2.2.1.unique hsplit
  subst j
  rfl

theorem blockTransform_eq_suffix (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r)
    (j : Fin r) (hsize : j.succ.val < r) (ha : j.succ ∈ q.2.1)
    (hsplit : SplitValues (blockWordValues x q) j)
    (hapex : blockApexValue x q = blockWordValues x q 0) :
    blockTransform x q = suffixPairAt q j hsize ha := by
  have hs : ActiveSuffix x q := ⟨j, hsize, ha, hsplit, hapex⟩
  have hnp : ¬ ActivePrefix x q := fun hp => activePrefix_not_activeSuffix hp hs
  rw [blockTransform, dif_neg hnp, dif_pos hs]
  have hj : Classical.choose hs = j :=
    (Classical.choose_spec hs).2.2.1.unique hsplit
  subst j
  rfl

theorem blockTransform_eq_self (x : Fin (r + 1 + 1) → ℝ) (q : BlockIndex r)
    (hp : ¬ ActivePrefix x q) (hs : ¬ ActiveSuffix x q) :
    blockTransform x q = q := by
  rw [blockTransform, dif_neg hp, dif_neg hs]

theorem blockTransform_involutive (x : Fin (r + 1 + 1) → ℝ) :
    Function.Involutive (blockTransform x : BlockIndex r → BlockIndex r) := by
  intro q
  by_cases hp : ActivePrefix x q
  · obtain ⟨j, ha0, hb, hsplit, hapex⟩ := hp
    rw [blockTransform_eq_prefix x q j ha0 hb hsplit hapex]
    have hb' : j.succ ∈ (prefixPairAt q j ha0 hb).2.1 :=
      (mem_toggleCut_of_ne (ne_of_gt (Fin.castSucc_lt_succ j))).mpr hb
    have hsplit' : SplitValues (blockWordValues x (prefixPairAt q j ha0 hb)) j := by
      rwa [blockWordValues_prefixPairAt]
    have hapex' : blockApexValue x (prefixPairAt q j ha0 hb) =
        blockWordValues x (prefixPairAt q j ha0 hb) j.succ := by
      rwa [blockApexValue_prefixPairAt, blockWordValues_prefixPairAt]
    rw [blockTransform_eq_prefix x (prefixPairAt q j ha0 hb) j ha0 hb' hsplit' hapex']
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact toggleCut_involutive j.castSucc q.2.1
  · by_cases hs : ActiveSuffix x q
    · obtain ⟨j, hsize, ha, hsplit, hapex⟩ := hs
      rw [blockTransform_eq_suffix x q j hsize ha hsplit hapex]
      have ha' : j.succ ∈ (suffixPairAt q j hsize ha).2.1 := by
        change (nextIndex j hsize).castSucc ∈
          toggleCut (nextIndex j hsize).succ q.2.1
        exact (mem_toggleCut_of_ne (ne_of_lt (Fin.castSucc_lt_succ _))).mpr ha
      have hsplit' : SplitValues (blockWordValues x (suffixPairAt q j hsize ha)) j := by
        rwa [blockWordValues_suffixPairAt x q j hsize ha hsplit]
      have hapex' : blockApexValue x (suffixPairAt q j hsize ha) =
          blockWordValues x (suffixPairAt q j hsize ha) 0 := by
        rw [blockApexValue_suffixPairAt]
        rwa [blockWordValues_suffixPairAt x q j hsize ha hsplit]
      rw [blockTransform_eq_suffix x (suffixPairAt q j hsize ha) j hsize ha' hsplit' hapex']
      apply Prod.ext
      · exact suffixPerm_involutive (nextIndex j hsize) q.1
      · apply Subtype.ext
        exact toggleCut_involutive (nextIndex j hsize).succ q.2.1
    · rw [blockTransform_eq_self x q hp hs, blockTransform_eq_self x q hp hs]

theorem wordWeight_blockTransform_prefix (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (hp : ActivePrefix x q) :
    wordWeight r (blockTransform x q).2.1 = -wordWeight r q.2.1 := by
  obtain ⟨j, ha0, hb, hsplit, hapex⟩ := hp
  rw [blockTransform_eq_prefix x q j ha0 hb hsplit hapex, prefixPairAt_cuts]
  exact wordWeight_toggleCut j.castSucc q.2.1

theorem wordWeight_blockTransform_suffix (x : Fin (r + 1 + 1) → ℝ)
    (q : BlockIndex r) (hs : ActiveSuffix x q) :
    wordWeight r (blockTransform x q).2.1 = -wordWeight r q.2.1 := by
  obtain ⟨j, hsize, ha, hsplit, hapex⟩ := hs
  rw [blockTransform_eq_suffix x q j hsize ha hsplit hapex, suffixPairAt_cuts]
  exact wordWeight_toggleCut (nextIndex j hsize).succ q.2.1

end MaxNN.Caterpillar
