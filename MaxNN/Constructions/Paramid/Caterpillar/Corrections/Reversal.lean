import MaxNN.Constructions.Paramid.Caterpillar.Corrections.NormalizeFaces

/-! # Reversal of the full caterpillar spine

For the all-cut word the caterpillar base is a path.  Reversing its base
order reverses every edge label and moves the affine endpoint by the sum of
the old labels.  Orientation normalization therefore identifies the two
words.  The reversal is fixed-point free as soon as the path has an edge.
-/

open BigOperators

namespace MaxNN.Caterpillar.Corrections

open ParamidGeom ParamidChain

variable {n r : ℕ}

theorem reverseLabel_simplex_sub_iff {a b : Fin (n + 1)} (hab : a ≠ b) :
    reverseLabel (toR (vtx a) - toR (vtx b)) ↔ b < a := by
  constructor
  · rintro ⟨c, d, hdc, he⟩
    exact (simplex_difference_endpoints hab he).2 ▸
      (simplex_difference_endpoints hab he).1 ▸ hdc
  · intro hba
    exact ⟨a, b, hba, rfl⟩

theorem reverseLabel_neg_simplex_sub_iff {a b : Fin (n + 1)} (hab : a ≠ b) :
    reverseLabel (-(toR (vtx a) - toR (vtx b))) ↔ a < b := by
  rw [neg_sub]
  exact reverseLabel_simplex_sub_iff hab.symm

theorem orientedLabel_neg_simplex_sub {a b : Fin (n + 1)} (hab : a ≠ b) :
    orientedLabel (-(toR (vtx a) - toR (vtx b))) =
      orientedLabel (toR (vtx a) - toR (vtx b)) := by
  unfold orientedLabel
  rw [reverseLabel_simplex_sub_iff hab,
    reverseLabel_neg_simplex_sub_iff hab]
  rcases lt_or_gt_of_ne hab with hab' | hba
  · simp [hab', not_lt_of_ge hab'.le, neg_neg]
  · simp [hba, not_lt_of_ge hba.le]

/-- Negating every label and translating the apex by their sum does not
change the orientation-normalized key. -/
theorem normalizedKey_neg_image (γ : Fin n → ℝ) (V : Finset (Fin n → ℝ))
    (hV : ∀ v ∈ V, ∃ a b : Fin (n + 1), a ≠ b ∧
      v = toR (vtx a) - toR (vtx b)) :
    normalizedKey (γ + ∑ v in V, v, V.image fun v => -v) =
      normalizedKey (γ, V) := by
  classical
  have hrev (v : Fin n → ℝ) (hv : v ∈ V) :
      reverseLabel (-v) ↔ ¬ reverseLabel v := by
    obtain ⟨a, b, hab, rfl⟩ := hV v hv
    rw [reverseLabel_simplex_sub_iff hab,
      reverseLabel_neg_simplex_sub_iff hab]
    exact ⟨fun hab' hba => (not_lt_of_ge hab'.le) hba,
      fun hn => (lt_or_gt_of_ne hab).resolve_right hn⟩
  have horient (v : Fin n → ℝ) (hv : v ∈ V) :
      orientedLabel (-v) = orientedLabel v := by
    obtain ⟨a, b, hab, rfl⟩ := hV v hv
    exact orientedLabel_neg_simplex_sub hab
  unfold normalizedKey
  apply Prod.ext
  · simp only [Finset.sum_filter]
    rw [Finset.sum_image]
    · rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [if_congr (hrev v hv) rfl rfl]
      by_cases h : reverseLabel v <;> simp [h]
    · intro a _ha b _hb hab
      exact neg_injective hab
  · rw [Finset.image_image]
    apply Finset.image_congr
    intro v hv
    exact horient v hv

/-- Reverse the base slots while fixing the apex slot. -/
def pathSlotReverse (r : ℕ) : Equiv.Perm (Fin (r + 1 + 1)) where
  toFun i := Fin.cases 0 (fun j => (Fin.rev j).succ) i
  invFun i := Fin.cases 0 (fun j => (Fin.rev j).succ) i
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cases_succ, Fin.rev_rev]
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [Fin.cases_succ, Fin.rev_rev]

def reversePathPerm (π : Equiv.Perm (Fin (r + 1 + 1))) :
    Equiv.Perm (Fin (r + 1 + 1)) :=
  (pathSlotReverse r).trans π

@[simp] theorem reversePathPerm_zero (π : Equiv.Perm (Fin (r + 1 + 1))) :
    reversePathPerm π 0 = π 0 := rfl

@[simp] theorem reversePathPerm_succ (π : Equiv.Perm (Fin (r + 1 + 1)))
    (i : Fin (r + 1)) :
    reversePathPerm π i.succ = π (Fin.rev i).succ := rfl

@[simp] theorem reversePathPerm_involutive
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    reversePathPerm (reversePathPerm π) = π := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp

theorem reversePathPerm_ne (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) : reversePathPerm π ≠ π := by
  intro he
  have h := congrArg (fun q : Equiv.Perm (Fin (r + 1 + 1)) => q (1 : Fin (r + 2))) he
  apply π.injective at h
  have hv := congrArg Fin.val h
  change r + 1 = 1 at hv
  omega

theorem parent_cutPositions_succ (j : Fin r) :
    parent (cutPositions r) j.succ = j.castSucc := by
  apply le_antisymm
  · have hp := parent_lt (S := cutPositions r) (Fin.succ_pos j)
    change (parent (cutPositions r) j.succ).val ≤ j.val
    change (parent (cutPositions r) j.succ).val < j.val + 1 at hp
    omega
  · by_cases hj : j.val = 0
    · rw [show j.castSucc = 0 by apply Fin.ext; exact hj]
      exact Fin.zero_le _
    · apply le_parent_of_mem
      · apply Finset.mem_erase.mpr
        exact ⟨by
          intro he
          apply hj
          exact congrArg Fin.val he, Finset.mem_univ _⟩
      · exact Fin.castSucc_lt_succ j

theorem lastHead_cutPositions (hr : 1 ≤ r) :
    lastHead (cutPositions r) = Fin.last r := by
  apply le_antisymm
  · exact Fin.le_last _
  · apply Finset.le_max'
    apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have hv := congrArg Fin.val h
    change r = 0 at hv
    omega

theorem sum_path_edges (A : Fin (r + 1) → Fin n → ℝ) :
    (∑ j : Fin r, (A j.castSucc - A (Fin.succ j))) = A 0 - A (Fin.last r) := by
  induction r with
  | zero =>
      funext x
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply, Pi.sub_apply]
      rw [show Fin.last 0 = (0 : Fin 1) by apply Fin.ext; rfl]
      ring
  | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      simp_rw [Fin.succ_castSucc]
      have h := ih (A := fun i : Fin (r + 1) => A i.castSucc)
      rw [h]
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [show Fin.castSucc (0 : Fin (r + 1)) = (0 : Fin (r + 2)) by rfl]
      rw [show Fin.succ (Fin.last r) = Fin.last (r + 1) by apply Fin.ext; rfl]
      ring

theorem cutPositions_mem_admissible (hr : 1 ≤ r) :
    cutPositions r ∈ admissibleCuts r := by
  apply Finset.mem_erase.mpr
  constructor
  · intro he
    have hm : Fin.last r ∈ cutPositions r := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      have hv := congrArg Fin.val h
      change r = 0 at hv
      omega
    rw [he] at hm
    exact Finset.not_mem_empty _ hm
  · exact Finset.mem_powerset.mpr (Finset.Subset.rfl)

noncomputable def pathWord (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) : WordIndex r :=
  (π, ⟨cutPositions r, cutPositions_mem_admissible hr⟩)

theorem path_edge_reverse (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) (j : Fin r) :
    edgeVecs (wordBase (pathWord hr (reversePathPerm π))) (cutPositions r) j =
      -edgeVecs (wordBase (pathWord hr π)) (cutPositions r) (Fin.rev j) := by
  unfold edgeVecs wordBase pathWord
  rw [parent_cutPositions_succ, parent_cutPositions_succ]
  simp only [reversePathPerm_succ]
  have h₁ : Fin.rev j.castSucc = (Fin.rev j).succ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.coe_castSucc, Fin.val_succ]
    have hj := j.isLt
    have hjle : j.val + 1 ≤ r := by omega
    simpa only [Nat.succ_eq_add_one] using Nat.succ_sub hjle
  have h₂ : Fin.rev j.succ = (Fin.rev j).castSucc := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
    have hj := j.isLt
    have hjle : j.val + 1 ≤ r := by omega
    exact Nat.succ_sub_succ_eq_sub r (j.val + 1)
  rw [h₁, h₂]
  exact (neg_sub _ _).symm

theorem path_labels_reverse (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    wordLabels (pathWord hr (reversePathPerm π)) =
      (wordLabels (pathWord hr π)).image fun v => -v := by
  classical
  change (Finset.univ.image
      (edgeVecs (wordBase (pathWord hr (reversePathPerm π))) (cutPositions r))) =
    (Finset.univ.image (edgeVecs (wordBase (pathWord hr π)) (cutPositions r))).image
      (fun v => -v)
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨edgeVecs (wordBase (pathWord hr π)) (cutPositions r) (Fin.rev j),
      ⟨Fin.rev j, rfl⟩, ?_⟩
    exact (path_edge_reverse hr π j).symm
  · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
    refine ⟨Fin.rev j, ?_⟩
    rw [path_edge_reverse, Fin.rev_rev]

theorem path_gamma_reverse (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    wordGamma (pathWord hr (reversePathPerm π)) =
      wordGamma (pathWord hr π) + ∑ v in wordLabels (pathWord hr π), v := by
  classical
  have hinj : Function.Injective
      (edgeVecs (wordBase (pathWord hr π)) (cutPositions r)) := by
    exact edgeVecs_simplex_injective (fun i => π i.succ)
      (π.injective.comp (Fin.succ_injective (r + 1))) (cutPositions r)
  change wordBase (pathWord hr (reversePathPerm π)) (lastHead (cutPositions r)) -
      wordApex (pathWord hr (reversePathPerm π)) =
    wordBase (pathWord hr π) (lastHead (cutPositions r)) - wordApex (pathWord hr π) +
      ∑ v in wordLabels (pathWord hr π), v
  rw [lastHead_cutPositions hr]
  change _ = _ + ∑ v in Finset.univ.image
    (edgeVecs (wordBase (pathWord hr π)) (cutPositions r)), v
  rw [Finset.sum_image (fun a _ha b _hb he => hinj he)]
  rw [show (∑ j : Fin r,
      edgeVecs (wordBase (pathWord hr π)) (cutPositions r) j) =
      ∑ j : Fin r, (wordBase (pathWord hr π) j.castSucc -
        wordBase (pathWord hr π) j.succ) by
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [edgeVecs, parent_cutPositions_succ]]
  rw [sum_path_edges (wordBase (pathWord hr π))]
  unfold wordBase wordApex pathWord
  simp only [reversePathPerm_zero, reversePathPerm_succ]
  rw [show Fin.rev (Fin.last r) = (0 : Fin (r + 1)) by apply Fin.ext; simp]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem path_labels_simplexDifference (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    ∀ v ∈ wordLabels (pathWord hr π), ∃ a b : Fin (r + 1 + 1), a ≠ b ∧
      v = toR (vtx a) - toR (vtx b) := by
  intro v hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨π (parent (cutPositions r) j.succ).succ, π j.succ.succ, ?_, rfl⟩
  intro he
  have hp := π.injective he
  have hp' := Fin.succ_injective (r + 1) hp
  exact (ne_of_lt (parent_lt (Fin.succ_pos j))) hp'

theorem normalized_pathWord_reverse (hr : 1 ≤ r)
    (π : Equiv.Perm (Fin (r + 1 + 1))) :
    normalizedKey (wordKey (pathWord hr (reversePathPerm π))) =
      normalizedKey (wordKey (pathWord hr π)) := by
  unfold wordKey
  rw [path_labels_reverse hr π, path_gamma_reverse hr π]
  exact normalizedKey_neg_image _ _ (path_labels_simplexDifference hr π)

noncomputable def normalizedPathCones (hr : 1 ≤ r) :
    Finset (RealKey (r + 1)) :=
  Finset.univ.image fun π : Equiv.Perm (Fin (r + 1 + 1)) =>
    normalizedKey (wordKey (pathWord hr π))

private noncomputable def pathConeRepresentative (hr : 1 ≤ r)
    (k : normalizedPathCones hr) : Equiv.Perm (Fin (r + 1 + 1)) :=
  Classical.choose (Finset.mem_image.mp k.2)

private theorem pathConeRepresentative_spec (hr : 1 ≤ r)
    (k : normalizedPathCones hr) :
    normalizedKey (wordKey (pathWord hr (pathConeRepresentative hr k))) = k.1 :=
  (Classical.choose_spec (Finset.mem_image.mp k.2)).2

private noncomputable def pathConePairEmbedding (hr : 1 ≤ r) :
    Fin 2 × normalizedPathCones hr → Equiv.Perm (Fin (r + 1 + 1)) :=
  fun q => if q.1 = 0 then pathConeRepresentative hr q.2
    else reversePathPerm (pathConeRepresentative hr q.2)

private theorem pathConePairEmbedding_injective (hr : 1 ≤ r) :
    Function.Injective (pathConePairEmbedding hr) := by
  intro q₁ q₂ he
  have hkey (q : Fin 2 × normalizedPathCones hr) :
      normalizedKey (wordKey (pathWord hr (pathConePairEmbedding hr q))) = q.2.1 := by
    unfold pathConePairEmbedding
    split_ifs
    · exact pathConeRepresentative_spec hr q.2
    · exact (normalized_pathWord_reverse hr _).trans
        (pathConeRepresentative_spec hr q.2)
  have hk : q₁.2 = q₂.2 := by
    apply Subtype.ext
    rw [← hkey q₁, ← hkey q₂, he]
  rcases q₁ with ⟨b₁, k₁⟩
  rcases q₂ with ⟨b₂, k₂⟩
  dsimp only at hk
  subst k₂
  apply Prod.ext
  · fin_cases b₁ <;> fin_cases b₂
    · rfl
    · exact False.elim ((reversePathPerm_ne hr _)
        (by simpa [pathConePairEmbedding] using he.symm))
    · exact False.elim ((reversePathPerm_ne hr _)
        (by simpa [pathConePairEmbedding] using he))
    · rfl
  · rfl

theorem card_normalizedPathCones_le_half (hr : 1 ≤ r) :
    (normalizedPathCones hr).card ≤ (r + 1 + 1).factorial / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  have h := Fintype.card_le_of_injective
    (f := pathConePairEmbedding hr) (pathConePairEmbedding_injective hr)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    Fintype.card_perm, Nat.mul_comm] using h

noncomputable def pathWords (hr : 1 ≤ r) : Finset (WordIndex r) :=
  Finset.univ.filter fun w => w.2.1 = cutPositions r

noncomputable def nonPathWords (hr : 1 ≤ r) : Finset (WordIndex r) :=
  Finset.univ \ pathWords hr

noncomputable def pathWordsEquiv (hr : 1 ≤ r) :
    (pathWords hr : Type) ≃ Equiv.Perm (Fin (r + 1 + 1)) where
  toFun w := w.1.1
  invFun π := ⟨pathWord hr π, by simp [pathWords, pathWord]⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (Finset.mem_filter.mp w.2).2.symm
  right_inv π := rfl

theorem card_pathWords (hr : 1 ≤ r) :
    (pathWords hr).card = (r + 1 + 1).factorial := by
  rw [← Fintype.card_coe, Fintype.card_congr (pathWordsEquiv hr),
    Fintype.card_perm, Fintype.card_fin]

theorem card_nonPathWords (hr : 1 ≤ r) :
    (nonPathWords hr).card = Fintype.card (WordIndex r) - (r + 1 + 1).factorial := by
  unfold nonPathWords
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, card_pathWords hr]

theorem normalizedWordCones_subset_path_union (hr : 1 ≤ r) :
    normalizedWordCones r ⊆ normalizedPathCones hr ∪
      (nonPathWords hr).image (fun w => normalizedKey (wordKey w)) := by
  intro k hk
  unfold normalizedWordCones wordCones at hk
  rw [Finset.image_image] at hk
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hk
  by_cases hw : w.2.1 = cutPositions r
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨w.1, Finset.mem_univ _, ?_⟩
    congr 2
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact hw.symm
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, rfl⟩
    simp [nonPathWords, pathWords, hw]

/-- Even using only the full-cut path family, reversal removes half of one
factorial-sized slice of the raw decorated-word bound. -/
theorem card_normalizedWordCones_le_reversal (hr : 1 ≤ r) :
    (normalizedWordCones r).card ≤
      Fintype.card (WordIndex r) - (r + 1 + 1).factorial +
        (r + 1 + 1).factorial / 2 := by
  calc
    (normalizedWordCones r).card ≤
        (normalizedPathCones hr ∪
          (nonPathWords hr).image (fun w => normalizedKey (wordKey w))).card :=
      Finset.card_le_of_subset (normalizedWordCones_subset_path_union hr)
    _ ≤ (normalizedPathCones hr).card +
        ((nonPathWords hr).image (fun w => normalizedKey (wordKey w))).card :=
      Finset.card_union_le _ _
    _ ≤ (r + 1 + 1).factorial / 2 + (nonPathWords hr).card :=
      Nat.add_le_add (card_normalizedPathCones_le_half hr) Finset.card_image_le
    _ = _ := by rw [card_nonPathWords hr]; omega

end MaxNN.Caterpillar.Corrections
