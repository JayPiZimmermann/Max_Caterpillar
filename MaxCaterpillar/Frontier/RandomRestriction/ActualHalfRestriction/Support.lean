import MaxCaterpillar.Frontier.RandomRestriction.WeightedRestriction

/-! # A half-size support restriction in an arbitrary ambient dimension

Embed an even coordinate set and discard whole supports that leave its image.
Only wholly contained supports are pulled back. The even restriction theorem
therefore transports exact cardinalities and whole-support charges, including
when the ambient dimension is odd. Both boundary dimensions and zero slots are
allowed; the original first-hidden index set is never changed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
open BigOperators
variable {N n h₁ : ℕ}

/-- The bounded support moment can be selected inside any embedded even set.
Rows leaving that set are discarded wholesale, rather than intersected with it. -/
theorem exists_embedded_half_support_fourth_moment (e : Fin (2*n) ↪ Fin N)
    (T : Fin h₁ → Finset (Fin N)) :
    ∃ U : Finset (Fin N), U.card = n ∧ U ⊆ Finset.univ.image e ∧
      4 * (∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U then (T j).card ^ 4 else 0) ≤ 81*h₁ := by
  classical
  let V : Finset (Fin N) := Finset.univ.image e
  let Q : Fin h₁ → Finset (Fin (2*n)) := fun j =>
    if T j ⊆ V then Finset.univ.filter (fun i => e i ∈ T j) else ∅
  have hdecode (j : Fin h₁) (hj : T j ⊆ V) : (Q j).image e = T j := by
    ext i
    constructor
    · intro hi
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
      simpa only [Q,if_pos hj,Finset.mem_filter,Finset.mem_univ,true_and] using ha
    · intro hi
      obtain ⟨a,_ha,hai⟩ := Finset.mem_image.mp (hj hi)
      refine Finset.mem_image.mpr ⟨a,?_,hai⟩
      simp only [Q,if_pos hj,Finset.mem_filter,Finset.mem_univ,true_and]
      rwa [hai]
  obtain ⟨U,hcard,hmoment⟩ :=
    MaxCaterpillar.WeightedRestriction.half_fourth_moment_restriction n
      (Fintype.card_fin (2*n)) Q
  have hUV : U.image e ⊆ V :=
    Finset.image_subset_image (Finset.subset_univ U)
  have hcost :
      (∑ j, if 3 ≤ (Q j).card ∧ Q j ⊆ U then (Q j).card ^ 4 else 0) =
        ∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U.image e then (T j).card ^ 4 else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hj : T j ⊆ V
    · have hc : (Q j).card = (T j).card := by
        have hc := Finset.card_image_of_injective (Q j) e.injective
        rw [hdecode j hj] at hc
        exact hc.symm
      have hs : Q j ⊆ U ↔ T j ⊆ U.image e := by
        rw [← hdecode j hj]
        exact (Finset.image_subset_image_iff e.injective).symm
      simp only [hc,hs]
    · have hQ : Q j = ∅ := by simp only [Q,if_neg hj]
      have hout : ¬ T j ⊆ U.image e := fun h => hj (h.trans hUV)
      simp [hQ,hout]
  refine ⟨U.image e,?_,hUV,?_⟩
  · rw [Finset.card_image_of_injective U e.injective,hcard]
  · rw [← hcost]
    simpa only [Fintype.card_fin] using hmoment

/-- Every ambient dimension admits a restriction of any half-size n with
2*n≤N and the same fourth-moment constant. No parity premise is needed. -/
theorem exists_half_support_fourth_moment (h : 2*n ≤ N)
    (T : Fin h₁ → Finset (Fin N)) :
    ∃ U : Finset (Fin N), U.card = n ∧
      4 * (∑ j, if 3 ≤ (T j).card ∧ T j ⊆ U then (T j).card ^ 4 else 0) ≤ 81*h₁ := by
  obtain ⟨U,hcard,_himage,hmoment⟩ :=
    exists_embedded_half_support_fourth_moment (Fin.castLEEmb h).toEmbedding T
  exact ⟨U,hcard,hmoment⟩

#check @exists_embedded_half_support_fourth_moment
#check @exists_half_support_fourth_moment
#print axioms exists_embedded_half_support_fourth_moment
#print axioms exists_half_support_fourth_moment
end MaxCaterpillar.Frontier.RandomRestriction.ActualHalfRestriction
