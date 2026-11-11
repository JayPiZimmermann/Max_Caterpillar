import research.sN.overnight_20261103.constants.FallingHalf
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedTotalHalf

/-! The sharper falling-factorial budget on one actual localized model.
Original first and second hidden index types are retained. -/
set_option autoImplicit false
namespace MaxCaterpillar.Overnight.Constants.FallingHalf
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork ActualHalfRestriction
variable {N n h₁ h₂ : ℕ}

theorem exists_embedded_half_support_falling (e : Fin (2*n) ↪ Fin N)
    (T : Fin h₁ → Finset (Fin N)) :
    ∃ U : Finset (Fin N), U.card=n ∧ U⊆Finset.univ.image e ∧
      16*(∑ j, if T j⊆U then (T j).card.descFactorial 4 else 0) ≤ 105*h₁ := by
  classical
  let V : Finset (Fin N) := Finset.univ.image e
  let Q : Fin h₁ → Finset (Fin (2*n)) := fun j =>
    if T j⊆V then Finset.univ.filter (fun i => e i∈T j) else ∅
  have hdecode (j : Fin h₁) (hj : T j⊆V) : (Q j).image e=T j := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      simpa only [Q, if_pos hj, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    · intro hi
      obtain ⟨a, _, hai⟩ := Finset.mem_image.mp (hj hi)
      refine Finset.mem_image.mpr ⟨a, ?_, hai⟩
      simp only [Q, if_pos hj, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hai]
  obtain ⟨U, hcard, hmoment⟩ := half_falling_restriction n (Fintype.card_fin (2*n)) Q
  have hUV : U.image e⊆V := Finset.image_subset_image (Finset.subset_univ U)
  have hcost :
      (∑ j, if Q j⊆U then (Q j).card.descFactorial 4 else 0)=
        ∑ j, if T j⊆U.image e then (T j).card.descFactorial 4 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : T j⊆V
    · have hc : (Q j).card=(T j).card := by
        have hc := Finset.card_image_of_injective (Q j) e.injective
        rw [hdecode j hj] at hc
        exact hc.symm
      have hs : Q j⊆U ↔ T j⊆U.image e := by
        rw [←hdecode j hj]
        exact (Finset.image_subset_image_iff e.injective).symm
      simp only [hc, hs]
    · have hQ : Q j=∅ := by simp only [Q, if_neg hj]
      have hout : ¬T j⊆U.image e := fun h => hj (h.trans hUV)
      simp [hQ, hout, Nat.descFactorial]
  refine ⟨U.image e, ?_, hUV, ?_⟩
  · rw [Finset.card_image_of_injective U e.injective, hcard]
  · rw [←hcost]
    simpa only [Fintype.card_fin] using hmoment

theorem exists_half_support_falling (h : 2*n≤N)
    (T : Fin h₁ → Finset (Fin N)) :
    ∃ U : Finset (Fin N), U.card=n ∧
      16*(∑ j, if T j⊆U then (T j).card.descFactorial 4 else 0) ≤ 105*h₁ := by
  obtain ⟨U, hcard, _, hmoment⟩ :=
    exists_embedded_half_support_falling (Fin.castLEEmb h).toEmbedding T
  exact ⟨U, hcard, hmoment⟩

/-- Every exact normalized network admits a same-width half restriction
whose actual fourth falling support moment is at most 105/16 times h₁. -/
theorem exists_model [NeZero N] [NeZero n]
    (net : NormalizedNetwork N h₁ h₂) (hn : net.TranslationNormalized)
    (hnet : ∀ x, net.eval x=Maximum N x) (hpair : 2*n≤N) :
    ∃ S : Finset (Fin N), S.card=n ∧ ∃ model : NormalizedNetwork n h₁ h₂,
      (∀ x, model.eval x=Maximum n x) ∧ model.TranslationNormalized ∧
      16*(∑ j, (rowSupport (model.A j)).card.descFactorial 4) ≤ 105*h₁ := by
  classical
  obtain ⟨S, hS, hbudget⟩ := exists_half_support_falling hpair
    (fun j => rowSupport (net.A j))
  subst n
  obtain ⟨model, hmax, hnorm, hrows, _⟩ :=
    exists_localized_normalized net hnet hn.1 (selectedEmbedding S)
  have hcost :
      (∑ j, (rowSupport (model.A j)).card.descFactorial 4)=
      ∑ j, if rowSupport (net.A j)⊆S
        then (rowSupport (net.A j)).card.descFactorial 4 else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrows j, selectedEmbedding_image]
    by_cases hs : rowSupport (net.A j)⊆S
    · rw [if_pos hs, card_rowSupport_restrict (selectedEmbedding S) (net.A j)
        (by rwa [selectedEmbedding_image]), if_pos hs]
    · simp only [if_neg hs, rowSupport_zero, Finset.card_empty]
      norm_num [Nat.descFactorial]
  refine ⟨S, rfl, model, hmax, hnorm, ?_⟩
  rw [hcost]
  exact hbudget

#check @exists_model
#print axioms exists_half_support_falling
#print axioms exists_model
end MaxCaterpillar.Overnight.Constants.FallingHalf
