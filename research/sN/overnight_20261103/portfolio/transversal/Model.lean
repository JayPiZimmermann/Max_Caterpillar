import MaxCaterpillar.Frontier.RandomRestriction.AffineSkipNormalization

/-! A support transversal replaces a first-width cap.  At a generic top tie,
every original zero-bias, zero-sum first row meeting the deleted coordinates
becomes affine.  No first or second hidden index is added or identified. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.SupportTransversal
open BigOperators Frontier Frontier.RandomRestriction
open NormalizedNetwork AffineSkipExtension
variable {N m h₁ h₂ : ℕ}

/-- The retained coordinate set contains no support of an original first row
that can remain nonlinear and has at least three nonzero coordinates. -/
def BraidOnRetained (net : AffineSkipNetwork N h₁ h₂) (e : Fin m ↪ Fin N) : Prop :=
  ∀ j, net.b j = 0 → (∑ i, net.A j i) = 0 →
    rowSupport (net.A j) ⊆ Finset.univ.image e →
      (rowSupport (net.A j)).card ≤ 2

/-- Exact generic localization of the actual nine-array model. Widths are
unchanged; arbitrary affine heads, biases, and output skips are permitted. -/
theorem exists_braid_model [NeZero N] [NeZero m]
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (e : Fin m ↪ Fin N) (hkeep : BraidOnRetained net e) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x, model.eval x = Maximum m x) ∧ model.TranslationNormalized ∧
      (∀ j, (rowSupport (model.A j)).card ≤ 2) ∧
      (∀ j, model.Feeding j → ∃ k, net.W k j ≠ 0) := by
  classical
  let source := normalizedModel net
  have hsmax : ∀ x, source.eval x = Maximum N x :=
    normalizedModel_computes_max net hnet
  have hsnorm : source.TranslationNormalized :=
    normalizedModel_translation_normalized net hnet
  obtain ⟨model, hmax, hnorm, hrows, hfeed⟩ :=
    source.exists_localized_normalized hsmax hsnorm.1 e
  refine ⟨model, hmax, hnorm, ?_, ?_⟩
  · intro j
    rw [hrows j]
    by_cases hsub : rowSupport (source.A j) ⊆ Finset.univ.image e
    · rw [if_pos hsub, card_rowSupport_restrict e (source.A j) hsub]
      change (rowSupport ((normalizedModel net).A j)).card ≤ 2
      rw [normalizedModel_first_row]
      by_cases hj : net.b j = 0 ∧ (∑ i, net.A j i) = 0
      · rw [if_pos hj]
        apply hkeep j hj.1 hj.2
        simpa only [source, normalizedModel_first_row, if_pos hj] using hsub
      · rw [if_neg hj, rowSupport_zero, Finset.card_empty]
        exact Nat.zero_le 2
    · rw [if_neg hsub, rowSupport_zero, Finset.card_empty]
      exact Nat.zero_le 2
  · intro j hj
    exact normalizedModel_feeding_original net j (hfeed j hj)

/-- Direct transversal form: every relevant large support meets C, and all
retained coordinates avoid C. No bound on the number of these rows occurs. -/
theorem braidOnRetained_of_transversal (net : AffineSkipNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (C : Finset (Fin N))
    (havoid : ∀ a, e a ∉ C)
    (hhit : ∀ j, net.b j = 0 → (∑ i, net.A j i) = 0 →
      3 ≤ (rowSupport (net.A j)).card →
      ∃ i ∈ rowSupport (net.A j), i ∈ C) :
    BraidOnRetained net e := by
  intro j hb hs hsub
  by_contra hbad
  have hlarge : 3 ≤ (rowSupport (net.A j)).card := Nat.succ_le_of_lt (Nat.lt_of_not_ge hbad)
  obtain ⟨i, hi, hiC⟩ := hhit j hb hs hlarge
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hsub hi)
  exact havoid a (ha ▸ hiC)

#check @exists_braid_model
#check @braidOnRetained_of_transversal
#print axioms exists_braid_model
#print axioms braidOnRetained_of_transversal
end MaxCaterpillar.Overnight.SupportTransversal
