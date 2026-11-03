import research.sN.overnight_20261103.portfolio.coordinate_quotient.Model
import research.sN.overnight_20261103.portfolio.transversal.Model

/-! Every braid coordinate quotient admits a same-size generic deletion.
Thus the quotient criterion must not be advertised as stronger than the
optimal support-transversal criterion. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.CoordinateQuotient
open BigOperators Frontier Frontier.RandomRestriction
open AffineSkipExtension NormalizedNetwork
variable {N m h₁ h₂ : ℕ}

theorem blockSum_eq_on_section (φ : Fin N → Fin m) (e : Fin m ↪ Fin N)
    (he : ∀ b, φ (e b) = b) (a : Point N)
    (ha : rowSupport a ⊆ Finset.univ.image e) (b : Fin m) :
    blockSum φ a b = a (e b) := by
  classical
  unfold blockSum
  rw [Finset.sum_eq_single (e b)]
  · rw [if_pos (he b)]
  · intro i _ hi
    by_cases hφ : φ i = b
    · rw [if_pos hφ]
      by_contra hne
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp (ha ((mem_rowSupport a i).mpr hne))
      have hcb : c = b := by rw [← he c, hc, hφ]
      exact hi (hc.symm.trans (congrArg e hcb))
    · rw [if_neg hφ]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem braidOnRetained_of_section (net : AffineSkipNetwork N h₁ h₂)
    (φ : Fin N → Fin m) (hbraid : BraidBlockSums net φ)
    (e : Fin m ↪ Fin N) (he : ∀ b, φ (e b) = b) :
    SupportTransversal.BraidOnRetained net e := by
  intro j hb hs hsub
  have hrow : blockSum φ (net.A j) = restrict e (net.A j) := by
    funext b
    exact blockSum_eq_on_section φ e he (net.A j) hsub b
  have h := hbraid j hb hs
  rw [hrow, card_rowSupport_restrict e (net.A j) hsub] at h
  exact h

/-- Choosing one representative per block produces a retained coordinate
set of exactly the same size satisfying the generic deletion condition. -/
theorem exists_braid_retained_of_quotient (net : AffineSkipNetwork N h₁ h₂)
    (φ : Fin N → Fin m) (hφ : Function.Surjective φ)
    (hbraid : BraidBlockSums net φ) :
    ∃ e : Fin m ↪ Fin N, SupportTransversal.BraidOnRetained net e := by
  let e : Fin m ↪ Fin N := ⟨Function.surjInv hφ,
    (Function.rightInverse_surjInv hφ).injective⟩
  refine ⟨e, braidOnRetained_of_section net φ hbraid e ?_⟩
  intro b
  exact Function.surjInv_eq hφ b

#check @exists_braid_retained_of_quotient
#print axioms blockSum_eq_on_section
#print axioms exists_braid_retained_of_quotient
end MaxCaterpillar.Overnight.CoordinateQuotient
