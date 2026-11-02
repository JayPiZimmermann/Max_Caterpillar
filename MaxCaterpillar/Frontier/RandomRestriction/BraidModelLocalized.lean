import MaxCaterpillar.Frontier.RandomRestriction.BraidModelInteraction
import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.AtPoint

/-! # Actual localization preserves the ambient cancellation graph

The hypotheses concern the original preactivations at the actual point.
No equality of interaction graphs or aggregate coefficients is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.BraidModel
open NormalizedNetwork MaxCaterpillar.Frontier.StarCertificate
variable {N m h₁ h₂ : ℕ}

theorem localize_braidEdgeWeight_eq_ambient (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin m ↪ Fin N)
    (hfirst : ∀ j, lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image e)
    (k : Fin h₂) (hk : net.inner k q=0) (a b : Fin m) :
    braidEdgeWeight (net.localize q e).A ((net.localize q e).W k) a b=
      braidEdgeWeight net.A (net.W k) (e a) (e b) := by
  classical
  apply braidEdgeWeight_masked_restrict e net.A (net.W k)
    (net.localize q e).A ((net.localize q e).W k)
  · intro j
    rw [localize_first_row]
    simp only [hfirst j]
  · intro j hj
    exact localize_retained_weight net q e k j hk ((hfirst j).mpr hj)

theorem localize_inner_interaction_eq_ambient (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin 5 ↪ Fin N)
    (hfirst : ∀ j, lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image e)
    (k : Fin h₂) (hk : net.inner k q=0)
    (pairs : ∀ j, BraidPair ((net.localize q e).A j))
    (a b : Fin 5) (hab : a≠b) :
    effectiveInteraction (innerQuadratic (net.localize q e) pairs k) a b=
      braidEdgeWeight net.A (net.W k) (e a) (e b) := by
  rw [inner_interaction_eq_braidEdgeWeight (net.localize q e) pairs k a b hab]
  exact localize_braidEdgeWeight_eq_ambient net q e hfirst k hk a b

/-- Exact graph identity through the actual embedding. This includes the
nonedge created by any cancellation among original parallel first rows. -/
theorem localize_interaction_graph_iff (net : NormalizedNetwork N h₁ h₂)
    (q : Point N) (e : Fin 5 ↪ Fin N)
    (hfirst : ∀ j, lin (net.A j) q=0 ↔ rowSupport (net.A j)⊆Finset.univ.image e)
    (k : Fin h₂) (hk : net.inner k q=0)
    (pairs : ∀ j, BraidPair ((net.localize q e).A j)) (a b : Fin 5) :
    (quadraticInteractionGraph (innerQuadratic (net.localize q e) pairs k)).Adj a b ↔
      e a≠e b ∧ braidEdgeWeight net.A (net.W k) (e a) (e b)≠0 := by
  classical
  by_cases hab : a=b
  · subst b
    simp [quadraticInteractionGraph]
  · change (a≠b ∧ effectiveInteraction (innerQuadratic (net.localize q e) pairs k) a b≠0) ↔ _
    rw [localize_inner_interaction_eq_ambient net q e hfirst k hk pairs a b hab]
    constructor
    · rintro ⟨_,hw⟩
      exact ⟨e.injective.ne hab,hw⟩
    · rintro ⟨_,hw⟩
      exact ⟨hab,hw⟩

#print axioms localize_braidEdgeWeight_eq_ambient
#print axioms localize_inner_interaction_eq_ambient
#print axioms localize_interaction_graph_iff
end MaxCaterpillar.Frontier.RandomRestriction.BraidModel
