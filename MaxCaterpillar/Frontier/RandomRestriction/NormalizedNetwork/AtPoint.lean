import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Localization

/-! # Literal coefficients of localization at a prescribed actual point

These identities concern `localize` before the optional second diagonal pass.
Thus every surviving outer index is exactly the original outer index.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
open BigOperators
variable {N m h₁ h₂ : ℕ}

/-- First-to-second coefficients are only masked; they are never rescaled or merged. -/
theorem localize_weights (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (j : Fin h₁) :
    (net.localize q e).W k j = if net.inner k q = 0 then
      (if lin (net.A j) q = 0 then net.W k j else 0) else 0 := rfl

theorem localize_outer_output (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (e : Fin m ↪ Fin N) (k : Fin h₂) :
    (net.localize q e).d k = if net.inner k q = 0 then net.d k else 0 := rfl

theorem localize_linear_skip (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (e : Fin m ↪ Fin N) (k : Fin h₂) :
    (net.localize q e).U k = if net.inner k q = 0 then
      restrict e (net.U k) +
        ∑ j, if 0 < lin (net.A j) q then net.W k j • restrict e (net.A j) else 0
      else 0 := rfl

theorem localize_retained_weight (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (j : Fin h₁)
    (hk : net.inner k q = 0) (hj : lin (net.A j) q = 0) :
    (net.localize q e).W k j = net.W k j := by
  simp only [localize_weights,hk,hj,ite_true]

theorem localize_first_output (net : NormalizedNetwork N h₁ h₂) (q : Point N)
    (e : Fin m ↪ Fin N) (j : Fin h₁) :
    (net.localize q e).B j = if lin (net.A j) q = 0 then
      net.B j + ∑ k, if 0 < net.inner k q then net.d k * net.W k j else 0
      else 0 := by
  classical
  by_cases hj : lin (net.A j) q = 0 <;> simp [localize,freezeOuter,localFirst,hj]

#print axioms localize_weights
#print axioms localize_linear_skip
#print axioms localize_first_output
end MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork
