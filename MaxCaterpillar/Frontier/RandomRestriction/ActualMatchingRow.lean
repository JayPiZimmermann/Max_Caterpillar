import MaxCaterpillar.Frontier.RandomRestriction.CleanActivation
import MaxCaterpillar.Frontier.RandomRestriction.EffectiveCoinDifference
import MaxCaterpillar.Frontier.RandomRestriction.BraidCoinActivation
import MaxCaterpillar.Frontier.RandomRestriction.DominantGap.NetworkRealization

/-! # The actual effective-row map on isolated matching coins

The activation calculation is performed on the original real first rows. Its
restricted row is the exact coefficient vector whose vanishing is equivalent
to an actual second preactivation vanishing at a common generic scale.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction
open BigOperators Cartesian DominantGap GoodEvent NormalizedNetwork
variable {N h₁ h₂ m : ℕ}

noncomputable def actualMatchingRow (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho tau : Equiv.Perm (Fin m))
    (T : ℝ) : Point m :=
  restrict e (actualEffectiveRow net k (actualGapPoint e (tau,rho) T))

theorem actualMatchingRow_zero_iff (net : NormalizedNetwork N h₁ h₂)
    (e : Fin m ↪ Fin N) (k : Fin h₂) (rho tau : Equiv.Perm (Fin m))
    (T : ℝ) (hg : GenericNetworkPoint net e (tau,rho) T) :
    actualMatchingRow net e k rho tau T = 0 ↔
      net.inner k (actualGapPoint e (tau,rho) T) = 0 :=
  (hg.second_zero_iff k).symm

theorem restrict_braidRoot (e : Fin m ↪ Fin N) (a b : Fin m) :
    restrict e (braidRoot (e a) (e b)) = braidRoot a b := by
  funext x
  simp only [restrict, braidRoot, Pi.sub_apply, unitVec, e.injective.eq_iff]

/-- Adapter of any proved original effective-row difference to the actual
restricted vector, with the original edge coefficient unchanged. -/
theorem actualMatchingRow_sub_of_effective_difference
    (net : NormalizedNetwork N h₁ h₂) (e : Fin m ↪ Fin N) (k : Fin h₂)
    (rho tau tau' : Equiv.Perm (Fin m)) (T : ℝ) (a b : Fin m) (c : ℝ)
    (h : actualEffectiveRow net k (actualGapPoint e (tau',rho) T) -
      actualEffectiveRow net k (actualGapPoint e (tau,rho) T) =
        c • braidRoot (e a) (e b)) :
    actualMatchingRow net e k rho tau' T - actualMatchingRow net e k rho tau T =
      c • braidRoot a b := by
  have he := congrArg (restrict e) h
  change actualMatchingRow net e k rho tau' T - actualMatchingRow net e k rho tau T =
    restrict e (c • braidRoot (e a) (e b)) at he
  have hs : restrict e (c • braidRoot (e a) (e b)) = c • braidRoot a b := by
    funext x
    change c * braidRoot (e a) (e b) (e x) = c * braidRoot a b x
    have hx := congrFun (restrict_braidRoot e a b) x
    change braidRoot (e a) (e b) (e x) = braidRoot a b x at hx
    rw [hx]
  exact he.trans hs

#print axioms actualMatchingRow_zero_iff
#print axioms restrict_braidRoot
#print axioms actualMatchingRow_sub_of_effective_difference
end MaxCaterpillar.Frontier.RandomRestriction
