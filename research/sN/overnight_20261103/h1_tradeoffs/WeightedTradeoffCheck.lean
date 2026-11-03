import research.sN.overnight_20261103.h1_tradeoffs.WeightedTradeoff

/-! Independent raw-array contract for the support-sensitive lower bound.
The support is the literal nonzero-coordinate filter on each original row.
Neither total first width nor a count of feeding rows is bounded. -/
set_option autoImplicit false
noncomputable section
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open AffineSkipExtension GrowingMatching GrowingMatching.Bernoulli
open MaxCaterpillar.ExponentialPush MaxCaterpillar.ExponentialPush.WidthTradeoff
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff.Audit
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}
local instance weightedArityNeZero (q : ℕ) : NeZero (4*q+1) := ⟨Nat.succ_ne_zero _⟩

theorem exact_weighted_support_contract (d : ℕ) (hd : 1 ≤ d)
    (hsize : 10000000000*d^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (4*Nat.floor (Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ)))+1)
      (Nat.floor (Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ)))))
    (A : Fin h₁ → (Fin N → ℝ)) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → (Fin N → ℝ))
    (theta outerCoeff : Fin h₂ → ℝ) (B : Fin h₁ → ℝ)
    (L : Fin N → ℝ) (beta : ℝ)
    (hnet : letI := originalNeZero N d hd hsize;
      ∀ x : Fin N → ℝ,
        (∑ k, outerCoeff k * max ((∑ j, W k j * max ((∑ i, A j i*x i)+b j) 0)+
          (∑ i, U k i*x i)+theta k) 0)+
        ((∑ j, B j * max ((∑ i, A j i*x i)+b j) 0)+(∑ i, L i*x i)+beta) =
          Maximum N x)
    (hbudget : (∑ j : Fin h₁,
      let r := (Finset.univ.filter (fun i : Fin N => A j i ≠ 0)).card
      if b j=0 ∧ (∑ i : Fin N, A j i)=0 ∧ (∃ k : Fin h₂, W k j≠0) then
        (if r ≤ N/2 then ((if 3≤r then max 1 (r.descFactorial 4) else 0 : ℕ) : ℝ)
          else 0)/(2 : ℝ)^r else 0) ≤ (d : ℝ)^2*((N/2 : ℕ) : ℝ)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ))) ≤
      (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,theta,outerCoeff,B,L,beta⟩
  have hH : LocalMatchingObstruction (Parameters.minimumArity (N/2) d)
      (Parameters.matchingOrder (N/2) d) := by
    simpa only [Parameters.minimumArity,Affine.matchingOrder_eq_sqrt_floor] using H
  have hb : originalSupportBudget (N/2) net ≤ (d : ℝ)^2*((N/2 : ℕ) : ℝ)^2 := by
    simpa only [originalSupportBudget,WeightedSupport.affineFeedingSupportBudget,
      WeightedSupport.clipCost,supportCost,supportCostNat,NormalizedNetwork.rowSupport,net]
      using hbudget
  apply conditional_affine_support_tradeoff d hd hsize hH net ?_ hb
  intro x
  have hrelu : ∀ t : ℝ, relu t=max t 0 := fun t => max_comm 0 t
  simpa only [AffineSkipExtension.eval,AffineSkipExtension.inner,
    AffineSkipExtension.outputSkip,AffineSkipExtension.first,net,hrelu] using hnet x

theorem exact_cost_at_small_support (r : ℕ) (hr : r ≤ 2) : supportCost r=0 := by
  unfold supportCost supportCostNat
  rw [if_neg (by linarith only [hr])]
  exact Nat.cast_zero

theorem exact_clipped_cost_zero (n r : ℕ) (hr : n<r) :
    (if r≤n then supportCost r else 0)/(2 : ℝ)^r=0 := by
  rw [if_neg (Nat.not_le_of_gt hr),zero_div]

example : supportCost 3=1 := by norm_num [supportCost,supportCostNat]
example : supportCost 4=24 := by norm_num [supportCost,supportCostNat,Nat.descFactorial]
example : supportCost 7=840 := by norm_num [supportCost,supportCostNat,Nat.descFactorial]
example : supportCost 8=1680 := by norm_num [supportCost,supportCostNat,Nat.descFactorial]

#check @exact_weighted_support_contract
#print axioms exact_weighted_support_contract
#print axioms exact_cost_at_small_support
#print axioms exact_clipped_cost_zero
#print axioms conditional_affine_support_tradeoff
end MaxCaterpillar.ExponentialPush.WidthTradeoff.Audit
