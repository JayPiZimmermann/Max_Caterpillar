import research.sN.overnight_20261103.h1_tradeoffs.SharpTradeoff

/-! Independent stronger raw-array contract: only original nonzero W columns
are charged, and all constants and the structural matching order are explicit. -/
set_option autoImplicit false
noncomputable section
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open AffineSkipExtension GrowingMatching GrowingMatching.Bernoulli
open MaxCaterpillar.ExponentialPush.WidthTradeoff
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff.Audit
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}
local instance sharpArityNeZero (q : ℕ) : NeZero (4*q+1) := ⟨Nat.succ_ne_zero _⟩

theorem exact_sharp_feeding_contract (d : ℕ) (hd : 1 ≤ d)
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
    (hwidth : 105*Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, W k j ≠ 0} ≤
      16*d^2*(N/2)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ))) ≤
      (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,theta,outerCoeff,B,L,beta⟩
  have hH : LocalMatchingObstruction (Parameters.minimumArity (N/2) d)
      (Parameters.matchingOrder (N/2) d) := by
    simpa only [Parameters.minimumArity,Affine.matchingOrder_eq_sqrt_floor] using H
  apply conditional_affine_feeding_sharp d hd hsize hH net ?_ hwidth
  intro x
  have hrelu : ∀ t : ℝ, relu t=max t 0 := fun t => max_comm 0 t
  simpa only [AffineSkipExtension.eval,AffineSkipExtension.inner,
    AffineSkipExtension.outputSkip,AffineSkipExtension.first,net,hrelu] using hnet x

theorem exact_sharp_rounding_budget (h : ℕ) (hn : 2 ≤ N) :
    105*h ≤ 16*(Nat.sqrt (105*h/(16*(N/2)^2))+1)^2*(N/2)^2 :=
  sharpParameter_budget (N/2) h (Nat.div_pos hn (by decide : 0<2))

/-- This expected type exposes the improved denominator and no total-width cap. -/
theorem exact_sqrt_coefficient_contract (C : ℕ)
    (hsize : 10000000000*(6*(Nat.sqrt (C-1)+1))^2 ≤ N/2)
    (H : LocalMatchingObstruction
      (4*Nat.floor (Real.sqrt ((N/2 : ℕ) : ℝ)/(48000*((Nat.sqrt (C-1)+1 : ℕ) : ℝ)))+1)
      (Nat.floor (Real.sqrt ((N/2 : ℕ) : ℝ)/(48000*((Nat.sqrt (C-1)+1 : ℕ) : ℝ)))))
    (net : AffineSkipNetwork N h₁ h₂)
    (hnet : letI := originalNeZero N (6*sqrtCeiling C) (by have h := sqrtCeiling_pos C; linarith only [h]) hsize;
      ∀ x, AffineSkipExtension.eval net x = Maximum N x)
    (hwidth : Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, net.W k j ≠ 0} ≤ C*N^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/
      (48000*((Nat.sqrt (C-1)+1 : ℕ) : ℝ))) ≤ (h₂ : ℝ) := by
  have he : (8000 : ℝ)*(6*sqrtCeiling C : ℕ)=48000*(sqrtCeiling C : ℝ) := by
    push_cast
    ring
  have hq : Parameters.matchingOrder (N/2) (6*sqrtCeiling C)=
      Nat.floor (Real.sqrt ((N/2 : ℕ) : ℝ)/(48000*(sqrtCeiling C : ℝ))) := by
    rw [Affine.matchingOrder_eq_sqrt_floor,he]
  have hH : LocalMatchingObstruction (Parameters.minimumArity (N/2) (6*sqrtCeiling C))
      (Parameters.matchingOrder (N/2) (6*sqrtCeiling C)) := by
    simpa only [Parameters.minimumArity,hq] using H
  exact conditional_affine_feeding_sqrt_coefficient C hsize hH net hnet hwidth

example (n : ℕ) : sharpParameter n 0 = 1 := by simp [sharpParameter]
example : sharpParameter (10/2) (10^2) = 6 := by decide
example : sharpParameter (11/2) (11^2) = 6 := by decide
example : sharpParameter 10 380 = 5 := by decide
example : sharpParameter 10 381 = 6 := by decide

#check @exact_sharp_feeding_contract
#check @exact_sqrt_coefficient_contract
#check @conditional_affine_feeding_sharp_explicit
#print axioms exact_sharp_feeding_contract
#print axioms exact_sharp_rounding_budget
#print axioms exact_sqrt_coefficient_contract
#print axioms conditional_affine_feeding_sharp_explicit
#print axioms conditional_affine_feeding_sqrt_coefficient
end MaxCaterpillar.ExponentialPush.WidthTradeoff.Audit
