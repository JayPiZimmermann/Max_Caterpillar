import research.sN.overnight_20261103.h1_tradeoffs.AffineFeeding
import research.sN.overnight_20261103.h1_tradeoffs.SqrtCoefficient

/-! Independently written raw-array contracts. The structural obstruction,
integer matching order, original feeding-column count and every constant are
visible. No model, normalization, support, survival or probability premise
is supplied to either contract. -/
set_option autoImplicit false
noncomputable section
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Frontier.RandomRestriction
open AffineSkipExtension GrowingMatching GrowingMatching.Bernoulli
open MaxCaterpillar.ExponentialPush.WidthTradeoff
namespace MaxCaterpillar.ExponentialPush.WidthTradeoff.Audit
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}
local instance arityNeZero (q : ℕ) : NeZero (4*q+1) := ⟨Nat.succ_ne_zero _⟩

theorem exact_total_width_contract (d : ℕ) (hd : 1 ≤ d)
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
    (hwidth : 81*h₁ ≤ 4*d^2*(N/2)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ))) ≤
      (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,theta,outerCoeff,B,L,beta⟩
  have hH : LocalMatchingObstruction (Parameters.minimumArity (N/2) d)
      (Parameters.matchingOrder (N/2) d) := by
    simpa only [Parameters.minimumArity,Affine.matchingOrder_eq_sqrt_floor] using H
  apply conditional_affine_width_tradeoff d hd hsize hH net ?_ hwidth
  intro x
  have hrelu : ∀ t : ℝ, relu t=max t 0 := fun t => max_comm 0 t
  simpa only [AffineSkipExtension.eval,AffineSkipExtension.inner,
    AffineSkipExtension.outputSkip,AffineSkipExtension.first,net,hrelu] using hnet x

theorem exact_feeding_width_contract (d : ℕ) (hd : 1 ≤ d)
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
    (hwidth : 81*Fintype.card {j : Fin h₁ // ∃ k : Fin h₂, W k j ≠ 0} ≤
      4*d^2*(N/2)^2) :
    (1/2 : ℝ)*Real.exp (3*Real.sqrt ((N/2 : ℕ) : ℝ)/(8000*(d : ℝ))) ≤
      (h₂ : ℝ) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,theta,outerCoeff,B,L,beta⟩
  have hH : LocalMatchingObstruction (Parameters.minimumArity (N/2) d)
      (Parameters.matchingOrder (N/2) d) := by
    simpa only [Parameters.minimumArity,Affine.matchingOrder_eq_sqrt_floor] using H
  apply conditional_affine_feeding_tradeoff d hd hsize hH net ?_ hwidth
  intro x
  have hrelu : ∀ t : ℝ, relu t=max t 0 := fun t => max_comm 0 t
  simpa only [AffineSkipExtension.eval,AffineSkipExtension.inner,
    AffineSkipExtension.outputSkip,AffineSkipExtension.first,net,hrelu] using hnet x

/-- The explicit parameter really discharges the original-width inequality,
including odd N; the only required boundary is a nonempty half. -/
theorem exact_rounding_budget (h : ℕ) (hn : 2 ≤ N) :
    81*h ≤ 4*(Nat.sqrt (81*h/(4*(N/2)^2))+1)^2*(N/2)^2 :=
  widthParameter_budget (N/2) h (Nat.div_pos hn (by decide : 0<2))

example (n : ℕ) : widthParameter n 0 = 1 := by simp [widthParameter]
example : widthParameter (10/2) (10^2) = 10 := by decide
example : widthParameter (11/2) (11^2) = 10 := by decide
example : widthParameter 10 399 = 9 := by decide
example : widthParameter 10 400 = 10 := by decide
example : sqrtCeiling 1 = 1 := by decide
example : sqrtCeiling 4 = 2 := by decide
example : sqrtCeiling 9 = 3 := by decide

#check @exact_total_width_contract
#check @exact_feeding_width_contract
#check @conditional_affine_width_tradeoff_explicit
#check @conditional_affine_feeding_tradeoff_explicit
#check @conditional_affine_sqrt_coefficient
#print axioms exact_total_width_contract
#print axioms exact_feeding_width_contract
#print axioms exact_rounding_budget
#print axioms conditional_affine_width_tradeoff_explicit
#print axioms conditional_affine_feeding_tradeoff_explicit
#print axioms conditional_affine_sqrt_coefficient
end MaxCaterpillar.ExponentialPush.WidthTradeoff.Audit
