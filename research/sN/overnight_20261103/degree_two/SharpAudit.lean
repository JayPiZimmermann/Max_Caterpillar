import research.sN.overnight_20261103.degree_two.SharpBound
import research.sN.overnight_20261103.degree_two.Audit

/-! Independent primitive-array contracts for the sharp graph-capacity bound.
The earlier audit and its controls are imported unchanged. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo.SharpAudit
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open AffineSkipExtension ExponentialPush.DegreeTwo.Recession
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

/-- The original nine-array contract, with the sharp factors two and four.
The entire forward pass and signed-neighbor condition are explicit. -/
theorem raw_nine_array_sharp_bounds [NeZero N]
    (A : Fin h₁ → Fin N → ℝ) (b : Fin h₁ → ℝ)
    (W : Fin h₂ → Fin h₁ → ℝ) (U : Fin h₂ → Fin N → ℝ)
    (θ : Fin h₂ → ℝ) (d : Fin h₂ → ℝ) (B : Fin h₁ → ℝ)
    (L : Fin N → ℝ) (β : ℝ)
    (hmax : ∀ x : Fin N → ℝ,
      (∑ k,d k*max 0 ((∑ j,W k j*max 0 ((∑ i,A j i*x i)+b j))+
        (∑ i,U k i*x i)+θ k))+
      ((∑ j,B j*max 0 ((∑ i,A j i*x i)+b j))+(∑ i,L i*x i)+β)=Maximum N x)
    (hA : ∀ j,∑ i,A j i=0)
    (hbraid : ∀ j,(Finset.univ.filter (fun i : Fin N => A j i≠0)).card≤2)
    (hdegree : ∀ k v,
      (Finset.univ.filter fun w : Fin N => v≠w ∧
        (∑ j in Finset.univ.filter (fun j : Fin h₁ =>
          (Finset.univ.filter (fun i : Fin N => A j i≠0))={v,w}),
          W k j*|A j v|)≠0).card≤2) :
    (∀ m : ℕ,3≤m → 2*N.choose m≤h₂*(2*N+(m-1)*N^2)) ∧
      (6≤N → (4:ℝ)*2^N/((N:ℝ)^3*((N:ℝ)+1))≤(h₂:ℝ)) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  have hmax' : ∀ x,AffineSkipExtension.eval net x=Maximum N x := hmax
  have hdegree' : ∀ k v,(rawInteractionGraph net hA k).degree v≤2 := by
    intro k v
    rw [Audit.raw_degree_literal]
    exact hdegree k v
  constructor
  · intro m hm
    exact raw_width_binomial_sharp net hmax' hA hbraid hdegree' m hm
  · intro hN
    exact raw_width_exponential_sharp_real hN net hmax' hA hbraid hdegree'

/-- The feeding-only normalized contract retains the global zero-sum
normalization, but imposes no support bound on output-only first rows. -/
theorem normalized_feeding_exact_type [NeZero N]
    (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j,∑ i,net.A j i=0) (hU : ∀ k,∑ i,net.U k i=0)
    (hL : ∑ i,net.L i=1)
    (hmax : ∀ x,net.eval x=Maximum N x)
    (hbraid : ∀ k j,net.W k j≠0 →
      (Finset.univ.filter (fun i : Fin N => net.A j i≠0)).card≤2)
    (hdegree : ∀ k v,(braidInteractionGraph net ⟨hA,hU,hL⟩ k).degree v≤2)
    (m : ℕ) (hm : 3≤m) :
    2*N.choose m≤h₂*(2*N+(m-1)*N^2) :=
  normalized_width_binomial_sharp_feeding net ⟨hA,hU,hL⟩ hmax hbraid hdegree m hm

#check @raw_nine_array_sharp_bounds
#check @normalized_feeding_exact_type
#print axioms raw_nine_array_sharp_bounds
#print axioms normalized_feeding_exact_type
#print axioms connectedSets_card_le_sharp
#print axioms two_mul_twoComponentSets_card_le_sharp
#print axioms four_pow_two_le_width_polynomial
end MaxCaterpillar.Overnight.DegreeTwo.SharpAudit
