import research.sN.overnight_20261103.degree_two.RawBound
import research.sN.overnight_20261103.degree_two.AuditControl

/-! Independent semantic contracts: the forward pass and the signed neighbor
count are expanded into the original nine parameter arrays. -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Overnight.DegreeTwo.Audit
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
open AffineSkipExtension ExponentialPush.DegreeTwo.Recession
attribute [local instance] Classical.propDecidable
variable {N h₁ h₂ : ℕ}

theorem raw_degree_literal (net : AffineSkipNetwork N h₁ h₂)
    (hA : ∀ j,∑ i,net.A j i=0) (k : Fin h₂) (v : Fin N) :
    (rawInteractionGraph net hA k).degree v=
      (Finset.univ.filter fun w : Fin N => v≠w ∧
        (∑ j in Finset.univ.filter (fun j : Fin h₁ =>
          (Finset.univ.filter (fun i : Fin N => net.A j i≠0))={v,w}),
          net.W k j*|net.A j v|)≠0).card := by
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  congr 1
  ext w
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,
    rawInteractionGraph,braidEdgeWeight,braidEdgeRows,rowSupport,neg_ne_zero]

/-- Literal nine-array contract. The graph premise counts neighbors AFTER
all parallel first-row contributions are summed with their real signs.
No width assumption, coefficient sign condition, or zero-bias hypothesis
is supplied to this declaration. -/
theorem raw_nine_array_bounds [NeZero N]
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
    (∀ m : ℕ,3≤m → N.choose m≤h₂*(2*N+2*(m-1)*N^2)) ∧
      (6≤N → (2:ℝ)^N/((N:ℝ)^3*((N:ℝ)+1))≤(h₂:ℝ)) := by
  let net : AffineSkipNetwork N h₁ h₂ := ⟨A,b,W,U,θ,d,B,L,β⟩
  have hmax' : ∀ x,AffineSkipExtension.eval net x=Maximum N x := hmax
  have hdegree' : ∀ k v,(rawInteractionGraph net hA k).degree v≤2 := by
    intro k v
    rw [raw_degree_literal]
    exact hdegree k v
  constructor
  · intro m hm
    exact raw_width_binomial net hmax' hA hbraid hdegree' m hm
  · intro hN
    exact raw_width_exponential_real hN net hmax' hA hbraid hdegree'

/-- The literal four-input network meets the full normalized assumptions,
including the actual signed-degree condition, with nonzero h₂=1. -/
theorem four_input_nonvacuity :
    Check.fourNet.TranslationNormalized ∧
    (∀ x,Check.fourNet.eval x=Maximum 4 x) ∧
    (∀ j,(rowSupport (Check.fourNet.A j)).card≤2) ∧
    (∀ k v,(braidInteractionGraph Check.fourNet Check.fourNet_normalized k).degree v≤2) := by
  refine ⟨Check.fourNet_normalized,Check.fourNet_max,Check.fourNet_braid,?_⟩
  intro k v
  exact (fourNet_degree k v).trans (by decide)

#check @raw_nine_array_bounds
#check @four_input_nonvacuity
#print axioms raw_degree_literal
#print axioms raw_nine_array_bounds
#print axioms four_input_nonvacuity
end MaxCaterpillar.Overnight.DegreeTwo.Audit
