import MaxCaterpillar.Frontier.RandomRestriction.NetworkLowerBound

/-! Exact pruning of unused first neurons in ordinary arbitrary-bias networks.
The lower bound charges only first neurons that feed the second hidden layer. -/
set_option autoImplicit false
namespace MaxCaterpillar.Frontier.RandomRestriction.FeedingWidthExtension
open BigOperators
variable {N h₁ h₂ : ℕ}

def Feeds (net : Network N h₁ h₂) (j : Fin h₁) : Prop :=
  ∃ k,net.W₂ k j≠0

noncomputable def feedingCount (net : Network N h₁ h₂) : ℕ := by
  classical
  exact Fintype.card {j : Fin h₁ // Feeds net j}

theorem feedingCount_le (net : Network N h₁ h₂) : feedingCount net≤h₁ := by
  classical
  exact (Fintype.card_subtype_le (Feeds net)).trans_eq (Fintype.card_fin _)

noncomputable def feedingEnumeration (net : Network N h₁ h₂) :
    Fin (feedingCount net) ≃ {j : Fin h₁ // Feeds net j} := by
  classical
  exact (Fintype.equivFin _).symm

noncomputable def prune (net : Network N h₁ h₂) : Network N (feedingCount net) h₂ where
  W₁ j := net.W₁ (feedingEnumeration net j).val
  b₁ j := net.b₁ (feedingEnumeration net j).val
  W₂ k j := net.W₂ k (feedingEnumeration net j).val
  b₂ := net.b₂
  w₃ := net.w₃
  b₃ := net.b₃

theorem first_sum_prune (net : Network N h₁ h₂) (k : Fin h₂) (x : Point N) :
    (∑ j,(prune net).W₂ k j*relu ((∑ i,(prune net).W₁ j i*x i)+(prune net).b₁ j))=
      ∑ j,net.W₂ k j*relu ((∑ i,net.W₁ j i*x i)+net.b₁ j) := by
  classical
  let f : Fin h₁ → ℝ := fun j => net.W₂ k j*relu ((∑ i,net.W₁ j i*x i)+net.b₁ j)
  calc
    _ = ∑ j : {j : Fin h₁ // Feeds net j},f j.val :=
      Fintype.sum_equiv (feedingEnumeration net) _ _ (fun _ => rfl)
    _ = _ := by
      have hs := Fintype.sum_subtype_add_sum_subtype (Feeds net) f
      have hz : (∑ j : {j : Fin h₁ // ¬Feeds net j},f j.val)=0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hw : net.W₂ k j.val=0 := by
          by_contra hh
          exact j.property ⟨k,hh⟩
        exact mul_eq_zero_of_left hw _
      rw [hz,add_zero] at hs
      exact hs

/-- Literal equality of ordinary-network evaluations, retaining every bias
and the exact original second-hidden-layer index type. -/
theorem prune_eval (net : Network N h₁ h₂) (x : Point N) :
    (prune net).eval x=net.eval x := by
  simp only [Network.eval,first_sum_prune]
  rfl

/-- The closed ordinary-network tradeoff depends only on first neurons with
a nonzero weight into the second hidden layer. No other premise is added. -/
theorem second_width_tradeoff_feeding (hN : 1040≤N) (net : Network N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt
      (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,net.eval x=Maximum N x) →
      (1/400000000 : ℝ)*min ((N : ℝ)^2)
        ((N : ℝ)^4/(feedingCount net : ℝ))≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet
  apply NetworkLowerBound.second_width_tradeoff hN (prune net)
  intro x
  exact (prune_eval net x).trans (hnet x)

theorem second_width_quadratic_feeding (hN : 1040≤N) (net : Network N h₁ h₂) :
    letI : NeZero N := ⟨Nat.ne_of_gt
      (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
    (∀ x,net.eval x=Maximum N x) → (feedingCount net : ℝ)≤(N : ℝ)^2 →
      (1/400000000 : ℝ)*(N : ℝ)^2≤(h₂ : ℝ) := by
  letI : NeZero N := ⟨Nat.ne_of_gt
    (lt_of_lt_of_le (by decide : 0<1040) hN)⟩
  intro hnet hwidth
  apply NetworkLowerBound.second_width_quadratic hN (prune net) _ hwidth
  intro x
  exact (prune_eval net x).trans (hnet x)

#print axioms prune_eval
#print axioms second_width_tradeoff_feeding
#print axioms second_width_quadratic_feeding
end MaxCaterpillar.Frontier.RandomRestriction.FeedingWidthExtension
