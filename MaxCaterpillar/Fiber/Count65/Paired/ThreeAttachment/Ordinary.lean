import MaxCaterpillar.Fiber.Count65.Paired.SwitchingPath
import MaxCaterpillar.Fiber.Count65.Paired.CodeEndpointNetwork

/-! # Nonexceptional literal switching profiles reach an actual unit comparison -/
set_option autoImplicit false
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
open BigOperators Frontier Absorption

def literalSwitching (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (b₀ b₁ b₂ : Bool) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (t : ℝ) :
    Network 4 6 5 :=
  switchingWithSpectators (pairedRows U) 0 (comparisonRow U) F G 0 0 0 0
    b₀ b₁ b₂ rows 0 weights t

lemma literalSwitching_zeroBias (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (b₀ b₁ b₂ : Bool) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) (t : ℝ) :
    (literalSwitching U F G b₀ b₁ b₂ rows weights t).HasZeroBiases := by
  refine ⟨rfl,?_,rfl⟩
  funext i
  fin_cases i
  · change (if b₀ then -(0+(t-1)*0+0*0) else 0+(t-1)*0+0*0)=(0 : ℝ)
    cases b₀ <;> norm_num
  · change (if b₁ then -(0+0*0+(-1)*0) else 0+0*0+(-1)*0)=(0 : ℝ)
    cases b₁ <;> norm_num
  · change (if b₂ then -(0+(t-1)*0+(-1)*0) else 0+(t-1)*0+(-1)*0)=(0 : ℝ)
    cases b₂ <;> norm_num
  · change (0 : ℝ)=0
    rfl
  · change (0 : ℝ)=0
    rfl

lemma literalSwitching_one_first (U : Fin 2 → Fin 2 → ℝ) (F G : Fin 6 → ℝ)
    (b₀ b₁ b₂ : Bool) (rows : Fin 2 → Fin 6 → ℝ) (weights : Fin 2 → ℝ) :
    (literalSwitching U F G b₀ b₁ b₂ rows weights 1).W₂ 0=
      if b₀ then -comparisonRow U else comparisonRow U := by
  funext j
  cases b₀
  · change comparisonRow U j+(1-1)*F j+0*G j=comparisonRow U j
    ring
  · change -(comparisonRow U j+(1-1)*F j+0*G j)= -comparisonRow U j
    ring

/-- The complete nonexceptional physical profile, including both arbitrary
spectator neurons, follows an exact-network path to a unit target gate. -/
theorem literalSwitching_ordinary_to_unit (U : Fin 2 → Fin 2 → ℝ)
    (F G : Fin 6 → ℝ) (b₀ b₁ : Bool) (rows : Fin 2 → Fin 6 → ℝ)
    (weights : Fin 2 → ℝ)
    (hFG : ∀ x,preact (pairedRows U) 0 F 0 x*preact (pairedRows U) 0 G 0 x=0)
    (hsource : ∀ x,(literalSwitching U F G b₀ b₁ b₀ rows weights 0).eval x=Maximum 4 x) :
    ∃ n : ExactFiber 4 6 5,
      n.val.W₁=pairedRows U ∧ n.val.HasZeroBiases ∧ n.val.w₃ 0=1 ∧
      n.val.W₂ 0=(if b₀ then -comparisonRow U else comparisonRow U) ∧
      JoinedIn (ExactSet 4 6 5) (literalSwitching U F G b₀ b₁ b₀ rows weights 0) n.val := by
  have hp := switchingWithSpectators_joinedIn_exact (pairedRows U) 0
    (comparisonRow U) F G 0 0 0 0 b₀ b₁ rows 0 weights hFG hsource
  let n : ExactFiber 4 6 5 :=
    ⟨literalSwitching U F G b₀ b₁ b₀ rows weights 1,hp.target_mem⟩
  refine ⟨n,rfl,literalSwitching_zeroBias U F G b₀ b₁ b₀ rows weights 1,rfl,?_,hp⟩
  exact literalSwitching_one_first U F G b₀ b₁ b₀ rows weights

/-- Of the eight orientation triples, the only remaining alternative has the
two positive atoms in the same orientation, opposite the negative atom. -/
lemma orientation_cases : ∀ b₀ b₁ b₂ : Bool,
    b₀=b₂ ∨ b₁=b₂ ∨ (b₀=b₁ ∧ b₀≠b₂) := by decide

#print axioms literalSwitching_ordinary_to_unit
end MaxCaterpillar.Fiber.Count65.Paired.ThreeAttachment
