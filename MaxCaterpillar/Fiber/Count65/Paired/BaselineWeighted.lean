import MaxCaterpillar.Fiber.Count65.Paired.BaselineFold
import MaxCaterpillar.Fiber.Count65.Paired.CodeOffsets

/-! # Mixed weighted baselines for arbitrary invertible anchor codes

This supplies the explicit model bridge from the usual weighted baseline to
the physical safe-folding lemma. It does not assert connectivity of the
remaining arbitrary-width quadrant coefficient fiber.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineWeighted
open BigOperators Frontier BaselineFold

variable {m r : ℕ}

def anchorLeft (U : Fin 2 → Fin 2 → ℝ) (s : ℝ) : ℝ :=
  (s*U 1 1-(1-s)*U 1 0)/codeDet U

def anchorRight (U : Fin 2 → Fin 2 → ℝ) (s : ℝ) : ℝ :=
  ((1-s)*U 0 0-s*U 0 1)/codeDet U

lemma anchor_identity (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (x : Point 4) :
    anchorLeft U s*code U x 0+anchorRight U s*code U x 1=s*x 1+(1-s)*x 3 := by
  dsimp [anchorLeft,anchorRight,code]
  field_simp [hU]
  unfold codeDet
  ring

def weightedTarget (s : ℝ) (x : Point 4) : ℝ :=
  s*(relu (x 0-x 1)+x 1)+(1-s)*(relu (x 2-x 3)+x 3)

lemma weightedTarget_above_one (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (x : Point 4) :
    weightedTarget s x=target U s (s-1) (anchorLeft U s) (anchorRight U s) x := by
  dsimp [weightedTarget,target]
  linear_combination -(anchor_identity U hU s x)

lemma weightedTarget_below_zero (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (x : Point 4) :
    weightedTarget s x=(-1)*target U (-s) (1-s) (-anchorLeft U s) (-anchorRight U s) x := by
  dsimp [weightedTarget,target]
  linear_combination -(anchor_identity U hU s x)

/-- Every mixed weighted baseline over an invertible code is exactly in the
domain of the safe-folding theorem, in both possible increment orientations. -/
theorem mixed_weighted_normal_form (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (hs : s<0 ∨ 1<s) :
    ∃ A B c d ε : ℝ, 0<A ∧ 0<B ∧ (ε=1 ∨ ε=-1) ∧
      ∀ x, weightedTarget s x=ε*target U A B c d x := by
  rcases hs with hs|hs
  · refine ⟨-s,1-s,-anchorLeft U s,-anchorRight U s,-1,
      by linarith,by linarith,Or.inr rfl,?_⟩
    exact weightedTarget_below_zero U hU s
  · refine ⟨s,s-1,anchorLeft U s,anchorRight U s,1,
      by linarith,by linarith,Or.inl rfl,?_⟩
    intro x
    simpa only [one_mul] using weightedTarget_above_one U hU s x

/-- The physical coefficient homotopy exists for every mixed weighted
baseline completion. All source coefficients, including dormant gates and
biases, are arbitrary; the first layer and spectator rows remain fixed. -/
theorem mixed_weighted_joinedIn_exact (U : Fin 2 → Fin 2 → ℝ) (hU : codeDet U≠0)
    (s : ℝ) (hs : s<0 ∨ 1<s) (C : Fin m → Fin 6 → ℝ)
    (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ∀ x, (completion U C bias weights θ).eval x=weightedTarget s x)
    (rows : Fin r → Fin 6 → ℝ) (sbias sweights : Fin r → ℝ)
    (hsource : ∀ x,
      (Absorption.appendSpectators (completion U C bias weights θ) rows sbias sweights).eval x=
        Maximum 4 x) :
    ∃ A B c d ε : ℝ, 0<A ∧ 0<B ∧ (ε=1 ∨ ε=-1) ∧
      (∀ x, weightedTarget s x=ε*target U A B c d x) ∧
      JoinedIn (ExactSet 4 6 (m+r))
        (Absorption.appendSpectators (completion U C bias weights θ) rows sbias sweights)
        (withSpectators U A B c d C bias weights θ rows sbias sweights 1) := by
  obtain ⟨A,B,c,d,ε,hA,hB,hε,htarget⟩ := mixed_weighted_normal_form U hU s hs
  refine ⟨A,B,c,d,ε,hA,hB,hε,htarget,?_⟩
  have hfit' : ∀ x, (completion U C bias weights θ).eval x=ε*target U A B c d x := by
    intro x
    rw [hfit,htarget]
  have hsource' : ∀ x,
      (withSpectators U A B c d C bias weights θ rows sbias sweights 0).eval x=Maximum 4 x := by
    simpa only [withSpectators,foldedCompletion_zero] using hsource
  simpa only [withSpectators,foldedCompletion_zero] using
    withSpectators_smul_joinedIn_exact U A B c d ε hA hB C bias weights θ hfit'
      rows sbias sweights hsource'

end MaxCaterpillar.Fiber.Count65.Paired.BaselineWeighted
