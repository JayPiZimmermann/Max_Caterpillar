import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

/-!
# Local structure of a finite closed convex cover of `ℝ`

`exists_left_right_piece`: if finitely many closed convex sets (intervals) cover `ℝ`,
then at every point `t₀` there are a *left piece* containing `[t₀ - δ, t₀]` and a
*right piece* containing `[t₀, t₀ + δ]`, both containing `t₀`.

This is the structural heart of the one-dimensional difference-of-convex core
(`MaxNN/CPWL/Representation/DiffConvex/OneDim/Core.lean`): near any point, a
one-dimensional CPWL function is a two-piece function with a single kink.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

/-- At every point of a finite closed convex cover of `ℝ` there are a left and a right
piece: pieces containing a full closed segment on each side of the point. -/
theorem exists_left_right_piece {n : ℕ} (J : Fin n → Set ℝ)
    (hJc : ∀ i, IsClosed (J i)) (hJconv : ∀ i, Convex ℝ (J i))
    (hcover : ∀ t : ℝ, ∃ i, t ∈ J i) (t₀ : ℝ) :
    ∃ (L R : Fin n) (δ : ℝ), 0 < δ ∧ t₀ ∈ J L ∧ t₀ ∈ J R ∧
      Set.Icc (t₀ - δ) t₀ ⊆ J L ∧ Set.Icc t₀ (t₀ + δ) ⊆ J R := by
  -- pieces not containing `t₀` stay out of a small ball around it
  have hU : IsClosed (⋃ i : { i : Fin n // t₀ ∉ J i }, J i) :=
    isClosed_iUnion_of_finite fun i => hJc i
  have ht₀U : t₀ ∈ (⋃ i : { i : Fin n // t₀ ∉ J i }, J i)ᶜ := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact i.2 hi
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hU.isOpen_compl t₀ ht₀U
  have hnear : ∀ s : ℝ, |s - t₀| < δ₀ → ∃ i, t₀ ∈ J i ∧ s ∈ J i := by
    intro s hs
    obtain ⟨i, hi⟩ := hcover s
    by_cases h : t₀ ∈ J i
    · exact ⟨i, h, hi⟩
    · exfalso
      have hsball : s ∈ Metric.ball t₀ δ₀ := by
        rw [Metric.mem_ball, Real.dist_eq]
        exact hs
      exact hball hsball (Set.mem_iUnion.mpr ⟨⟨i, h⟩, hi⟩)
  obtain ⟨R, hR₀, hRs⟩ := hnear (t₀ + δ₀ / 2) (by
    rw [show t₀ + δ₀ / 2 - t₀ = δ₀ / 2 from by ring, abs_of_pos (by linarith)]
    linarith)
  obtain ⟨L, hL₀, hLs⟩ := hnear (t₀ - δ₀ / 2) (by
    rw [show t₀ - δ₀ / 2 - t₀ = -(δ₀ / 2) from by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith)
  refine ⟨L, R, δ₀ / 2, by linarith, hL₀, hR₀, ?_, ?_⟩
  · exact ((hJconv L).ordConnected).out hLs hL₀
  · exact ((hJconv R).ordConnected).out hR₀ hRs

end MaxNN
