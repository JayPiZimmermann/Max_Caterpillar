import MaxNN.CPWL.Representation.DiffConvex.OneDim.ConvexBricks
import MaxNN.CPWL.Representation.DiffConvex.OneDim.Engine
import MaxNN.CPWL.Representation.DiffConvex.OneDim.LeftRight
import Mathlib.Analysis.Convex.Normed

/-!
# The one-dimensional difference-of-convex core

`convexOn_pl_add_reluPairs`: a one-dimensional CPWL function `h` (agreeing with the
affine function `t ↦ c i * t + e i` on each member of a finite closed convex cover of
`ℝ`) becomes **convex** after adding the pair sum
`t ↦ ∑ (i,j), relu ((c i * t + e i) - (c j * t + e j))`.

Proof: by the local-to-global engine it suffices to be convex near each `t₀`.  By the
left/right structure lemma, near `t₀` the function `h` is a two-piece function with
pieces `ψ_L, ψ_R` from the family, agreeing at `t₀`.  If the kink is convex
(`c L ≤ c R`), then `h = max ψ_L ψ_R` locally and everything is convex.  If the kink
is concave, then `h = min ψ_L ψ_R` locally, and the two pair-sum terms indexed by
`(L,R)` and `(R,L)` absorb it: `min + relu(Δ) + relu(-Δ) = max`.

House style: no `simp`, no `sorry` (see `.claude/skills/formalization-conventions`).
-/

namespace MaxNN

open BigOperators

/-- Transfer convexity along a pointwise equality on the domain. -/
theorem convexOn_congr_on {D : Set ℝ} (hD : Convex ℝ D) {F G : ℝ → ℝ}
    (hFG : ∀ t ∈ D, F t = G t) (hF : ConvexOn ℝ D F) : ConvexOn ℝ D G := by
  refine ⟨hD, fun u hu w hw a b ha hb hab => ?_⟩
  rw [← hFG u hu, ← hFG w hw, ← hFG _ (hD hu hw ha hb hab)]
  exact hF.2 hu hw ha hb hab

/-- **One-dimensional difference-of-convex core.**  Adding the pair sum of `relu`s of
the differences of the affine pieces convexifies a one-dimensional CPWL function. -/
theorem convexOn_pl_add_reluPairs {n : ℕ} (J : Fin n → Set ℝ) (c e : Fin n → ℝ)
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hJc : ∀ i, IsClosed (J i)) (hJconv : ∀ i, Convex ℝ (J i))
    (hcover : ∀ t, ∃ i, t ∈ J i)
    (hagree : ∀ i, ∀ t ∈ J i, h t = c i * t + e i) :
    ConvexOn ℝ Set.univ (fun t => h t
      + ∑ p : Fin n × Fin n, relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2))) := by
  have hSconv : ∀ (s : Finset (Fin n × Fin n)) (D : Set ℝ), Convex ℝ D →
      ConvexOn ℝ D (fun t => ∑ p in s,
        relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2))) :=
    fun s D hD => convexOn_finset_sum hD s _
      fun p _ => convexOn_relu_affine_sub hD (c p.1) (e p.1) (c p.2) (e p.2)
  have hScont : Continuous fun t : ℝ =>
      ∑ p : Fin n × Fin n, relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)) := by
    refine continuous_finset_sum _ fun p _ => ?_
    show Continuous fun t : ℝ => max 0 ((c p.1 * t + e p.1) - (c p.2 * t + e p.2))
    exact continuous_const.max
      (((continuous_const.mul continuous_id).add continuous_const).sub
        ((continuous_const.mul continuous_id).add continuous_const))
  refine convexOn_univ_of_locally (hcont.add hScont) ?_
  intro t₀
  obtain ⟨L, R, δ, hδ, hL₀, hR₀, hIccL, hIccR⟩ :=
    exists_left_right_piece J hJc hJconv hcover t₀
  have hLt₀ : h t₀ = c L * t₀ + e L := hagree L t₀ hL₀
  have hRt₀ : h t₀ = c R * t₀ + e R := hagree R t₀ hR₀
  have heq0 : c L * t₀ + e L = c R * t₀ + e R := by linarith
  have hleft : ∀ t, t₀ - δ ≤ t → t ≤ t₀ → h t = c L * t + e L :=
    fun t h1 h2 => hagree L t (hIccL (Set.mem_Icc.mpr ⟨h1, h2⟩))
  have hright : ∀ t, t₀ ≤ t → t ≤ t₀ + δ → h t = c R * t + e R :=
    fun t h1 h2 => hagree R t (hIccR (Set.mem_Icc.mpr ⟨h1, h2⟩))
  have hmem : ∀ t ∈ Metric.ball t₀ δ, t₀ - δ ≤ t ∧ t ≤ t₀ + δ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    obtain ⟨h1, h2⟩ := abs_le.mp (le_of_lt ht)
    exact ⟨by linarith, by linarith⟩
  rcases le_or_lt (c L) (c R) with hc | hc
  · -- convex kink: `h = max ψL ψR` on the ball
    refine ⟨δ, hδ, ?_⟩
    refine convexOn_congr_on (convex_ball t₀ δ) ?_
      (ConvexOn.add (convexOn_max_affine1 (convex_ball t₀ δ) (c L) (e L) (c R) (e R))
        (hSconv Finset.univ _ (convex_ball t₀ δ)))
    intro t ht
    obtain ⟨ht1, ht2⟩ := hmem t ht
    show max (c L * t + e L) (c R * t + e R)
        + (∑ p : Fin n × Fin n, relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
      = h t + (∑ p : Fin n × Fin n, relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
    rcases le_total t t₀ with htt | htt
    · have hψ : c R * t + e R ≤ c L * t + e L := by
        have hprod : 0 ≤ (c R - c L) * (t₀ - t) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hprod, heq0]
      rw [max_eq_left hψ, hleft t ht1 htt]
    · have hψ : c L * t + e L ≤ c R * t + e R := by
        have hprod : 0 ≤ (c R - c L) * (t - t₀) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hprod, heq0]
      rw [max_eq_right hψ, hright t htt ht2]
  · -- concave kink: the (L,R) and (R,L) pair terms absorb it
    have hne : L ≠ R := by
      intro hLR
      rw [hLR] at hc
      exact lt_irrefl _ hc
    have hpairne : (R, L) ≠ (L, R) := by
      intro hp
      exact hne (congrArg Prod.fst hp).symm
    have hmem2 : (R, L) ∈ Finset.univ.erase (L, R) :=
      Finset.mem_erase.mpr ⟨hpairne, Finset.mem_univ _⟩
    have hsplit : ∀ t : ℝ,
        (∑ p : Fin n × Fin n, relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
        = relu ((c L * t + e L) - (c R * t + e R))
          + (relu ((c R * t + e R) - (c L * t + e L))
            + ∑ p in (Finset.univ.erase (L, R)).erase (R, L),
                relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2))) := by
      intro t
      rw [← Finset.add_sum_erase Finset.univ
          (fun p : Fin n × Fin n => relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
          (Finset.mem_univ (L, R)),
        ← Finset.add_sum_erase (Finset.univ.erase (L, R))
          (fun p : Fin n × Fin n => relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
          hmem2]
    refine ⟨δ, hδ, ?_⟩
    refine convexOn_congr_on (convex_ball t₀ δ) ?_
      (ConvexOn.add (convexOn_max_affine1 (convex_ball t₀ δ) (c L) (e L) (c R) (e R))
        (hSconv ((Finset.univ.erase (L, R)).erase (R, L)) _ (convex_ball t₀ δ)))
    intro t ht
    obtain ⟨ht1, ht2⟩ := hmem t ht
    show max (c L * t + e L) (c R * t + e R)
        + (∑ p in (Finset.univ.erase (L, R)).erase (R, L),
            relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
      = h t + (∑ p : Fin n × Fin n, relu ((c p.1 * t + e p.1) - (c p.2 * t + e p.2)))
    rw [hsplit t]
    have hmin : h t = min (c L * t + e L) (c R * t + e R) := by
      rcases le_total t t₀ with htt | htt
      · have hψ : c L * t + e L ≤ c R * t + e R := by
          have hprod : 0 ≤ (c L - c R) * (t₀ - t) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith [hprod, heq0]
        rw [hleft t ht1 htt, min_eq_left hψ]
      · have hψ : c R * t + e R ≤ c L * t + e L := by
          have hprod : 0 ≤ (c L - c R) * (t - t₀) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith [hprod, heq0]
        rw [hright t htt ht2, min_eq_right hψ]
    rw [hmin]
    have habs := min_add_relu_add_relu (c L * t + e L) (c R * t + e R)
    linarith [habs]

end MaxNN
