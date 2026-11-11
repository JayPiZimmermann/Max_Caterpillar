import MaxCaterpillar.Fiber.Count65.TwoInvariantPairing.PairedWallGeometry
import MaxCaterpillar.Fiber.Count65.RootFrames

/-! # Actual carrier support at the paired four-invariant-row wall

The hypotheses are exactness, the actual invariant-row count, and the finite
root-frame classification branch. No matrix normal form is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65
open BigOperators Frontier
variable {h₂ : ℕ}

/-- Translate the finite root dictionary to its four real covector rays. -/
lemma paired_frame_roots (net : Network 4 6 h₂) (q : Equiv.Perm (Fin 4))
    (hroots : ∀ j, (∑ i, net.W₁ j i) = 0 →
      ∃ r ∈ RootFrames.pairedFrame (q : Fin 4 → Fin 4),
        ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • RootFrames.row r) :
    ∀ j, net.toZ.s j = 0 →
      (∃ c : ℝ, 0 < c ∧ net.toZ.A j = c • (unitVec (q 0) - unitVec (q 1))) ∨
      (∃ c : ℝ, 0 < c ∧ net.toZ.A j = c • (unitVec (q 2) - unitVec (q 3))) ∨
      (∃ c : ℝ, 0 < c ∧ net.toZ.A j = c • (unitVec (q 1) - unitVec (q 3))) ∨
      (∃ c : ℝ, 0 < c ∧ net.toZ.A j = c • (unitVec (q 3) - unitVec (q 1))) := by
  intro j hj
  obtain ⟨r,hr,c,hc,he⟩ := hroots j hj
  have hrow (a b : Fin 4) : RootFrames.row (a,b) = unitVec a - unitVec b := by
    rfl
  simp only [RootFrames.pairedFrame, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨c,hc,he.trans (congrArg (fun v => c • v) (hrow _ _))⟩
  · exact Or.inr (Or.inl ⟨c,hc,he.trans (congrArg (fun v => c • v) (hrow _ _))⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c,hc,he.trans (congrArg (fun v => c • v) (hrow _ _))⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c,hc,he.trans (congrArg (fun v => c • v) (hrow _ _))⟩))

/-- Both actual non-invariant first rows lie in the two-anchor plane. Biases
and the second hidden width are unrestricted. -/
theorem paired_wall_actual_carrier_plane (net : Network 4 6 h₂)
    (hnet : ∀ x, net.eval x = Maximum 4 x)
    (hcard : (Finset.univ.filter fun j => (∑ i, net.W₁ j i) = 0).card = 4)
    (q : Equiv.Perm (Fin 4))
    (hroots : ∀ j, (∑ i, net.W₁ j i) = 0 →
      ∃ r ∈ RootFrames.pairedFrame (q : Fin 4 → Fin 4),
        ∃ c : ℝ, 0 < c ∧ net.W₁ j = c • RootFrames.row r) :
    ∀ j, (∑ i, net.W₁ j i) ≠ 0 →
      ∀ i, i ≠ q 1 → i ≠ q 3 → net.W₁ j i = 0 := by
  obtain ⟨p,n,c,hpn,hc,hp,hn,hopp,hother⟩ :=
    max4_four_invariant_rows_have_opposite_carriers net hnet hcard
  have huniq : ∀ j, 0 < (1 : ℝ) * net.toZ.s j → j = p := by
    intro j hj
    have hj' : 0 < ∑ i, net.W₁ j i := by simpa using hj
    by_contra hjp
    by_cases hjn : j = n
    · subst j
      linarith
    · rw [hother j hjp hjn] at hj'
      exact (lt_irrefl 0 hj')
  have hplane := paired_wall_carrier_plane net.toZ (net.toZ_eval_of_max hnet)
    (q 0) (q 1) (q 2) (q 3)
    (q.injective.ne (by decide)) (q.injective.ne (by decide))
    (q.injective.ne (by decide)) (q.injective.ne (by decide))
    (q.injective.ne (by decide)) (paired_frame_roots net q hroots)
    1 one_ne_zero p huniq
  intro j hj i hi₁ hi₃
  by_cases hjp : j = p
  · subst j
    exact hplane i hi₁ hi₃
  · have hjn : j = n := by
      by_contra hjn
      exact hj (hother j hjp hjn)
    subst j
    rw [hopp]
    have hw₀ : net.W₁ p i = 0 := hplane i hi₁ hi₃
    simp only [Pi.smul_apply, smul_eq_mul, hw₀, mul_zero]

#check @paired_wall_actual_carrier_plane
#print axioms paired_wall_actual_carrier_plane
end MaxCaterpillar.Fiber.Count65
