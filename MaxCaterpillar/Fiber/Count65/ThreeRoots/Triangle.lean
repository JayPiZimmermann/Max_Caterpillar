import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # Three triangle roots cannot accompany a nonroot observation

The decoder is arbitrary. The two triangle orientations are excluded directly
by invisible perturbations at strict root gates on target top-tie facets.
The fourth observation may have any real coefficients and may vanish at the
chosen points; its perturbation is always annihilated explicitly.
-/

set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ThreeRoots
open MaxCaterpillar.Frontier BigOperators
open MaxCaterpillar.Fiber.Count65.TwoRoots

noncomputable def transitiveTriangleRows (t : Point 4) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![0,1,-1,0], ![1,0,-1,0], t]

noncomputable def cyclicTriangleRows (t : Point 4) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![0,1,-1,0], ![-1,0,1,0], t]

/-- A transitive root triangle erases a top-tie normal unless its fourth
observation is itself a coordinate root. No coefficient or decoder restriction
is imposed. -/
theorem not_represents_transitive_triangle (t : Point 4) (ht : Nonroot t) :
    ¬ Represents (transitiveTriangleRows t) := by
  intro h
  let q : Point 4 := ![-2,-1,0,0]
  apply not_one_active_nonroot (transitiveTriangleRows t) h q 2 3 3
    (by decide) (by norm_num [q, Maximum_four])
    (by norm_num [q, Maximum_four]) _ (by exact ht)
  intro j hj
  fin_cases j
  · norm_num [lin_four, transitiveTriangleRows, q]
  · norm_num [lin_four, transitiveTriangleRows, q]
  · norm_num [lin_four, transitiveTriangleRows, q]
  · exact False.elim (hj rfl)

/-- An arbitrary decoder of a cyclic triangle and a fourth row can retain
the two displayed target-tie normals only if that row has two zero entries. -/
theorem cyclic_triangle_forced_zeros (t : Point 4)
    (h : Represents (cyclicTriangleRows t)) : t 2 = 0 ∧ t 0 = 0 := by
  obtain ⟨ell,Phi,h⟩ := h
  constructor
  · let q : Point 4 := ![0,-2,-1,0]
    let w : Point 4 := ![0,0,t 3,-t 2]
    have he := active_kernel_top_coordinates_eq (cyclicTriangleRows t) ell Phi h q w
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four, cyclicTriangleRows, w]
        · have hn : lin (cyclicTriangleRows t 1) q < 0 := by
            norm_num [lin_four, cyclicTriangleRows, q]
          exact False.elim (not_lt_of_ge hj hn)
        · have hn : lin (cyclicTriangleRows t 2) q < 0 := by
            norm_num [lin_four, cyclicTriangleRows, q]
          exact False.elim (not_lt_of_ge hj hn)
        · change lin t w = 0
          rw [lin_four]
          change t 0*0+t 1*0+t 2*t 3+t 3*(-t 2) = 0
          ring)
      0 3 (by norm_num [q, Maximum_four]) (by norm_num [q, Maximum_four])
    change (0 : ℝ) = -t 2 at he
    linarith only [he]
  · let q : Point 4 := ![-1,0,-2,0]
    let w : Point 4 := ![t 3,0,0,-t 0]
    have he := active_kernel_top_coordinates_eq (cyclicTriangleRows t) ell Phi h q w
      (fun j hj => by
        fin_cases j
        · have hn : lin (cyclicTriangleRows t 0) q < 0 := by
            norm_num [lin_four, cyclicTriangleRows, q]
          exact False.elim (not_lt_of_ge hj hn)
        · norm_num [lin_four, cyclicTriangleRows, w]
        · have hn : lin (cyclicTriangleRows t 2) q < 0 := by
            norm_num [lin_four, cyclicTriangleRows, q]
          exact False.elim (not_lt_of_ge hj hn)
        · change lin t w = 0
          rw [lin_four]
          change t 0*t 3+t 1*0+t 2*0+t 3*(-t 0) = 0
          ring)
      1 3 (by norm_num [q, Maximum_four]) (by norm_num [q, Maximum_four])
    change (0 : ℝ) = -t 0 at he
    linarith only [he]

/-- A zero-sum nonroot cannot accompany the three cyclic triangle roots.
The conclusion is independent of second-layer width and decoder regularity. -/
theorem not_represents_cyclic_triangle (t : Point 4)
    (hsum : ∑ i, t i = 0) (ht : Nonroot t) :
    ¬ Represents (cyclicTriangleRows t) := by
  intro h
  obtain ⟨h2,h0⟩ := cyclic_triangle_forced_zeros t h
  apply nonroot_not_supported_on_pair t hsum ht 1 3 (by decide)
  intro i hi1 hi3
  fin_cases i
  · exact h0
  · exact False.elim (hi1 rfl)
  · exact h2
  · exact False.elim (hi3 rfl)

#print axioms not_represents_transitive_triangle
#print axioms cyclic_triangle_forced_zeros
#print axioms not_represents_cyclic_triangle
end MaxCaterpillar.Fiber.Count65.ThreeRoots
