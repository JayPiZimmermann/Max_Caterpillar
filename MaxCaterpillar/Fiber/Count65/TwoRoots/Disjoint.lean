import MaxCaterpillar.Fiber.Count65.TwoRoots.Outward

/-! # Disjoint roots and two nonroots lose a target-tie normal

The proof uses only the arbitrary-decoder factorization and active kernels.
It does not need positive homogeneity of the decoder.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier BigOperators

noncomputable def disjointRows (s t : Point 4) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![0,0,1,-1],s,t]

lemma positive_at_disjoint_anchor (s : Point 4) (hsum : ∑ i, s i = 0)
    (hs : Nonroot s)
    (hn : ∀ u v : ℝ, 0 < u → 0 < v → 0 ≤ lin s ![-u,0,-v,0]) :
    0 < lin s ![-1,0,-1,0] := by
  have h0 := hn 1 1 (by norm_num) (by norm_num)
  by_contra hh
  have hz : lin s ![-1,0,-1,0] = 0 := le_antisymm (not_lt.mp hh) h0
  have h1 := hn 2 1 (by norm_num) (by norm_num)
  have h2 := hn 1 2 (by norm_num) (by norm_num)
  norm_num [lin_four] at hz h1 h2
  have hs0 : s 0 = 0 := by linarith only [hz,h1,h2]
  have hs2 : s 2 = 0 := by linarith only [hz,h1,h2]
  apply nonroot_not_supported_on_pair s hsum hs 1 3 (by decide)
  intro l hl1 hl3
  fin_cases l
  · exact hs0
  · exact False.elim (hl1 rfl)
  · exact hs2
  · exact False.elim (hl3 rfl)

theorem disjoint_roots_excluded (s t : Point 4)
    (hsum : ∑ i, s i = 0) (htsum : ∑ i, t i = 0)
    (hs : Nonroot s) (ht : Nonroot t) : ¬ Represents (disjointRows s t) := by
  intro h
  have hn (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      0 ≤ lin s ![-u,0,-v,0] ∧ 0 ≤ lin t ![-u,0,-v,0] := by
    let q : Point 4 := ![-u,0,-v,0]
    have hi : q 1 = Maximum 4 q := by
      norm_num [q,Maximum_four,max_eq_right (neg_nonpos.mpr hu.le),
        max_eq_right (neg_nonpos.mpr hv.le)]
    have hk : q 3 = Maximum 4 q := by exact hi
    have hinactive : ∀ j : Fin 4, j ≠ 2 → j ≠ 3 →
        lin (disjointRows s t j) q < 0 := by
      intro j hj2 hj3
      fin_cases j
      · simpa [lin_four,disjointRows,q] using neg_neg_of_pos hu
      · simpa [lin_four,disjointRows,q] using neg_neg_of_pos hv
      · exact False.elim (hj2 rfl)
      · exact False.elim (hj3 rfl)
    constructor
    · exact nonroot_nonneg_of_two_possible _ h q 1 3 2 3 (by decide) hi hk
        hinactive (by simpa [disjointRows] using ht)
    · exact nonroot_nonneg_of_two_possible _ h q 1 3 3 2 (by decide) hi hk
        (fun j hj3 hj2 => hinactive j hj2 hj3) (by simpa [disjointRows] using hs)
  have hsp := positive_at_disjoint_anchor s hsum hs (fun u v hu hv => (hn u v hu hv).1)
  have htp := positive_at_disjoint_anchor t htsum ht (fun u v hu hv => (hn u v hu hv).2)
  obtain ⟨ell,Phi,h⟩ := h
  let q : Point 4 := ![1,0,1,0]
  let w : Point 4 := ![1,1,0,0]
  have hsq : lin s q < 0 := by
    norm_num [lin_four] at hsp
    norm_num [lin_four,q]
    linarith only [hsp]
  have htq : lin t q < 0 := by
    norm_num [lin_four] at htp
    norm_num [lin_four,q]
    linarith only [htp]
  have hi : q 0 = Maximum 4 q := by norm_num [q,Maximum_four]
  have hk : q 2 = Maximum 4 q := by norm_num [q,Maximum_four]
  have he := active_kernel_top_coordinates_eq (disjointRows s t) ell Phi h q w
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,disjointRows,w]
      · norm_num [lin_four,disjointRows,w]
      · exact False.elim (not_lt_of_ge hj hsq)
      · exact False.elim (not_lt_of_ge hj htq)) 0 2 hi hk
  norm_num [w] at he

#print axioms disjoint_roots_excluded
end MaxCaterpillar.Fiber.Count65.TwoRoots
