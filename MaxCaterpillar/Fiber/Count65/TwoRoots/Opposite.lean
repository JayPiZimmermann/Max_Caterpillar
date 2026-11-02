import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # Opposite roots with the two C3-forced triple rows are impossible

Two explicit top facets suffice; there is no restriction on the decoder or
on second hidden width. Every remaining coefficient is an arbitrary real.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier

noncomputable def oppositeRows (a b c d e f : ℝ) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![-1,1,0,0], ![a,0,b,c], ![0,d,e,f]]

theorem opposite_roots_excluded (a b c d e f : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) (htsum : d+e+f = 0) :
    ¬ Represents (oppositeRows a b c d e f) := by
  rintro ⟨ell,Phi,h⟩
  have hepos : 0 < e := by
    by_contra hh
    have heneg : e < 0 := lt_of_le_of_ne (not_lt.mp hh) he
    let q : Point 4 := ![0,-1,0,-1]
    let w : Point 4 := ![c,c,0,-a]
    have htop0 : q 0 = Maximum 4 q := by norm_num [q,Maximum_four]
    have htop2 : q 2 = Maximum 4 q := by norm_num [q,Maximum_four]
    have hlast : lin (oppositeRows a b c d e f 3) q < 0 := by
      norm_num [lin_four,oppositeRows,q]
      linarith only [htsum,heneg]
    have hh := active_kernel_top_coordinates_eq (oppositeRows a b c d e f) ell Phi h q w
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four,oppositeRows,w]
        · norm_num [lin_four,oppositeRows,q] at hj
        · norm_num [lin_four,oppositeRows,w]; ring
        · exact False.elim (not_lt_of_ge hj hlast)) 0 2 htop0 htop2
    exact hc (by exact hh)
  let q : Point 4 := ![-1,0,-1,0]
  let w : Point 4 := ![b,b,-a,0]
  have htop1 : q 1 = Maximum 4 q := by norm_num [q,Maximum_four]
  have htop3 : q 3 = Maximum 4 q := by norm_num [q,Maximum_four]
  have hlast : lin (oppositeRows a b c d e f 3) q < 0 := by
    norm_num [lin_four,oppositeRows,q]
    exact hepos
  have hh := active_kernel_top_coordinates_eq (oppositeRows a b c d e f) ell Phi h q w
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,oppositeRows,q] at hj
      · norm_num [lin_four,oppositeRows,w]
      · norm_num [lin_four,oppositeRows,w]; ring
      · exact False.elim (not_lt_of_ge hj hlast)) 1 3 htop1 htop3
  exact hb (by exact hh)

#print axioms opposite_roots_excluded
end MaxCaterpillar.Fiber.Count65.TwoRoots
