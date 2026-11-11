import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # The directed-path two-root branch: arbitrary-real facet obstructions -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier BigOperators

noncomputable def pathRows (a b c d e f g : ℝ) : Fin 4 → Point 4 :=
  ![![1,-1,0,0], ![0,1,-1,0], ![a,0,b,c], ![d,e,f,g]]

lemma path_c_negative (a b c d e f g : ℝ) (hc : c ≠ 0) (hg : g ≠ 0)
    (h : Represents (pathRows a b c d e f g)) : c < 0 := by
  have hn := row_nonneg_of_tie_kernel (pathRows a b c d e f g) h
    ![0,-1,0,-1] ![g,g,0,-(d+e)] 0 2 2
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four]) (by exact hg)
    (by
      intro j hj2 hj
      fin_cases j
      · norm_num [lin_four,pathRows] <;> ring
      · norm_num [lin_four,pathRows] at hj
      · exact False.elim (hj2 rfl)
      · norm_num [lin_four,pathRows] <;> ring)
  norm_num [lin_four,pathRows] at hn
  exact lt_of_le_of_ne (by linarith only [hn]) hc

/-- This covers every second nonroot having nonzero coordinates 0 and 3. -/
theorem directed_path_fullsupport_excluded (a b c d e f g : ℝ)
    (hsum : a+b+c = 0) (hc : c ≠ 0) (hd : d ≠ 0) (hg : g ≠ 0) :
    ¬ Represents (pathRows a b c d e f g) := by
  intro hh
  have hcneg := path_c_negative a b c d e f g hc hg hh
  obtain ⟨ell,Phi,h⟩ := hh
  have hs : lin (pathRows a b c d e f g 2) ![-1,0,-1,0] < 0 := by
    norm_num [lin_four,pathRows]
    linarith only [hsum,hcneg]
  have he := active_kernel_top_coordinates_eq (pathRows a b c d e f g) ell Phi h
    ![-1,0,-1,0] ![-(e+f),d,d,0]
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,pathRows] at hj
      · norm_num [lin_four,pathRows]
      · exact False.elim (not_lt_of_ge hj hs)
      · norm_num [lin_four,pathRows] <;> ring)
    1 3 (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
  exact hd (by exact he)

/-- The omitted-coordinate-0 boundary. All three entries of the other
nonroot are arbitrary nonzero reals. -/
theorem directed_path_zero0_excluded (a b c e f g : ℝ)
    (hsum : a+b+c = 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) :
    ¬ Represents (pathRows a b c 0 e f g) := by
  intro hh
  have hcneg := path_c_negative a b c 0 e f g hc hg hh
  have hbn := row_nonneg_of_tie_kernel (pathRows a b c 0 e f g) hh
    ![0,-2,-1,0] ![f,f,-e,0] 0 3 2
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four]) (by exact hf)
    (by
      intro j hj2 hj
      fin_cases j
      · norm_num [lin_four,pathRows]
      · norm_num [lin_four,pathRows] at hj
      · exact False.elim (hj2 rfl)
      · norm_num [lin_four,pathRows] <;> ring)
  have hbneg : b < 0 := by
    norm_num [lin_four,pathRows] at hbn
    exact lt_of_le_of_ne (by linarith only [hbn]) hb
  have hapos : 0 < a := by linarith only [hsum,hcneg,hbneg]
  obtain ⟨ell,Phi,h⟩ := hh
  have hs : lin (pathRows a b c 0 e f g 2) ![-2,-1,0,0] < 0 := by
    norm_num [lin_four,pathRows]
    linarith only [hapos]
  have het := active_kernel_top_coordinates_eq (pathRows a b c 0 e f g) ell Phi h
    ![-2,-1,0,0] ![0,-f,e,0]
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,pathRows] at hj
      · norm_num [lin_four,pathRows] at hj
      · exact False.elim (not_lt_of_ge hj hs)
      · norm_num [lin_four,pathRows] <;> ring)
    2 3 (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
  exact he (by exact het)

/-- The omitted-coordinate-3 boundary. The facet argument does not require
sign hypotheses on any coefficient. -/
theorem directed_path_zero3_excluded (a b c d e f : ℝ)
    (htsum : d+e+f = 0) (ha : a ≠ 0) (hb : b ≠ 0) (he : e ≠ 0) :
    ¬ Represents (pathRows a b c d e f 0) := by
  intro hh
  have hen := row_nonneg_of_tie_kernel (pathRows a b c d e f 0) hh
    ![-1,0,-1,0] ![-b,a,a,0] 1 3 3
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four]) (by exact ha)
    (by
      intro j hj3 hj
      fin_cases j
      · norm_num [lin_four,pathRows] at hj
      · norm_num [lin_four,pathRows]
      · norm_num [lin_four,pathRows] <;> ring
      · exact False.elim (hj3 rfl))
  have hepos : 0 < e := by
    norm_num [lin_four,pathRows] at hen
    exact lt_of_le_of_ne (by linarith only [hen,htsum]) (Ne.symm he)
  let u : ℝ := max 2 ((1-f)/e)
  have hu : 1 < u := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have humul : 1-f ≤ u*e := (div_le_iff hepos).mp (le_max_right _ _)
  have htneg : lin (pathRows a b c d e f 0 3) ![0,-u,-1,0] < 0 := by
    norm_num [lin_four,pathRows]
    nlinarith only [humul]
  obtain ⟨ell,Phi,h⟩ := hh
  have het := active_kernel_top_coordinates_eq (pathRows a b c d e f 0) ell Phi h
    ![0,-u,-1,0] ![b,b,-a,0]
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,pathRows]
      · norm_num [lin_four,pathRows] at hj <;>
        linarith only [hu,hj]
      · norm_num [lin_four,pathRows] <;> ring
      · exact False.elim (not_lt_of_ge hj htneg))
    0 3 (by norm_num [Maximum_four,max_eq_left (by linarith only [hu] : -u ≤ 0)])
      (by norm_num [Maximum_four,max_eq_left (by linarith only [hu] : -u ≤ 0)])
  exact hb (by exact het)

lemma triple_nonzero_of_nonroot (e f g : ℝ) (hsum : e+f+g = 0)
    (h : Nonroot ![0,e,f,g]) : e ≠ 0 ∧ f ≠ 0 ∧ g ≠ 0 := by
  have hsum' : ∑ l, (![0,e,f,g] : Point 4) l = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hsum
  refine ⟨?_,?_,?_⟩
  · intro he
    apply nonroot_not_supported_on_pair _ hsum' h 2 3 (by decide)
    intro l hl2 hl3
    fin_cases l
    · rfl
    · exact he
    · exact False.elim (hl2 rfl)
    · exact False.elim (hl3 rfl)
  · intro hf
    apply nonroot_not_supported_on_pair _ hsum' h 1 3 (by decide)
    intro l hl1 hl3
    fin_cases l
    · rfl
    · exact False.elim (hl1 rfl)
    · exact hf
    · exact False.elim (hl3 rfl)
  · intro hg
    apply nonroot_not_supported_on_pair _ hsum' h 1 2 (by decide)
    intro l hl1 hl2
    fin_cases l
    · rfl
    · exact False.elim (hl1 rfl)
    · exact False.elim (hl2 rfl)
    · exact hg

/-- All support-three/support-four boundaries for the other nonroot are
included. The first nonroot is the C3-forced row omitting coordinate 1. -/
theorem directed_path_excluded (a b c d e f g : ℝ)
    (hsum : a+b+c = 0) (htsum : d+e+f+g = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ht : Nonroot ![d,e,f,g]) : ¬ Represents (pathRows a b c d e f g) := by
  by_cases hd : d = 0
  · subst d
    have htr := triple_nonzero_of_nonroot e f g (by linarith only [htsum]) ht
    exact directed_path_zero0_excluded a b c e f g hsum hb hc htr.1 htr.2.1 htr.2.2
  by_cases hg : g = 0
  · subst g
    have he : e ≠ 0 := by
      intro he
      have hsum' : ∑ l, (![d,e,f,0] : Point 4) l = 0 := by
        simpa [Fin.sum_univ_succ,add_assoc] using htsum
      apply nonroot_not_supported_on_pair _ hsum' ht 0 2 (by decide)
      intro l hl0 hl2
      fin_cases l
      · exact False.elim (hl0 rfl)
      · exact he
      · exact False.elim (hl2 rfl)
      · rfl
    exact directed_path_zero3_excluded a b c d e f (by linarith only [htsum]) ha hb he
  exact directed_path_fullsupport_excluded a b c d e f g hsum hc hd hg

#print axioms directed_path_excluded
#print axioms directed_path_fullsupport_excluded
#print axioms directed_path_zero0_excluded
#print axioms directed_path_zero3_excluded
end MaxCaterpillar.Fiber.Count65.TwoRoots
