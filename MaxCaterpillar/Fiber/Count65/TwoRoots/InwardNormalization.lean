import MaxCaterpillar.Fiber.Count65.TwoRoots.C3Normalization

/-! # Active-kernel normalization data for the remaining inward fork

Every sign and determinant below is forced by actual target facets. No
coefficient sign pattern, proportionality relation, or parameter bound is assumed.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.TwoRoots
open MaxCaterpillar.Frontier BigOperators

noncomputable def inwardRows (a b c d e f g : ℝ) : Fin 4 → Point 4 :=
  ![![1,-1,0,0],![0,-1,1,0],![a,0,b,c],![d,e,f,g]]

/-- On the target facet where both roots are inactive, the two nonroots
must span its normal. This explicitly gives the proportionality determinant. -/
theorem inward_determinant (a b c d e f g : ℝ)
    (h : Represents (inwardRows a b c d e f g)) : a*f-b*d=0 := by
  obtain ⟨ell,Phi,h⟩ := h
  have hh := active_kernel_top_coordinates_eq (inwardRows a b c d e f g) ell Phi h
    ![-1,0,-1,0] ![b*e,a*f-b*d,-a*e,0]
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,inwardRows] at hj
      · norm_num [lin_four,inwardRows] at hj
      · norm_num [lin_four,inwardRows] <;> ring
      · norm_num [lin_four,inwardRows] <;> ring)
    1 3 (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
  exact hh

/-- The other nonroot cannot omit the roots' shared coordinate as well. -/
theorem inward_second_center_ne_zero (a b c d e f g : ℝ)
    (h : Represents (inwardRows a b c d e f g)) : e ≠ 0 := by
  intro he
  obtain ⟨ell,Phi,h⟩ := h
  have hh := active_kernel_top_coordinates_eq (inwardRows a b c d e f g) ell Phi h
    ![-1,0,-1,0] ![0,1,0,0]
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,inwardRows] at hj
      · norm_num [lin_four,inwardRows] at hj
      · norm_num [lin_four,inwardRows]
      · norm_num [lin_four,inwardRows,he])
    1 3 (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
  norm_num at hh

lemma coefficient_nonpos_of_negative_ray (a b : ℝ)
    (h : ∀ u : ℝ,0<u → 0≤ -a*u-b) : a ≤ 0 := by
  by_contra hh
  have ha : 0<a := lt_of_not_ge hh
  let u : ℝ := (|b|+1)/a
  have hu : 0<u := div_pos (by positivity) ha
  have hm : a*u=|b|+1 := mul_div_cancel' _ ha.ne'
  have hp := h u hu
  have hb := neg_abs_le_self b
  nlinarith only [hm,hp,hb]

/-- The omitted-center nonroot has negative outer coefficients, with no
strict activity assumption or generic-facet restriction. -/
theorem inward_negative_coefficients (a b c d e f g : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : Nonroot ![d,e,f,g])
    (h : Represents (inwardRows a b c d e f g)) : a<0 ∧ b<0 := by
  have hn (u v : ℝ) (hu : 0<u) (hv : 0<v) : 0≤ -a*u-b*v := by
    have hh := third_nonneg_of_inactive_roots (inwardRows a b c d e f g) h
      ![-u,0,-v,0] 1 3 (by decide)
      (by norm_num [Maximum_four,max_eq_right (neg_nonpos.mpr hu.le),
        max_eq_right (neg_nonpos.mpr hv.le)])
      (by norm_num [Maximum_four,max_eq_right (neg_nonpos.mpr hu.le),
        max_eq_right (neg_nonpos.mpr hv.le)])
      (by simpa [lin_four,inwardRows] using neg_neg_of_pos hu)
      (by simpa [lin_four,inwardRows] using neg_neg_of_pos hv)
      (by exact ht)
    simpa [lin_four,inwardRows] using hh
  have hna : a≤0 := coefficient_nonpos_of_negative_ray a b (by
    intro u hu
    simpa using hn u 1 hu (by norm_num))
  have hnb : b≤0 := coefficient_nonpos_of_negative_ray b a (by
    intro u hu
    have hh := hn 1 u (by norm_num) hu
    nlinarith only [hh])
  exact ⟨lt_of_le_of_ne hna ha,lt_of_le_of_ne hnb hb⟩

/-- Complete coefficient data needed for positive scaling to the two-parameter
fork dictionary. The remaining conversion is exact algebra. -/
theorem inward_normalization_data (a b c d e f g : ℝ)
    (hsum : a+b+c=0) (htsum : d+e+f+g=0)
    (ha : a≠0) (hb : b≠0)
    (hs : Nonroot ![a,0,b,c]) (ht : Nonroot ![d,e,f,g])
    (h : Represents (inwardRows a b c d e f g)) :
    a<0 ∧ b<0 ∧ 0<c ∧ e≠0 ∧ a*f-b*d=0 ∧
      0<d/a ∧ d=a*(d/a) ∧ f=b*(d/a) := by
  have hneg := inward_negative_coefficients a b c d e f g ha hb ht h
  have hdet := inward_determinant a b c d e f g h
  have he := inward_second_center_ne_zero a b c d e f g h
  have hd : d≠0 := by
    intro hd
    have haf : a*f=0 := by simpa only [hd,mul_zero,sub_zero] using hdet
    have hf : f=0 := (mul_eq_zero.mp haf).resolve_left ha
    have htrow : ∑ i, (![d,e,f,g] : Point 4) i=0 := by
      simpa [Fin.sum_univ_succ,add_assoc] using htsum
    apply nonroot_not_supported_on_pair _ htrow ht 1 3 (by decide)
    intro l hl1 hl3
    fin_cases l
    · exact hd
    · exact False.elim (hl1 rfl)
    · exact hf
    · exact False.elim (hl3 rfl)
  have had : a*(d/a)=d := mul_div_cancel' _ ha
  have hbf : b*(d/a)=f := by
    apply mul_left_cancel₀ ha
    calc
      a*(b*(d/a)) = b*(a*(d/a)) := by ring
      _ = b*d := by rw [had]
      _ = a*f := by nlinarith only [hdet]
  have htn := nonroot_nonneg_of_two_possible (inwardRows a b c d e f g) h
    ![-1,0,-1,0] 1 3 3 2 (by decide)
    (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
    (by
      intro j hj3 hj2
      fin_cases j
      · norm_num [lin_four,inwardRows]
      · norm_num [lin_four,inwardRows]
      · exact False.elim (hj2 rfl)
      · exact False.elim (hj3 rfl)) (by exact hs)
  norm_num [lin_four,inwardRows] at htn
  have hm : 0≤(d/a)*(-a-b) := by nlinarith only [htn,had,hbf]
  have hpos : 0< -a-b := by linarith only [hneg.1,hneg.2]
  have hm' : 0≤(-a-b)*(d/a) := by simpa only [mul_comm] using hm
  have hratio : 0≤d/a := nonneg_of_mul_nonneg_right hm' hpos
  exact ⟨hneg.1,hneg.2,by linarith only [hsum,hneg.1,hneg.2],he,hdet,
    lt_of_le_of_ne hratio (Ne.symm (div_ne_zero hd ha)),had.symm,hbf.symm⟩

/-- Exact positive scaling parameters, derived from the facet conditions. -/
theorem inward_positive_scaling_parameters (a b c d e f g : ℝ)
    (hsum : a+b+c=0) (htsum : d+e+f+g=0)
    (ha : a≠0) (hb : b≠0) (hs : Nonroot ![a,0,b,c]) (ht : Nonroot ![d,e,f,g])
    (h : Represents (inwardRows a b c d e f g)) :
    ∃ α β κ lscale μ : ℝ, 0<α ∧ 0<β ∧ α+β=1 ∧ 0<lscale ∧ 0<μ ∧
      a= -lscale*α ∧ b= -lscale*β ∧ c=lscale ∧ d= -μ*α ∧ f= -μ*β ∧
      e=μ*(1-κ) ∧ g=μ*κ := by
  obtain ⟨han,hbn,hcp,_,_,hτ,hd,hf⟩ :=
    inward_normalization_data a b c d e f g hsum htsum ha hb hs ht h
  let α : ℝ := -a/c
  let β : ℝ := -b/c
  let μ : ℝ := (d/a)*c
  let κ : ℝ := g/μ
  have hμ : 0<μ := mul_pos hτ hcp
  have hαc : c*α= -a := mul_div_cancel' _ hcp.ne'
  have hβc : c*β= -b := mul_div_cancel' _ hcp.ne'
  have hαβ : α+β=1 := by
    apply mul_left_cancel₀ hcp.ne'
    calc
      c*(α+β) = c*α+c*β := by ring
      _ = -a-b := by rw [hαc,hβc]; ring
      _ = c*1 := by linarith only [hsum]
  have hd' : d= -μ*α := by
    calc
      d = a*(d/a) := hd
      _ = -(d/a)*(c*α) := by rw [hαc]; ring
      _ = -μ*α := by dsimp [μ]; ring
  have hf' : f= -μ*β := by
    calc
      f = b*(d/a) := hf
      _ = -(d/a)*(c*β) := by rw [hβc]; ring
      _ = -μ*β := by dsimp [μ]; ring
  have hg' : g=μ*κ := (mul_div_cancel' _ hμ.ne').symm
  have hdf : d+f= -μ := by
    calc
      d+f = a*(d/a)+b*(d/a) := congrArg₂ (fun x y : ℝ => x+y) hd hf
      _ = (a+b)*(d/a) := by ring
      _ = (-c)*(d/a) := by congr 1; linarith only [hsum]
      _ = -μ := by dsimp [μ]; ring
  have he' : e=μ*(1-κ) := by
    calc
      e = μ-g := by linarith only [htsum,hdf]
      _ = μ*(1-κ) := by rw [hg']; ring
  refine ⟨α,β,κ,c,μ,div_pos (neg_pos.mpr han) hcp,
    div_pos (neg_pos.mpr hbn) hcp,hαβ,hcp,hμ,?_,?_,rfl,hd',hf',he',hg'⟩
  · calc a = -(c*α) := by rw [hαc]; ring
         _ = -c*α := by ring
  · calc b = -(c*β) := by rw [hβc]; ring
         _ = -c*β := by ring

/-- The genuine inward dictionary is a positive row scaling of the normalized
fork, with the two parameters and the row scales derived rather than assumed. -/
theorem inward_normalizes_to_fork (a b c d e f g : ℝ)
    (hsum : a+b+c=0) (htsum : d+e+f+g=0)
    (ha : a≠0) (hb : b≠0) (hs : Nonroot ![a,0,b,c]) (ht : Nonroot ![d,e,f,g])
    (h : Represents (inwardRows a b c d e f g)) :
    ∃ α β κ : ℝ, ∃ scale : Fin 4 → ℝ,
      0<α ∧ 0<β ∧ α+β=1 ∧ (∀ j,0<scale j) ∧
      ∀ j,inwardRows a b c d e f g j=scale j • forkRows α β κ j := by
  obtain ⟨α,β,κ,lscale,μ,hα,hβ,hαβ,hlscale,hμ,ha',hb',hc',hd',hf',he',hg'⟩ :=
    inward_positive_scaling_parameters a b c d e f g hsum htsum ha hb hs ht h
  refine ⟨α,β,κ,![1,1,lscale,μ],hα,hβ,hαβ,?_,?_⟩
  · intro j
    fin_cases j
    · norm_num
    · norm_num
    · exact hlscale
    · exact hμ
  · intro j
    fin_cases j
    · funext i;fin_cases i <;> norm_num [inwardRows,forkRows]
    · funext i;fin_cases i <;> norm_num [inwardRows,forkRows]
    · funext i
      fin_cases i
      · change a=lscale*(-α); simpa [mul_neg] using ha'
      · change 0=lscale*(α+β-1); rw [hαβ]; ring
      · change b=lscale*(-β); simpa [mul_neg] using hb'
      · change c=lscale*1; simpa using hc'
    · funext i
      fin_cases i
      · change d=μ*(-α); simpa [mul_neg] using hd'
      · change e=μ*(α+β-κ); rw [hαβ]; exact he'
      · change f=μ*(-β); simpa [mul_neg] using hf'
      · change g=μ*κ; exact hg'

/-- Positive feature scalings can be absorbed in the arbitrary decoder. -/
theorem Represents.unscale {A B : Fin 4 → Point 4} (h : Represents A)
    (scale : Fin 4 → ℝ) (hscale : ∀ j,0<scale j)
    (hrows : ∀ j,A j=scale j • B j) : Represents B := by
  obtain ⟨ell,Phi,h⟩ := h
  refine ⟨ell,fun z => Phi (fun j => scale j*z j),fun x => ?_⟩
  have hstate : (fun j => relu (lin (A j) x)) =
      (fun j => scale j*relu (lin (B j) x)) := by
    funext j
    rw [hrows j,lin_smul_left,relu_mul_pos (hscale j)]
  exact (h x).trans (by rw [hstate])

/-- Equal nonroot features lose the top-tie normal when both roots are off. -/
theorem fork_kappa_ne_one (α β κ : ℝ) (hsum : α+β=1)
    (h : Represents (forkRows α β κ)) : κ≠1 := by
  intro hκ
  obtain ⟨ell,Phi,h⟩ := h
  have hh := active_kernel_top_coordinates_eq (forkRows α β κ) ell Phi h
    ![-1,0,-1,0] ![0,1,0,0]
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,forkRows] at hj
      · norm_num [lin_four,forkRows] at hj
      · norm_num [lin_four,forkRows,hsum]
      · norm_num [lin_four,forkRows,hsum,hκ])
    1 3 (by norm_num [Maximum_four]) (by norm_num [Maximum_four])
  norm_num at hh

/-- All parameters of the canonical inward fork, including its excluded
coincidence and both necessary facet bounds, follow from the original rows. -/
theorem inward_normalized_fork_constraints (a b c d e f g : ℝ)
    (hsum : a+b+c=0) (htsum : d+e+f+g=0)
    (ha : a≠0) (hb : b≠0) (hs : Nonroot ![a,0,b,c]) (ht : Nonroot ![d,e,f,g])
    (h : Represents (inwardRows a b c d e f g)) :
    ∃ α β κ : ℝ, ∃ scale : Fin 4 → ℝ,
      0<α ∧ 0<β ∧ α+β=1 ∧ (∀ j,0<scale j) ∧
      (∀ j,inwardRows a b c d e f g j=scale j • forkRows α β κ j) ∧
      max α β≤κ ∧ 0<κ ∧ κ≠1 ∧ Represents (forkRows α β κ) := by
  obtain ⟨α,β,κ,scale,hα,hβ,hαβ,hscale,hrows⟩ :=
    inward_normalizes_to_fork a b c d e f g hsum htsum ha hb hs ht h
  have hcanon := h.unscale scale hscale hrows
  have hbnd := fork_facet_bounds hα hβ hcanon
  exact ⟨α,β,κ,scale,hα,hβ,hαβ,hscale,hrows,hbnd.1,hbnd.2,
    fork_kappa_ne_one α β κ hαβ hcanon,hcanon⟩

#print axioms inward_normalized_fork_constraints
#print axioms inward_positive_scaling_parameters
#print axioms inward_normalizes_to_fork
#print axioms inward_normalization_data
end MaxCaterpillar.Fiber.Count65.TwoRoots
