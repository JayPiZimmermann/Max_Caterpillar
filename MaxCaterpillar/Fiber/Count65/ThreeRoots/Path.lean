import MaxCaterpillar.Fiber.Count65.TwoRoots.OneActive

/-! # Three path roots and an arbitrary fourth row

The decoder is unrestricted. All conclusions hold even when the fourth row
vanishes on the selected facet: the kernel argument includes boundary rows.
-/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.Count65.ThreeRoots
open MaxCaterpillar.Frontier MaxCaterpillar.Fiber.Count65.TwoRoots
open BigOperators

noncomputable def pathFourth (a b c : ℝ) : Point 4 := ![a,b-a,c-b,-c]

noncomputable def pathRows (s₀ s₁ s₂ : Bool) (a b c : ℝ) : Fin 4 → Point 4 :=
  ![![(if s₀ then 1 else -1),(if s₀ then -1 else 1),0,0],
    ![0,(if s₁ then 1 else -1),(if s₁ then -1 else 1),0],
    ![0,0,(if s₂ then 1 else -1),(if s₂ then -1 else 1)],
    pathFourth a b c]

/-- Every zero-sum fourth row is included, with no rationality or support
restriction. These are its unique coefficients in the three-edge basis. -/
theorem zero_sum_eq_pathFourth (t : Point 4) (hsum : ∑ i, t i = 0) :
    t = pathFourth (t 0) (t 0+t 1) (-t 3) := by
  have hs : t 0+t 1+t 2+t 3=0 := by
    simpa [Fin.sum_univ_succ,add_assoc,
      show (Fin.succ (2 : Fin 3) : Fin 4)=3 from rfl] using hsum
  funext i
  fin_cases i
  · rfl
  · change t 1 = t 0+t 1-t 0
    ring
  · change t 2 = -t 3-(t 0+t 1)
    linarith only [hs]
  · change t 3 = -(-t 3)
    ring

private theorem kernel_tie (A : Fin 4 → Point 4) (h : Represents A)
    (q w : Point 4) (i k : Fin 4)
    (hi : q i = Maximum 4 q) (hk : q k = Maximum 4 q)
    (hw : ∀ j, 0 ≤ lin (A j) q → lin (A j) w = 0) : w i = w k := by
  obtain ⟨ell,Phi,h⟩ := h
  exact active_kernel_top_coordinates_eq A ell Phi h q w hw i k hi hk

private theorem maxA : Maximum 4 (![(-1:ℝ),0,-2,0]) = 0 := by norm_num [Maximum_four]
private theorem maxB : Maximum 4 (![(0:ℝ),-2,-1,0]) = 0 := by norm_num [Maximum_four]
private theorem maxC : Maximum 4 (![(0:ℝ),-1,0,-2]) = 0 := by norm_num [Maximum_four]
private theorem maxD : Maximum 4 (![(0:ℝ),-1,-2,0]) = 0 := by norm_num [Maximum_four]

/-- With only the first root active at facet C, the fourth row has no
component along the last path edge. -/
theorem path_ppm_last_zero (a b c : ℝ)
    (h : Represents (pathRows true true false a b c)) : c = 0 := by
  let q : Point 4 := ![0,-1,0,-2]
  let w : Point 4 := ![c-b,c-b,-b,0]
  have he := kernel_tie _ h q w 0 2
    (by simpa [q] using maxC.symm) (by simpa [q] using maxC.symm)
    (fun j hj => by
      fin_cases j
      · simp [lin_four,pathRows,w]
      · norm_num [lin_four,pathRows,q] at hj
      · norm_num [lin_four,pathRows,q] at hj
      · simp [lin_four,pathRows,pathFourth,w]; ring)
  change c-b = -b at he
  linarith only [he]

/-- The reversed surviving orientation has no component on its first edge. -/
theorem path_pmm_first_zero (a b c : ℝ)
    (h : Represents (pathRows true false false a b c)) : a = 0 := by
  let q : Point 4 := ![-1,0,-2,0]
  let w : Point 4 := ![b-a,-a,0,0]
  have he := kernel_tie _ h q w 1 3
    (by simpa [q] using maxA.symm) (by simpa [q] using maxA.symm)
    (fun j hj => by
      fin_cases j
      · norm_num [lin_four,pathRows,q] at hj
      · norm_num [lin_four,pathRows,q] at hj
      · simp [lin_four,pathRows,w]
      · simp [lin_four,pathRows,pathFourth,w]; ring)
  change -a = 0 at he
  linarith only [he]

private theorem ppp_constraints (a b c : ℝ)
    (h : Represents (pathRows true true true a b c)) : a = 0 ∧ b = c := by
  have hbc : b = c := by
    let q : Point 4 := ![0,-2,-1,0]
    let w : Point 4 := ![c-b,c-b,-b,0]
    have he := kernel_tie _ h q w 0 3
      (by simpa [q] using maxB.symm) (by simpa [q] using maxB.symm)
      (fun j hj => by
        fin_cases j
        · simp [lin_four,pathRows,w]
        · norm_num [lin_four,pathRows,q] at hj
        · norm_num [lin_four,pathRows,q] at hj
        · simp [lin_four,pathRows,pathFourth,w]; ring)
    change c-b = 0 at he
    linarith only [he]
  have ha : a = 0 := by
    let q : Point 4 := ![-1,0,-2,0]
    let w : Point 4 := ![c-a,-a,-a,0]
    have he := kernel_tie _ h q w 1 3
      (by simpa [q] using maxA.symm) (by simpa [q] using maxA.symm)
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four,pathRows,q] at hj
        · simp [lin_four,pathRows,w]
        · norm_num [lin_four,pathRows,q] at hj
        · simp [lin_four,pathRows,pathFourth,w]; ring)
    change -a = 0 at he
    linarith only [he]
  exact ⟨ha,hbc⟩

private theorem mmm_constraints (a b c : ℝ)
    (h : Represents (pathRows false false false a b c)) : c = 0 ∧ a = b := by
  have hc : c = 0 := by
    let q : Point 4 := ![0,-1,0,-2]
    let w : Point 4 := ![c-a,-a,-a,0]
    have he := kernel_tie _ h q w 0 2
      (by simpa [q] using maxC.symm) (by simpa [q] using maxC.symm)
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four,pathRows,q] at hj
        · simp [lin_four,pathRows,w]
        · norm_num [lin_four,pathRows,q] at hj
        · simp [lin_four,pathRows,pathFourth,w]; ring)
    change c-a = -a at he
    linarith only [he]
  have hab : a = b := by
    let q : Point 4 := ![0,-1,-2,0]
    let w : Point 4 := ![b-a,-a,0,0]
    have he := kernel_tie _ h q w 0 3
      (by simpa [q] using maxD.symm) (by simpa [q] using maxD.symm)
      (fun j hj => by
        fin_cases j
        · norm_num [lin_four,pathRows,q] at hj
        · norm_num [lin_four,pathRows,q] at hj
        · simp [lin_four,pathRows,w]
        · simp [lin_four,pathRows,pathFourth,w]; ring)
    change b-a = 0 at he
    linarith only [he]
  exact ⟨hc,hab⟩

private theorem no_roots_at_A (a b c : ℝ)
    (h : Represents (pathRows true false true a b c))
    (ht : Nonroot (pathFourth a b c)) : False := by
  apply not_one_active_nonroot _ h ![-1,0,-2,0] 1 3 3 (by decide)
    (by simpa using maxA.symm) (by simpa using maxA.symm) _ ht
  intro j hj
  fin_cases j
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · exact False.elim (hj rfl)

private theorem no_roots_at_B (a b c : ℝ)
    (h : Represents (pathRows false true true a b c))
    (ht : Nonroot (pathFourth a b c)) : False := by
  apply not_one_active_nonroot _ h ![0,-2,-1,0] 0 3 3 (by decide)
    (by simpa using maxB.symm) (by simpa using maxB.symm) _ ht
  intro j hj
  fin_cases j
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · exact False.elim (hj rfl)

private theorem no_roots_at_C (a b c : ℝ)
    (h : Represents (pathRows false true false a b c))
    (ht : Nonroot (pathFourth a b c)) : False := by
  apply not_one_active_nonroot _ h ![0,-1,0,-2] 0 2 3 (by decide)
    (by simpa using maxC.symm) (by simpa using maxC.symm) _ ht
  intro j hj
  fin_cases j
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · exact False.elim (hj rfl)

private theorem no_roots_at_D (a b c : ℝ)
    (h : Represents (pathRows false false true a b c))
    (ht : Nonroot (pathFourth a b c)) : False := by
  apply not_one_active_nonroot _ h ![0,-1,-2,0] 0 3 3 (by decide)
    (by simpa using maxD.symm) (by simpa using maxD.symm) _ ht
  intro j hj
  fin_cases j
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · norm_num [lin_four,pathRows]
  · exact False.elim (hj rfl)

/-- Complete orientation-and-span necessity, with arbitrary real fourth-row
coefficients and an arbitrary decoder. The two alternatives are path reversals. -/
theorem path_orientation_and_span (s₀ s₁ s₂ : Bool) (a b c : ℝ)
    (h : Represents (pathRows s₀ s₁ s₂ a b c))
    (ht : Nonroot (pathFourth a b c)) :
    (s₀ = true ∧ s₁ = true ∧ s₂ = false ∧ c = 0) ∨
    (s₀ = true ∧ s₁ = false ∧ s₂ = false ∧ a = 0) := by
  cases s₀ <;> cases s₁ <;> cases s₂
  · obtain ⟨hc,hab⟩ := mmm_constraints a b c h
    apply False.elim
    apply ht 0 2 (by decide)
    refine ⟨a,?_⟩
    intro l; fin_cases l <;> norm_num [pathFourth,hc,hab,Fin.ext_iff]
  · exact False.elim (no_roots_at_D a b c h ht)
  · exact False.elim (no_roots_at_C a b c h ht)
  · exact False.elim (no_roots_at_B a b c h ht)
  · exact Or.inr ⟨rfl,rfl,rfl,path_pmm_first_zero a b c h⟩
  · exact False.elim (no_roots_at_A a b c h ht)
  · exact Or.inl ⟨rfl,rfl,rfl,path_ppm_last_zero a b c h⟩
  · obtain ⟨ha,hbc⟩ := ppp_constraints a b c h
    apply False.elim
    apply ht 1 3 (by decide)
    refine ⟨b,?_⟩
    intro l; fin_cases l <;> norm_num [pathFourth,ha,hbc,Fin.ext_iff,show (3 : Fin 4).val = 3 from rfl]

/-- The whole open top-tie facet is retained, including every possible
fourth-row activation boundary. -/
theorem path_ppm_facet_nonnegative (a b u v : ℝ)
    (h : Represents (pathRows true true false a b 0))
    (hu : 0 < u) (hv : v < 0) : 0 ≤ a*u+(b-a)*v := by
  let q : Point 4 := ![u,v,0,u]
  let w : Point 4 := ![1,1,0,0]
  have hmax : Maximum 4 q = u := by
    rw [Maximum_four]
    change max (max u v) (max 0 u) = u
    rw [show max u v = u from max_eq_left (by linarith only [hu,hv]),
      show max 0 u = u from max_eq_right hu.le,max_self]
  have hh := row_nonneg_of_tie_kernel _ h q w 0 3 3
    (by simpa [q] using hmax.symm) (by simpa [q] using hmax.symm)
    (by norm_num [w]) (fun j hj hn => by
      fin_cases j
      · norm_num [lin_four,pathRows,w]
      · have : ¬ 0 ≤ v := not_le_of_gt hv
        apply False.elim; apply this
        simpa [lin_four,pathRows,q] using hn
      · norm_num [lin_four,pathRows,w]
      · exact False.elim (hj rfl))
  simpa [lin_four,pathRows,pathFourth,q] using hh

/-- Exact necessary coefficient cone for the surviving canonical path.
No sign or support restriction on the fourth row is assumed. -/
theorem path_ppm_coefficient_bounds (a b : ℝ)
    (h : Represents (pathRows true true false a b 0)) : 0 ≤ a ∧ b ≤ a := by
  have ha : 0 ≤ a := by
    by_contra hh
    have han : a < 0 := lt_of_not_ge hh
    have hane : a ≠ 0 := ne_of_lt han
    let u : ℝ := -(abs (b-a)+1)/a
    have hu : 0 < u := div_pos_of_neg_of_neg (by linarith [abs_nonneg (b-a)]) han
    have he := path_ppm_facet_nonnegative a b u (-1) h hu (by norm_num)
    have heu : a*u = -(abs (b-a)+1) := by dsimp [u]; field_simp [hane]; ring
    rw [heu] at he
    have hab := neg_abs_le_self (b-a)
    norm_num at he
    linarith only [he,hab]
  have hb : b ≤ a := by
    by_contra hh
    have hd : 0 < b-a := sub_pos.mpr (lt_of_not_ge hh)
    have hdne : b-a ≠ 0 := ne_of_gt hd
    let v : ℝ := -(a+1)/(b-a)
    have hv : v < 0 := div_neg_of_neg_of_pos (by linarith only [ha]) hd
    have he := path_ppm_facet_nonnegative a b 1 v h (by norm_num) hv
    have hev : (b-a)*v = -(a+1) := by dsimp [v]; field_simp [hdne]; ring
    rw [hev] at he
    linarith only [he]
  exact ⟨ha,hb⟩

/-- In the exactly-three-root stratum, the coefficient cone has none of
its root boundary points. Thus only the strict mixed and star intervals remain. -/
theorem path_ppm_nonroot_coefficient_bounds (a b : ℝ)
    (h : Represents (pathRows true true false a b 0))
    (ht : Nonroot (pathFourth a b 0)) : 0 < a ∧ b ≠ 0 ∧ b < a := by
  obtain ⟨ha,hba⟩ := path_ppm_coefficient_bounds a b h
  have hane : a ≠ 0 := by
    intro hz
    apply ht 1 2 (by decide)
    refine ⟨b,fun l => ?_⟩
    fin_cases l <;> norm_num [pathFourth,hz,Fin.ext_iff]
  have hbne : b ≠ 0 := by
    intro hz
    apply ht 0 1 (by decide)
    refine ⟨a,fun l => ?_⟩
    fin_cases l <;> norm_num [pathFourth,hz,Fin.ext_iff]
  have hbane : b ≠ a := by
    intro hz
    apply ht 0 2 (by decide)
    refine ⟨a,fun l => ?_⟩
    fin_cases l <;> norm_num [pathFourth,hz,Fin.ext_iff]
  exact ⟨lt_of_le_of_ne ha (Ne.symm hane),hbne,lt_of_le_of_ne hba hbane⟩

#print axioms path_orientation_and_span
#print axioms path_ppm_coefficient_bounds

end MaxCaterpillar.Fiber.Count65.ThreeRoots
