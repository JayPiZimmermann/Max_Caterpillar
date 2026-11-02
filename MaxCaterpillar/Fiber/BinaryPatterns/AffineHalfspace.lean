import MaxCaterpillar.Fiber.BinaryPatterns.Core

/-! # Global binary affine gates determine a positive ray or an inactive row -/
set_option autoImplicit false
namespace MaxCaterpillar.Fiber.BinaryPatterns.AffineHalfspace
open BigOperators
variable {N : ℕ}

noncomputable def linearValue (w x : Fin N → ℝ) : ℝ := ∑ i,w i*x i
noncomputable def affineValue (w : Fin N → ℝ) (b : ℝ) (x : Fin N → ℝ) : ℝ :=
  linearValue w x+b
noncomputable def coordinate (j : Fin N) (t : ℝ) : Fin N → ℝ := fun i => if i=j then t else 0

@[simp] lemma linear_zero (w : Fin N → ℝ) : linearValue w 0 = 0 := by simp [linearValue]
@[simp] lemma linear_zero_left (x : Fin N → ℝ) : linearValue 0 x = 0 := by simp [linearValue]
@[simp] lemma affine_zero (w : Fin N → ℝ) (b : ℝ) : affineValue w b 0 = b := by simp [affineValue]
@[simp] lemma affine_zero_left (b : ℝ) (x : Fin N → ℝ) : affineValue 0 b x = b := by simp [affineValue]
@[simp] lemma linear_coordinate (w : Fin N → ℝ) (j : Fin N) (t : ℝ) :
    linearValue w (coordinate j t) = w j*t := by simp [linearValue,coordinate,mul_ite]

lemma affine_line (w : Fin N → ℝ) (b : ℝ) (x v : Fin N → ℝ) (t : ℝ) :
    affineValue w b (fun i => x i+t*v i) = affineValue w b x+t*linearValue w v := by
  simp only [affineValue,linearValue,mul_add,mul_left_comm,Finset.sum_add_distrib,←Finset.mul_sum]
  ring

lemma affine_shift (w : Fin N → ℝ) (b : ℝ) (x v : Fin N → ℝ) (t : ℝ) :
    affineValue w b (fun i => x i-t*v i) = affineValue w b x-t*linearValue w v := by
  simpa only [neg_mul,sub_eq_add_neg] using affine_line w b x v (-t)

/-- A scalar affine function with precisely the positive half-line as its positive set. -/
theorem positive_halfline (a b : ℝ) (h : ∀ t : ℝ,0 < t ↔ 0 < a*t+b) :
    0 < a ∧ b = 0 := by
  have hb : b ≤ 0 := by
    have hn : ¬0 < a*0+b := fun hp => (lt_irrefl (0 : ℝ)) ((h 0).mpr hp)
    simpa only [mul_zero,zero_add] using le_of_not_gt hn
  have hp : 0 < a+b := by simpa only [mul_one] using (h 1).mp zero_lt_one
  have ha : 0 < a := by linarith
  have hb' : 0 ≤ b := by
    by_contra hn
    have hbn : b < 0 := lt_of_not_ge hn
    have ht : 0 < -b/a := div_pos (neg_pos.mpr hbn) ha
    have hh := (h (-b/a)).mp ht
    have hz : a*(-b/a)+b = 0 := by field_simp;ring
    rw [hz] at hh
    exact (lt_irrefl (0 : ℝ)) hh
  exact ⟨ha,le_antisymm hb hb'⟩

/-- An affine gate inactive at every real input has a zero incoming row. -/
theorem inactive_row (w : Fin N → ℝ) (b : ℝ)
    (h : ∀ x,affineValue w b x ≤ 0) : w = 0 ∧ b ≤ 0 := by
  have hw : ∀ j,w j = 0 := by
    intro j
    by_contra hn
    have hv := h (coordinate j ((1-b)/w j))
    have hz : affineValue w b (coordinate j ((1-b)/w j)) = 1 := by
      rw [affineValue,linear_coordinate]
      field_simp
      ring
    rw [hz] at hv
    norm_num at hv
  exact ⟨funext hw,by simpa only [affine_zero] using h 0⟩

/-- A globally positive affine function is a positive constant. -/
lemma positive_row (w : Fin N → ℝ) (b : ℝ)
    (h : ∀ x,0 < affineValue w b x) : w = 0 ∧ 0 < b := by
  have hw : ∀ j,w j = 0 := by
    intro j
    by_contra hn
    have hv := h (coordinate j (-b/w j))
    have hz : affineValue w b (coordinate j (-b/w j)) = 0 := by
      rw [affineValue,linear_coordinate]
      field_simp
      ring
    rw [hz] at hv
    exact (lt_irrefl (0 : ℝ)) hv
  exact ⟨funext hw,by simpa only [affine_zero] using h 0⟩

/-- Equality of nonempty strict-positive affine halfspaces forces positive proportionality.
Constant positive forms are included. The empty halfspace is the separate inactive-row case. -/
theorem positive_proportional (w v : Fin N → ℝ) (b c : ℝ)
    (h : ∀ x,0 < affineValue w b x ↔ 0 < affineValue v c x)
    (hne : ∃ x,0 < affineValue w b x) :
    ∃ s : ℝ,0 < s ∧ v = (fun j => s*w j) ∧ c = s*b := by
  by_cases hw : w = 0
  · have hb : 0 < b := by
      obtain ⟨x,hx⟩ := hne
      simpa only [hw,affine_zero_left] using hx
    have hp : ∀ x,0 < affineValue v c x := fun x => (h x).mp (by simpa only [hw,affine_zero_left] using hb)
    obtain ⟨hv,hc⟩ := positive_row v c hp
    refine ⟨c/b,div_pos hc hb,?_,?_⟩
    · rw [hw,hv]
      funext _j
      simp
    · field_simp
  · have hi : ∃ j,w j ≠ 0 := by
      by_contra hn
      apply hw
      funext j
      by_contra hj
      exact hn ⟨j,hj⟩
    obtain ⟨j,hj⟩ := hi
    let d := coordinate j (1/w j)
    let z := coordinate j (-b/w j)
    have hd : linearValue w d = 1 := by
      dsimp [d]
      rw [linear_coordinate]
      field_simp
    have hz : affineValue w b z = 0 := by
      dsimp [z]
      rw [affineValue,linear_coordinate]
      field_simp
      ring
    have line (y : Fin N → ℝ) (hy : affineValue w b y = 0) :
        ∀ t : ℝ,0 < t ↔ 0 < linearValue v d*t+affineValue v c y := by
      intro t
      have ht := h (fun i => y i+t*d i)
      rw [affine_line,affine_line,hy,hd] at ht
      simpa only [mul_one,zero_add,add_zero,mul_comm,add_comm] using ht
    have hs := (positive_halfline _ _ (line z hz)).1
    have all (x : Fin N → ℝ) : affineValue v c x = linearValue v d*affineValue w b x := by
      let y := fun i => x i-affineValue w b x*d i
      have hy : affineValue w b y = 0 := by
        dsimp [y]
        rw [affine_shift,hd]
        ring
      have hgy := (positive_halfline _ _ (line y hy)).2
      dsimp [y] at hgy
      rw [affine_shift] at hgy
      linarith
    have hc : c = linearValue v d*b := by simpa only [affine_zero] using all 0
    refine ⟨linearValue v d,hs,?_,hc⟩
    funext k
    have hk := all (coordinate k 1)
    have hvk : affineValue v c (coordinate k 1) = v k+c := by rw [affineValue,linear_coordinate,mul_one]
    have hwk : affineValue w b (coordinate k 1) = w k+b := by rw [affineValue,linear_coordinate,mul_one]
    rw [hvk,hwk] at hk
    linarith

/-- Exhaustive alternatives for equal global binary gates. -/
theorem binary_gate_alternatives (w v : Fin N → ℝ) (b c : ℝ)
    (h : ∀ x,0 < affineValue w b x ↔ 0 < affineValue v c x) :
    (∃ s : ℝ,0 < s ∧ v = (fun j => s*w j) ∧ c = s*b) ∨
      (w = 0 ∧ b ≤ 0 ∧ v = 0 ∧ c ≤ 0) := by
  by_cases hn : ∃ x,0 < affineValue w b x
  · exact Or.inl (positive_proportional w v b c h hn)
  · have ha : ∀ x,affineValue w b x ≤ 0 := fun x => le_of_not_gt (fun hp => hn ⟨x,hp⟩)
    have hb : ∀ x,affineValue v c x ≤ 0 := fun x => le_of_not_gt (fun hp => hn ⟨x,(h x).mpr hp⟩)
    obtain ⟨hw,hb'⟩ := inactive_row w b ha
    obtain ⟨hv,hc⟩ := inactive_row v c hb
    exact Or.inr ⟨hw,hb',hv,hc⟩

end MaxCaterpillar.Fiber.BinaryPatterns.AffineHalfspace
