import MaxCaterpillar.Fiber.Count65.SectorSeparation.PairedWedge
import MaxCaterpillar.Fiber.Count65.SectorSeparation.PairAlgebra

/-! The closed paired wedge becomes the genuine independent paired frame
when zero rows and repeated positive rays are excluded. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace MaxCaterpillar.Fiber.Count65.SectorSeparation

def LabeledPairedRows (A : FirstMatrix) : Prop :=
  ∃ a b c d : ℝ, a*d-b*c ≠ 0 ∧ ∃ s : Fin 6 → ℝ,
    (∀ j, 0 < s j) ∧ A = fun j i => s j * pairedRows a b c d j i

lemma oppositeClosed_scaled_pair (s t a b : ℝ) (hs : 0≤s) (ht : 0≤t) :
    OppositeClosed (s*a) (s*b) (t*(-a)) (t*(-b)) := by
  refine ⟨by ring, ?_, ?_⟩
  · nlinarith only [mul_nonneg (mul_nonneg hs ht) (sq_nonneg a)]
  · nlinarith only [mul_nonneg (mul_nonneg hs ht) (sq_nonneg b)]

lemma planeRow_scaled (t a b : ℝ) :
    t • planeRow a b = planeRow ((t • planeRow a b) 1) ((t • planeRow a b) 3) := by
  change t • planeRow a b = planeRow (t*a) (t*b)
  exact (planeRow_smul t a b).symm

lemma pairedClosedRows_of_labeled {A : FirstMatrix} (h : LabeledPairedRows A) :
    PairedClosedRows A := by
  obtain ⟨a,b,c,d,_,s,hs,hA⟩ := h
  have hrow (j : Fin 6) : A j = s j • pairedRows a b c d j := by
    funext i
    exact congrFun (congrFun hA j) i
  have h00 : A 0 0=s 0 := by
    have hh := congrFun (hrow 0) 0
    simpa only [pairedRows_zero,rootQ,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_zero,mul_one] using hh
  have h12 : A 1 2=s 1 := by
    have hh := congrFun (hrow 1) 2
    change A 1 2=s 1*1 at hh
    simpa only [mul_one] using hh
  refine ⟨by rw [h00]; exact (hs 0).le, by rw [h12]; exact (hs 1).le,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h00]
    simpa only [pairedRows_zero] using hrow 0
  · rw [h12]
    simpa only [pairedRows_one] using hrow 1
  · rw [hrow 2,pairedRows_two]
    exact planeRow_scaled (s 2) a b
  · rw [hrow 3,pairedRows_three]
    exact planeRow_scaled (s 3) (-a) (-b)
  · rw [hrow 4,pairedRows_four]
    exact planeRow_scaled (s 4) c d
  · rw [hrow 5,pairedRows_five]
    exact planeRow_scaled (s 5) (-c) (-d)
  · simpa only [hrow,pairedRows_two,pairedRows_three,planeRow,
      Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
      oppositeClosed_scaled_pair (s 2) (s 3) a b (hs 2).le (hs 3).le
  · simpa only [hrow,pairedRows_four,pairedRows_five,planeRow,
      Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
      oppositeClosed_scaled_pair (s 4) (s 5) c d (hs 4).le (hs 5).le

lemma labeled_of_pairedClosedRows (A : FirstMatrix)
    (hn : ∀ j, A j ≠ 0)
    (hp : ∀ (j k : Fin 6), j ≠ k → ∀ t : ℝ, 0<t → A j ≠ t • A k)
    (h : PairedClosedRows A) : LabeledPairedRows A := by
  rcases h with ⟨h0,h1,hq,hr,h2,h3,h4,h5,h23,h45⟩
  have h0p : 0<A 0 0 := lt_of_le_of_ne h0 (by
    intro hz
    exact hn 0 (by rw [hq,← hz,zero_smul]))
  have h1p : 0<A 1 2 := lt_of_le_of_ne h1 (by
    intro hz
    exact hn 1 (by rw [hr,← hz,zero_smul]))
  have hx : A 2 1≠0 ∨ A 2 3≠0 :=
    planeRow_nonzero_coordinates _ _ (by rw [← h2]; exact hn 2)
  have hy : A 3 1≠0 ∨ A 3 3≠0 :=
    planeRow_nonzero_coordinates _ _ (by rw [← h3]; exact hn 3)
  have hu : A 4 1≠0 ∨ A 4 3≠0 :=
    planeRow_nonzero_coordinates _ _ (by rw [← h4]; exact hn 4)
  have hv : A 5 1≠0 ∨ A 5 3≠0 :=
    planeRow_nonzero_coordinates _ _ (by rw [← h5]; exact hn 5)
  obtain ⟨k,hk,hk1,hk3⟩ := exists_pos_neg_scalar_of_det_eq_zero
    _ _ _ _ hx hy h23.1 h23.2.1 h23.2.2
  obtain ⟨l,hl,hl1,hl3⟩ := exists_pos_neg_scalar_of_det_eq_zero
    _ _ _ _ hu hv h45.1 h45.2.1 h45.2.2
  have h3neg : A 3=(-k) • A 2 := by
    rw [h3,h2,hk1,hk3,planeRow_smul]
  have hdet : A 2 1*A 4 3-A 2 3*A 4 1 ≠ 0 := by
    intro hd
    obtain ⟨t,ht,ht1,ht3⟩ := exists_nonzero_scalar_of_det_eq_zero
      _ _ _ _ hx hu hd
    have h4t : A 4=t • A 2 := by rw [h4,h2,ht1,ht3,planeRow_smul]
    by_cases htp : 0<t
    · exact hp 4 2 (by decide) t htp h4t
    · have htn : t<0 := lt_of_le_of_ne (le_of_not_gt htp) ht
      apply hp 4 3 (by decide) (-t/k) (div_pos (neg_pos.mpr htn) hk)
      rw [h3neg,smul_smul,h4t]
      congr 1
      field_simp [hk.ne']
  let s : Fin 6 → ℝ := ![A 0 0,A 1 2,1,k,1,l]
  have hs : ∀ j,0<s j := by
    intro j
    fin_cases j <;> simp only [s,Matrix.cons_val_zero',Matrix.cons_val_succ']
    · exact h0p
    · exact h1p
    · exact zero_lt_one
    · exact hk
    · exact zero_lt_one
    · exact hl
  refine ⟨A 2 1,A 2 3,A 4 1,A 4 3,hdet,s,hs,?_⟩
  have hrows : ∀ j, A j=s j • pairedRows (A 2 1) (A 2 3) (A 4 1) (A 4 3) j := by
    intro j
    fin_cases j
    · exact hq
    · exact hr
    · change A 2=1 • planeRow (A 2 1) (A 2 3)
      simpa only [one_smul] using h2
    · change A 3=k • planeRow (-A 2 1) (-A 2 3)
      rw [h3,hk1,hk3]
      rw [← planeRow_smul]
      simp only [neg_mul,mul_neg]
    · change A 4=1 • planeRow (A 4 1) (A 4 3)
      simpa only [one_smul] using h4
    · change A 5=l • planeRow (-A 4 1) (-A 4 3)
      rw [h5,hl1,hl3]
      rw [← planeRow_smul]
      simp only [neg_mul,mul_neg]
  funext j i
  exact congrFun (hrows j) i

#print axioms labeled_of_pairedClosedRows
end MaxCaterpillar.Fiber.Count65.SectorSeparation
