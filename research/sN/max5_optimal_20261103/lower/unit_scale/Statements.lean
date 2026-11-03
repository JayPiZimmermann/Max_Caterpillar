import research.sN.max5_optimal_20261103.lower.unit_scale.UnitComparator
set_option autoImplicit false
open BigOperators MaxCaterpillar MaxCaterpillar.Frontier
open MaxCaterpillar.Max5Optimal.TripleContact MaxCaterpillar.Max5Optimal.UnitScale

example : ∀ {N : ℕ} [NeZero N]
    (s : ℝ) (q : Point N) (I : Finset (Fin N)),
    3≤I.card → (∀ i ∈ I, q i=0) → (∀ i ∉ I, q i≤-1) →
    LocOddLin (fun x => s*Maximum N x) q → s=0 :=
  @scalar_eq_zero_of_locOddLin_max

example : ∀ {mR : ℕ}
    (aR : Point 4) (bR : ℝ) (AR : Fin mR → Point 4) (βR cR : Fin mR → ℝ)
    (aH : Point 4) (bH cH scale : ℝ), 0≤scale →
    (∀ x : Point 4,
      shallow aR bR AR βR cR x+
      relu (scale*(max (x 0) (x 1)-max (x 2) (x 3)))+
      relu (lin aH x+bH+cH*relu (x 0-x 1))=Maximum 4 x) → scale=1 :=
  @unit_comparator_scale

/-- Literal array-and-max consumer of the exact comparator statement. -/
example : ∀ {mR : ℕ}
    (aR : Fin 4 → ℝ) (bR : ℝ) (AR : Fin mR → Fin 4 → ℝ) (βR cR : Fin mR → ℝ)
    (aH : Fin 4 → ℝ) (bH cH scale : ℝ), 0≤scale →
    (∀ x : Fin 4 → ℝ,
      ((∑ i, aR i*x i)+bR+∑ k, cR k*max 0 ((∑ i, AR k i*x i)+βR k))+
      max 0 (scale*(max (x 0) (x 1)-max (x 2) (x 3)))+
      max 0 ((∑ i, aH i*x i)+bH+cH*max 0 (x 0-x 1))=Maximum 4 x) → scale=1 :=
  @unit_comparator_scale

/-- Nonvacuity at the forced value: one shallow comparison supplies R,
and the second core may be zero. -/
example : ∃ (aR : Point 4) (AR : Fin 1 → Point 4), ∀ x : Point 4,
    shallow aR 0 AR 0 (fun _ => 1) x+
    relu ((1:ℝ)*(max (x 0) (x 1)-max (x 2) (x 3)))+
    relu (lin (0:Point 4) x+0+0*relu (x 0-x 1))=Maximum 4 x := by
  refine ⟨unitVec 3,fun _ => unitVec 2-unitVec 3,fun x => ?_⟩
  have hlin : lin (unitVec (2:Fin 4)-unitVec 3) x=x 2-x 3 := by
    simp [lin,unitVec,sub_mul,Finset.sum_sub_distrib]
  have hR : shallow (unitVec 3) 0 (fun _ : Fin 1 => unitVec 2-unitVec 3)
      0 (fun _ => 1) x=max (x 2) (x 3) := by
    simp only [shallow,Fin.sum_univ_one,Pi.zero_apply,add_zero,one_mul,hlin]
    have hcoord : lin (unitVec (3:Fin 4)) x=x 3 := by simp [lin,unitVec]
    rw [hcoord,add_comm,relu_sub_add,max_comm]
  rw [hR,scaled_pair_comparator 1 (by norm_num)]
  simp only [lin_zero_left,zero_add,zero_mul,relu_of_nonpos (le_refl (0:ℝ)),add_zero,one_mul]
  ring

#print axioms scalar_eq_zero_of_locOddLin_max
#print axioms unit_comparator_scale
