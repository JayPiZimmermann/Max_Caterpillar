import MaxCaterpillar.Frontier.StarCertificate.Mobius

/-! # The top coefficient annihilates actual quadratic Boolean functions -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MaxCaterpillar.Frontier.StarCertificate
open BigOperators

noncomputable def booleanCoordinate (a : Fin 5) (B : Finset (Fin 5)) : ℝ :=
  if a∈B then 1 else 0

/-- These are actual evaluations of Max5 on the Boolean input vectors. -/
theorem maximum_boolean_input (B : Finset (Fin 5)) :
    Maximum 5 (fun i => booleanCoordinate i B)=booleanOR B := by
  classical
  by_cases hB : B=∅
  · subst B
    change Maximum 5 (0 : Point 5)=0
    exact Maximum_zero
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hB
    rw [booleanOR,if_neg hB]
    apply Maximum_eq_of _ _ i (by simp [booleanCoordinate,hi])
    intro j
    by_cases hj : j∈B <;> simp [booleanCoordinate,hj]

theorem constant_mobius_coefficients :
    (∑ B : Finset (Fin 5), topMobiusSign B)=0 := by decide

theorem linear_mobius_coefficients : ∀ a : Fin 5,
    (∑ B : Finset (Fin 5), topMobiusSign B*(if a∈B then 1 else 0))=0 := by decide

theorem quadratic_mobius_coefficients : ∀ a b : Fin 5,
    (∑ B : Finset (Fin 5), topMobiusSign B*(if a∈B ∧ b∈B then 1 else 0))=0 := by decide

theorem topMobius_constant (a : ℝ) : topMobius (fun _ => a)=0 := by
  have hh := congrArg (fun q : ℤ => (q : ℝ)) constant_mobius_coefficients
  have hz : (∑ B : Finset (Fin 5), (topMobiusSign B : ℝ))=0 := by
    simpa only [Int.cast_sum,Int.cast_zero] using hh
  simp only [topMobius,←Finset.sum_mul,hz,zero_mul]

theorem topMobius_booleanCoordinate (a : Fin 5) : topMobius (booleanCoordinate a)=0 := by
  have hh := congrArg (fun q : ℤ => (q : ℝ)) (linear_mobius_coefficients a)
  simpa only [topMobius,booleanCoordinate,Int.cast_sum,Int.cast_mul,apply_ite,
    Int.cast_one,Int.cast_zero] using hh

theorem topMobius_booleanProduct (a b : Fin 5) :
    topMobius (fun B => booleanCoordinate a B*booleanCoordinate b B)=0 := by
  have hh := congrArg (fun q : ℤ => (q : ℝ)) (quadratic_mobius_coefficients a b)
  have hp : (fun B => booleanCoordinate a B*booleanCoordinate b B)=
      fun B => if a∈B ∧ b∈B then (1:ℝ) else 0 := by
    funext B
    by_cases ha : a∈B <;> by_cases hb : b∈B <;> simp [booleanCoordinate,ha,hb]
  rw [hp]
  simpa only [topMobius,Int.cast_sum,Int.cast_mul,apply_ite,
    Int.cast_one,Int.cast_zero] using hh

/-- Coefficients are arbitrary reals and may include diagonal products.
No zero-top-coefficient property is built into this parameterization. -/
noncomputable def booleanQuadratic (a : ℝ) (b : Fin 5→ℝ) (d : Fin 5→Fin 5→ℝ)
    (B : Finset (Fin 5)) : ℝ :=
  a+(∑ i, b i*booleanCoordinate i B)+
    ∑ i, ∑ j, d i j*(booleanCoordinate i B*booleanCoordinate j B)

theorem topMobius_booleanQuadratic (a : ℝ) (b : Fin 5→ℝ) (d : Fin 5→Fin 5→ℝ) :
    topMobius (booleanQuadratic a b d)=0 := by
  unfold booleanQuadratic
  rw [topMobius_add,topMobius_add,topMobius_constant,topMobius_sum,topMobius_sum]
  simp_rw [topMobius_sum,topMobius_mul,topMobius_booleanCoordinate,
    topMobius_booleanProduct,mul_zero]
  simp

/-- A first-layer difference ReLU really has Boolean degree at most two. -/
theorem boolean_difference_relu (a b : Fin 5) (B : Finset (Fin 5)) :
    relu (booleanCoordinate a B-booleanCoordinate b B)=
      booleanCoordinate a B-booleanCoordinate a B*booleanCoordinate b B := by
  by_cases ha : a∈B <;> by_cases hb : b∈B <;> norm_num [booleanCoordinate,ha,hb,relu]

theorem topMobius_booleanDifferenceRelu (a b : Fin 5) :
    topMobius (fun B => relu (booleanCoordinate a B-booleanCoordinate b B))=0 := by
  simp_rw [boolean_difference_relu,sub_eq_add_neg]
  rw [topMobius_add,topMobius_booleanCoordinate]
  have hh := topMobius_mul (-1) (fun B => booleanCoordinate a B*booleanCoordinate b B)
  simp only [neg_one_mul,topMobius_booleanProduct,mul_zero] at hh
  rw [hh,zero_add]

#print axioms topMobius_booleanQuadratic
#print axioms topMobius_booleanDifferenceRelu
end MaxCaterpillar.Frontier.StarCertificate
