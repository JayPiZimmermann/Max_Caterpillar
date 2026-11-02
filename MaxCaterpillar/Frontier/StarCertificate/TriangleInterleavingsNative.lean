import MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings

/-! The primitive Boolean polynomial represented by the coefficient interface. -/
set_option autoImplicit false
set_option maxHeartbeats 0
namespace MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
open BigOperators

noncomputable def coordinate (S : Finset (Fin 5)) (i : Fin 5) : ℝ :=
  if i ∈ S then 1 else 0

/-- The model is exactly the stated quadratic polynomial in Boolean coordinates. -/
theorem nativeTriangle_formula (A B C x y z u v : ℝ) (S : Finset (Fin 5)) :
    nativeTriangle ![A,B,C,x,y,z,u,v] S =
      A*coordinate S 0 + B*coordinate S 1 + C*coordinate S 2 +
      x*coordinate S 0*coordinate S 1 + y*coordinate S 0*coordinate S 2 +
      z*coordinate S 1*coordinate S 2 + u*coordinate S 3 + v*coordinate S 4 := by
  unfold nativeTriangle
  rw [Fin.sum_univ_eight]
  change (bit S 0 : ℝ)*A + (bit S 1 : ℝ)*B + (bit S 2 : ℝ)*C +
    ((bit S 0*bit S 1 : ℤ) : ℝ)*x + ((bit S 0*bit S 2 : ℤ) : ℝ)*y +
    ((bit S 1*bit S 2 : ℤ) : ℝ)*z + (bit S 3 : ℝ)*u + (bit S 4 : ℝ)*v = _
  have hb : ∀ i : Fin 5, (bit S i : ℝ)=coordinate S i := by
    intro i
    by_cases hi : i ∈ S <;> simp [bit,coordinate,hi]
  simp only [Int.cast_mul,hb]
  ring

/-- Zero constant term is a consequence of the native polynomial definition. -/
theorem nativeTriangle_empty (p : Fin 8 → ℝ) : nativeTriangle p ∅=0 := by
  have hc : nativeCoefficients (∅ : Finset (Fin 5))=0 := by
    funext j
    fin_cases j <;> rfl
  simp only [nativeTriangle,hc,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero]

/-- The full-set normalization is exactly the sum of the eight coefficients. -/
theorem nativeTriangle_full (A B C x y z u v : ℝ) :
    nativeTriangle ![A,B,C,x,y,z,u,v] Finset.univ=A+B+C+x+y+z+u+v := by
  rw [nativeTriangle_formula]
  simp only [coordinate,Finset.mem_univ,if_true,mul_one]

#print axioms nativeTriangle_formula
#print axioms nativeTriangle_empty
#print axioms nativeTriangle_full
end MaxCaterpillar.Frontier.StarCertificate.TriangleInterleavings
