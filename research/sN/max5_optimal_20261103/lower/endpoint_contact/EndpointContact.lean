import research.sN.max5_optimal_20261103.lower.triple_contact.TripleContact

/-! Exact directional derivatives at a shared four-way contact.
All equalities below concern the literal finite affine-shallow expressions.
No differentiability across the entire ambient space is assumed. -/
set_option autoImplicit false
namespace MaxCaterpillar.Max5Optimal.EndpointContact
open BigOperators Filter Topology Frontier TripleContact

/-- The right derivative of ReLU(u+t*v) at t=0. -/
noncomputable def reluSlope (u v : ℝ) : ℝ :=
  if 0<u then v else if u=0 then relu v else 0

lemma relu_eventually_affine (u v : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      relu (u+ε*v)=relu u+ε*reluSlope u v := by
  rcases lt_trichotomy u 0 with hn | hz | hp
  · filter_upwards [eventually_small v (neg_pos.mpr hn)] with ε hε
    have he : u+ε*v≤0 := by linarith only [(abs_lt.mp hε).2]
    simp [relu_of_nonpos hn.le,relu_of_nonpos he,reluSlope,not_lt.mpr hn.le,hn.ne]
  · subst u
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0<ε := hε
    simp [reluSlope,relu_mul_pos hε',relu_of_nonpos (le_refl (0:ℝ))]
  · filter_upwards [eventually_small v hp] with ε hε
    have he : 0≤u+ε*v := by linarith only [(abs_lt.mp hε).1]
    simp [relu_of_nonneg hp.le,relu_of_nonneg he,reluSlope,hp]

/-- Directional slope of an affine-shallow function. Its biases are retained
inside the sign test of each first preactivation. -/
noncomputable def directionalSlope {N m : ℕ}
    (a : Point N) (A : Fin m → Point N) (β c : Fin m → ℝ) (q v : Point N) : ℝ :=
  lin a v+∑ k, c k*reluSlope (lin (A k) q+β k) (lin (A k) v)

/-- A finite shallow ReLU sum is exactly affine on a sufficiently short
positive ray, with the explicit directional slope above. -/
theorem shallow_eventually_affine {N m : ℕ}
    (a : Point N) (b : ℝ) (A : Fin m → Point N) (β c : Fin m → ℝ) (q v : Point N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      shallow a b A β c (q+ε • v)=
        shallow a b A β c q+ε*directionalSlope a A β c q v := by
  have hh : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k,
      relu (lin (A k) q+β k+ε*lin (A k) v)=
        relu (lin (A k) q+β k)+ε*reluSlope (lin (A k) q+β k) (lin (A k) v) :=
    Filter.eventually_all.mpr fun k =>
      relu_eventually_affine (lin (A k) q+β k) (lin (A k) v)
  filter_upwards [hh] with ε hε
  have hrow (k : Fin m) :
      relu (lin (A k) (q+ε • v)+β k)=
        relu (lin (A k) q+β k)+ε*reluSlope (lin (A k) q+β k) (lin (A k) v) := by
    rw [lin_add_right,lin_smul_right]
    convert hε k using 1
    congr 1
    ring
  simp only [shallow,hrow,directionalSlope]
  rw [lin_add_right,lin_smul_right]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm]
  ring

/-- The general derivative cut, retaining first biases and affine heads. -/
theorem shared_endpoint_directional_disjunction {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (βg cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (βh ch : Fin mh → ℝ)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (shallow ag bg Ag βg cg x)+relu (shallow ah bh Ah βh ch x)=Maximum 5 x)
    (i j : Fin 5) (hij : i≠j)
    (hg : shallow ag bg Ag βg cg (-unitVec i)=0)
    (hh : shallow ah bh Ah βh ch (-unitVec i)=0) :
    directionalSlope ag Ag βg cg (-unitVec i) (-unitVec j)=0 ∨
      directionalSlope ah Ah βh ch (-unitVec i) (-unitVec j)=0 := by
  have hgerm := shallow_eventually_affine ag bg Ag βg cg (-unitVec i) (-unitVec j)
  have hherm := shallow_eventually_affine ah bh Ah βh ch (-unitVec i) (-unitVec j)
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hge,hhe⟩ := (hpos.and (hgerm.and hherm)).exists
  have hpoint : -unitVec i+ε • (-unitVec j)=
      -((1:ℝ) • unitVec i)-ε • unitVec j := by simp [sub_eq_add_neg]
  rw [hg,zero_add,hpoint] at hge
  rw [hh,zero_add,hpoint] at hhe
  have hz := max5_weighted_pair_contact aR ag ah bR bg bh AR βR cR Ag βg cg Ah βh ch
    heq i j hij 1 ε (by norm_num) hε
  rw [hge,hhe] at hz
  rcases hz with hg0 | hh0
  · exact Or.inl ((mul_eq_zero.mp hg0).resolve_left hε.ne')
  · exact Or.inr ((mul_eq_zero.mp hh0).resolve_left hε.ne')

/-- Explicit homogeneous-row endpoint formula, with an optional affine head. -/
noncomputable def endpointSlope {m : ℕ} (a : Point 5) (A : Fin m → Point 5)
    (c : Fin m → ℝ) (i j : Fin 5) : ℝ :=
  -a j+∑ k, c k*(if A k i<0 then -A k j else if A k i=0 then relu (-A k j) else 0)

lemma directionalSlope_endpoint {m : ℕ} (a : Point 5) (A : Fin m → Point 5)
    (c : Fin m → ℝ) (i j : Fin 5) :
    directionalSlope a A 0 c (-unitVec i) (-unitVec j)=endpointSlope a A c i j := by
  simp only [directionalSlope,endpointSlope,lin_neg_right,lin_unitVec,Pi.zero_apply,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp [reluSlope]

/-- Direct model clause for homogeneous first rows. Both shared core values
are zero, so at least one of their explicit endpoint slopes is zero. -/
theorem shared_endpoint_slope_disjunction {mR mg mh : ℕ}
    (aR ag ah : Point 5) (bR bg bh : ℝ)
    (AR : Fin mR → Point 5) (βR cR : Fin mR → ℝ)
    (Ag : Fin mg → Point 5) (cg : Fin mg → ℝ)
    (Ah : Fin mh → Point 5) (ch : Fin mh → ℝ)
    (heq : ∀ x, shallow aR bR AR βR cR x+
      relu (shallow ag bg Ag 0 cg x)+relu (shallow ah bh Ah 0 ch x)=Maximum 5 x)
    (i j : Fin 5) (hij : i≠j)
    (hg : shallow ag bg Ag 0 cg (-unitVec i)=0)
    (hh : shallow ah bh Ah 0 ch (-unitVec i)=0) :
    endpointSlope ag Ag cg i j=0 ∨ endpointSlope ah Ah ch i j=0 := by
  simpa only [directionalSlope_endpoint] using
    shared_endpoint_directional_disjunction aR ag ah bR bg bh AR βR cR Ag 0 cg Ah 0 ch
      heq i j hij hg hh

#check @shared_endpoint_directional_disjunction
#print axioms shared_endpoint_directional_disjunction
#check @shared_endpoint_slope_disjunction
#print axioms shared_endpoint_slope_disjunction
end MaxCaterpillar.Max5Optimal.EndpointContact
