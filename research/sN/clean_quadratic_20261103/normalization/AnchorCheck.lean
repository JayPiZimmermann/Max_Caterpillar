import research.sN.clean_quadratic_20261103.normalization.AnchorLocalization

/-! Independent literal-type and realizability checks for the anchor lift.
The canonical tied point checks the maximum identity only; it is not asserted
to be generic for arbitrary first-layer forms. -/
set_option autoImplicit false
namespace MaxCaterpillar.CleanQuadratic.Normalization.IndependentCheck
open BigOperators Frontier Frontier.RandomRestriction NormalizedNetwork
variable {N m h₁ h₂ : ℕ}

theorem exact_step [NeZero N] [NeZero m]
    (e : Fin m ↪ Fin N) (a : Fin m) (q : Point N)
    (hq : ∀ i, q (e i) = 0)
    (hneg : ∀ i, i ∉ Finset.univ.image e → q i < 0)
    (x : Point m) (ε : ℝ) (hε : 0 < ε) :
    Maximum N (fun i => q i + ε * (lift e (fun j => x j-x a) i+x a)) =
      ε * Maximum m x := by
  exact maximum_anchorLift e a q hq hneg x ε hε

theorem exact_sum (e : Fin m ↪ Fin N) (a : Fin m) (v : Point N) :
    (∑ j, (v (e j) + ((∑ i,v i)-(∑ b,v (e b))) *
      (if j=a then 1 else 0))) = ∑ i,v i := by
  exact sum_anchorRestrict e a v

theorem exact_model [NeZero N] [NeZero m]
    (net : NormalizedNetwork N h₁ h₂)
    (hA : ∀ j, ∑ i,net.A j i=0)
    (hU : ∀ k, ∑ i,net.U k i=0)
    (hL : ∑ i,net.L i=1)
    (hnet : ∀ x, lin net.L x + (∑ j,net.B j*relu (lin (net.A j) x)) +
      ∑ k,net.d k*relu (lin (net.U k) x +
        ∑ j,net.W k j*relu (lin (net.A j) x)) = Maximum N x)
    (e : Fin m ↪ Fin N) :
    ∃ model : NormalizedNetwork m h₁ h₂,
      (∀ x,lin model.L x + (∑ j,model.B j*relu (lin (model.A j) x)) +
        ∑ k,model.d k*relu (lin (model.U k) x +
          ∑ j,model.W k j*relu (lin (model.A j) x)) = Maximum m x) ∧
      ((∀ j,∑ i,model.A j i=0) ∧ (∀ k,∑ i,model.U k i=0) ∧ ∑ i,model.L i=1) ∧
      (∀ j,model.A j =
        if (Finset.univ.filter (fun i => net.A j i≠0))⊆Finset.univ.image e
        then (fun i => net.A j (e i)) else 0) := by
  exact exists_anchor_localized net ⟨hA,hU,hL⟩ hnet e

noncomputable def canonicalPoint (e : Fin m ↪ Fin N) : Point N :=
  fun i => if i∈Finset.univ.image e then 0 else -1

theorem canonical_base_control [NeZero N] [NeZero m]
    (e : Fin m ↪ Fin N) (a : Fin m) (x : Point m) (ε : ℝ) (hε : 0<ε) :
    Maximum N (canonicalPoint e + ε • anchorLift e a x) = ε*Maximum m x := by
  apply maximum_anchorLift e a (canonicalPoint e) ?_ ?_ x ε hε
  · intro i
    simp [canonicalPoint]
  · intro i hi
    simp only [canonicalPoint,if_neg hi]
    norm_num

def maxTwo : NormalizedNetwork 2 1 1 where
  A _ := ![1,-1]
  U _ := 0
  W _ _ := 1
  L := ![0,1]
  B _ := 0
  d _ := 1

theorem maxTwo_normalized : maxTwo.TranslationNormalized := by
  norm_num [maxTwo,TranslationNormalized,Fin.sum_univ_two]

private theorem maximum_two (x : Point 2) : Maximum 2 x=max (x 0) (x 1) := by
  apply le_antisymm
  · apply (Maximum_le_iff _ _).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_Maximum x 0) (le_Maximum x 1)

theorem maxTwo_exact (x : Point 2) : maxTwo.eval x=Maximum 2 x := by
  rw [maximum_two]
  simp only [eval,NormalizedNetwork.inner,maxTwo,lin,Fin.sum_univ_two,Fin.sum_univ_one,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Pi.zero_apply,
    zero_mul,one_mul,neg_mul,zero_add,add_zero,zero_sub]
  by_cases h : x 0≤x 1
  · have hs : x 0 + -x 1≤0 := by linarith only [h]
    simp [relu,max_eq_right h,max_eq_left hs]
  · have hs : 0≤x 0 + -x 1 := by linarith only [h]
    rw [max_eq_left (le_of_not_ge h)]
    simp only [relu,max_eq_right hs,max_self]
    ring

theorem maxTwo_restriction_realizable :
    ∃ model : NormalizedNetwork 1 1 1,
      (∀ x,model.eval x=Maximum 1 x) ∧ model.TranslationNormalized ∧
      (∀ j,model.A j=0) := by
  let e : Fin 1 ↪ Fin 2 := ⟨fun _ => 0,fun x y _ => Subsingleton.elim x y⟩
  obtain ⟨model,hm,hn,hrows⟩ :=
    exists_anchor_localized maxTwo maxTwo_normalized maxTwo_exact e
  refine ⟨model,hm,hn,?_⟩
  intro j
  rw [hrows]
  have hnot : ¬rowSupport (maxTwo.A j)⊆Finset.univ.image e := by
    intro h
    have hm : (1 : Fin 2)∈rowSupport (maxTwo.A j) := by
      simp [mem_rowSupport,maxTwo]
    have hout := h hm
    simp [e] at hout
  rw [if_neg hnot]

#check @exact_step
#check @exact_sum
#check @exact_model
#print axioms exact_step
#print axioms exact_sum
#print axioms exact_model
#print axioms canonical_base_control
#print axioms maxTwo_normalized
#print axioms maxTwo_exact
#print axioms maxTwo_restriction_realizable
end MaxCaterpillar.CleanQuadratic.Normalization.IndependentCheck
