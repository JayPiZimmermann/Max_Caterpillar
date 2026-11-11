import MaxCaterpillar.Fiber.Count65.StarNonroot.Obstruction
import MaxCaterpillar.Fiber.Count65.PhysicalExtraction.Coordinates
import MaxCaterpillar.Fiber.Symmetry
import MaxCaterpillar.Fiber.Count65.TripleLocality

/-! # A genuine three-leaf nonroot cannot complete an outward star at width five

The theorem concerns the existing actual six-array Network model, with arbitrary
real weights and biases. The first matrix has three outward star roots, an invariant fourth direction,
and the signed anchor coordinate. Exactness forces that fourth direction to be
a scalar multiple of a comparison of two leaves; every genuine nonroot is therefore excluded.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MaxCaterpillar.Fiber.Count65.StarNonroot
open BigOperators MaxCaterpillar.Frontier

noncomputable def dictionary (a b c : ℝ) : Fin 4 → Point 3 :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![a,b,c]]

noncomputable def firstRows (a b c : ℝ) : Fin 6 → Point 4 :=
  PhysicalExtraction.carrierRows (dictionary a b c)

lemma features_zero (a b c : ℝ) (x y z : ℝ) :
    PhysicalExtraction.features (dictionary a b c) ![x,y,z] 0 = relu x := by
  simp [PhysicalExtraction.features,dictionary,lin,Fin.sum_univ_succ]

lemma features_one (a b c : ℝ) (x y z : ℝ) :
    PhysicalExtraction.features (dictionary a b c) ![x,y,z] 1 = relu y := by
  simp [PhysicalExtraction.features,dictionary,lin,Fin.sum_univ_succ]

lemma features_two (a b c : ℝ) (x y z : ℝ) :
    PhysicalExtraction.features (dictionary a b c) ![x,y,z] 2 = relu z := by
  simp [PhysicalExtraction.features,dictionary,lin,Fin.sum_univ_succ]

lemma features_three (a b c : ℝ) (x y z : ℝ) :
    PhysicalExtraction.features (dictionary a b c) ![x,y,z] 3 = relu (a*x+b*y+c*z) := by
  change relu (lin ![a,b,c] ![x,y,z])=relu (a*x+b*y+c*z)
  simp [lin,Fin.sum_univ_three]

lemma feature_linear_combination (R : Fin 4 → ℝ) (a b c x y z : ℝ) :
    (∑ i, R i * PhysicalExtraction.features (dictionary a b c) ![x,y,z] i) =
      form a b c (R 0) (R 1) (R 2) (R 3) x y z := by
  rw [Fin.sum_univ_four]
  simp only [features_zero,features_one,features_two,features_three,form]

lemma invariantPart_dictionary (net : Network 4 6 5) (a b c : ℝ)
    (j : Fin 5) (x y z : ℝ) :
    PhysicalExtraction.invariantPart net (dictionary a b c) j ![x,y,z] =
      form a b c (net.W₂ j 0) (net.W₂ j 1) (net.W₂ j 2) (net.W₂ j 3) x y z := by
  unfold PhysicalExtraction.invariantPart
  simpa only [Fin.castAdd_mk] using
    feature_linear_combination (fun i => net.W₂ j (Fin.castAdd 2 i)) a b c x y z

/-- The leaf-support condition is forced before the two noninvariant rows
are classified: their nonzero coordinate sums keep them out of the invariant
three-way-tie witness. -/
theorem sum_coefficients_zero_of_four_star_rows {m : ℕ} (net : Network 4 6 m) (a b c : ℝ)
    (hFirst : ∀ j : Fin 4, net.W₁ (Fin.castAdd 2 j)=
      PhysicalExtraction.liftRow (dictionary a b c j))
    (hFour : (∑ i,net.W₁ 4 i)≠0) (hFive : (∑ i,net.W₁ 5 i)≠0)
    (hmax : ∀ x,net.eval x=Maximum 4 x) : a+b+c=0 := by
  have h0 : net.W₁ 0 2 = -1 := by
    have he := congrFun (hFirst 0) 2
    change net.W₁ 0 2 = -(1:ℝ)-0-0 at he
    norm_num at he
    exact he
  have h1 : net.W₁ 1 2 = -1 := by
    have he := congrFun (hFirst 1) 2
    change net.W₁ 1 2 = -(0:ℝ)-1-0 at he
    norm_num at he
    exact he
  have h2 : net.W₁ 2 2 = -1 := by
    have he := congrFun (hFirst 2) 2
    change net.W₁ 2 2 = -(0:ℝ)-0-1 at he
    norm_num at he
    exact he
  have h3 : net.W₁ 3 2 = -a-b-c := by
    have he := congrFun (hFirst 3) 2
    change net.W₁ 3 2 = -a-b-c at he
    exact he
  obtain ⟨j,hjSum,hj,_⟩ := network_invariant_row_omits_coordinate net hmax 2
  fin_cases j
  · change net.W₁ 0 2=0 at hj
    linarith only [h0,hj]
  · change net.W₁ 1 2=0 at hj
    linarith only [h1,hj]
  · change net.W₁ 2 2=0 at hj
    linarith only [h2,hj]
  · change net.W₁ 3 2=0 at hj
    linarith only [h3,hj]
  · exact (hFour hjSum).elim
  · exact (hFive hjSum).elim

/-- Exactness itself forces the fourth star row to be supported on the three
leaves. Otherwise every first preactivation is strict at a three-way top tie. -/
theorem sum_coefficients_zero_of_exact {m : ℕ} (net : Network 4 6 m) (a b c : ℝ)
    (hRows : net.W₁=firstRows a b c) (hmax : ∀ x, net.eval x=Maximum 4 x) :
    a+b+c=0 := by
  obtain ⟨j,_,hj,_⟩ := network_invariant_row_omits_coordinate net hmax 2
  rw [hRows] at hj
  fin_cases j
  · change (-(1:ℝ)-0-0)=0 at hj
    norm_num at hj
  · change (-(0:ℝ)-1-0)=0 at hj
    norm_num at hj
  · change (-(0:ℝ)-0-1)=0 at hj
    norm_num at hj
  · change -a-b-c=0 at hj
    linarith only [hj]
  · change (1:ℝ)=0 at hj
    norm_num at hj
  · change (-1:ℝ)=0 at hj
    norm_num at hj

/-- No actual width-(6,5) network with these first rows computes Max4.
All original biases and all second-layer/output coefficients are arbitrary. -/
theorem network_excluded (net : Network 4 6 5) (a b c : ℝ)
    (habc : a+b+c=0) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hRows : net.W₁ = firstRows a b c) :
    ¬ ∀ x, net.eval x = Maximum 4 x := by
  classical
  intro hmax
  obtain ⟨S,hS,R,hR⟩ := PhysicalExtraction.physical_residual_at_most_three net
    (dictionary a b c) hRows hmax
  let d : ResidualSystem S :=
    ⟨R 0,R 1,R 2,R 3,(fun j => net.w₃ j),
      (fun j => net.W₂ j 0),(fun j => net.W₂ j 1),
      (fun j => net.W₂ j 2),(fun j => net.W₂ j 3)⟩
  have hRep : d.Represents a b c := by
    intro x y z
    have hh := hR ![x,y,z]
    rw [feature_linear_combination] at hh
    simp_rw [invariantPart_dictionary] at hh
    change target x y z = _ at hh
    change target x y z = form a b c (R 0) (R 1) (R 2) (R 3) x y z +
      ∑ j : S, net.w₃ j.val * relu (form a b c (net.W₂ j.val 0)
        (net.W₂ j.val 1) (net.W₂ j.val 2) (net.W₂ j.val 3) x y z)
    rw [Finset.sum_coe_sort S (fun j => net.w₃ j * relu (form a b c
      (net.W₂ j 0) (net.W₂ j 1) (net.W₂ j 2) (net.W₂ j 3) x y z))]
    exact hh
  have hFour := d.card_ge_four a b c habc ha hb hc hRep
  rw [Fintype.card_coe] at hFour
  linarith only [hS,hFour]

/-- The zero-sum leaf condition need not be assumed in the actual-network
exclusion: it follows from local odd linearity. -/
theorem network_excluded_genuine (net : Network 4 6 5) (a b c : ℝ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hRows : net.W₁=firstRows a b c) :
    ¬ ∀ x, net.eval x=Maximum 4 x := by
  intro hmax
  exact network_excluded net a b c
    (sum_coefficients_zero_of_exact net a b c hRows hmax) ha hb hc hRows hmax

/-- Exactness forces the fourth invariant row to be a scalar multiple of a
leaf comparison: its three leaf coefficients sum to zero and at least one vanishes. -/
theorem fourth_row_leaf_comparison_of_exact (net : Network 4 6 5) (a b c : ℝ)
    (hRows : net.W₁=firstRows a b c) (hmax : ∀ x, net.eval x=Maximum 4 x) :
    a+b+c=0 ∧ (a=0 ∨ b=0 ∨ c=0) := by
  refine ⟨sum_coefficients_zero_of_exact net a b c hRows hmax,?_⟩
  by_contra hn
  push_neg at hn
  exact network_excluded_genuine net a b c hn.1 hn.2.1 hn.2.2 hRows hmax

/-- The genuine star-nonroot first matrix, allowing exactly the permitted
positive row scalings and hidden/input permutations. -/
def FirstMatrixForm (net : Network 4 6 5) (a b c : ℝ) : Prop :=
  ∃ s : Fin 6 → ℝ, (∀ j, 0 < s j) ∧
    ∃ p : Equiv.Perm (Fin 6), ∃ q : Equiv.Perm (Fin 4),
      ∀ j i, net.W₁ j i = s j * firstRows a b c (p j) (q i)

/-- The excluded sector is empty under the full stated scaling/permutation
conventions. The original network may have arbitrary real biases. -/
theorem network_excluded_firstMatrixForm (net : Network 4 6 5) (a b c : ℝ)
    (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hRows : FirstMatrixForm net a b c) :
    ¬ ∀ x, net.eval x = Maximum 4 x := by
  classical
  intro hmax
  obtain ⟨s,hs,p,q,hW⟩ := hRows
  let n₁ := scaleFirst net (fun j => 1/s j)
  let n₂ := permuteHidden n₁ p.symm (Equiv.refl (Fin 5))
  let n₃ := permuteInputs n₂ q.symm
  have hmax₁ : ∀ x, n₁.eval x = Maximum 4 x := by
    intro x
    rw [scaleFirst_eval net (fun j => 1/s j) (fun j => one_div_pos.mpr (hs j)),hmax]
  have hmax₂ : ∀ x, n₂.eval x = Maximum 4 x := by
    intro x
    rw [permuteHidden_eval n₁ p.symm (Equiv.refl (Fin 5)),hmax₁]
  have hmax₃ : ∀ x, n₃.eval x = Maximum 4 x := by
    intro x
    rw [permuteInputs_eval n₂ q.symm,hmax₂,maximum_permute]
  have hfirst : n₃.W₁ = firstRows a b c := by
    funext j i
    dsimp only [n₃,n₂,n₁,permuteInputs,permuteHidden,scaleFirst]
    rw [hW]
    simp only [q.apply_symm_apply,p.apply_symm_apply]
    have hn : s (p.symm j) ≠ 0 := ne_of_gt (hs (p.symm j))
    field_simp [hn] <;> ring
  exact network_excluded_genuine n₃ a b c ha hb hc hfirst hmax₃

/-- The first-matrix hypotheses describe a genuine nonempty parameter family;
only the demanded exact Max4 completion is impossible. -/
theorem firstMatrixForm_nonempty : ∃ net : Network 4 6 5,
    FirstMatrixForm net 1 1 (-2) := by
  let net : Network 4 6 5 :=
    ⟨firstRows 1 1 (-2),0,0,0,0,0⟩
  refine ⟨net,(fun _ => 1),(by intro j; norm_num),Equiv.refl _,Equiv.refl _,?_⟩
  intro j i
  simp only [net,Equiv.refl_apply,one_mul]

#check @ResidualSystem.card_ge_four
#check @network_excluded
#check @fourth_row_leaf_comparison_of_exact
#check @network_excluded_genuine
#check @network_excluded_firstMatrixForm
#print axioms ResidualSystem.card_ge_four
#print axioms network_excluded
#print axioms fourth_row_leaf_comparison_of_exact
#print axioms network_excluded_genuine
#print axioms network_excluded_firstMatrixForm
end MaxCaterpillar.Fiber.Count65.StarNonroot
