import MaxCaterpillar.Frontier.RandomRestriction.NormalizedNetwork.Model

/-! # A genuine surviving neuron with a tail-order-dependent modular offset

This isolated research leaf proves a boundary of the fixed-quadratic transfer.
It neither asserts a lower bound nor assumes an unavailable certificate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace MaxCaterpillar.Frontier.RandomRestriction.ExponentialPush
open BigOperators

/-- Every original homogeneous second preactivation has a fixed global odd part.
Its localized odd part can nevertheless depend on the localization point. -/
theorem original_inner_odd_part {N h₁ h₂ : ℕ}
    (net : NormalizedNetwork N h₁ h₂) (k : Fin h₂) (x : Point N) :
    net.inner k x-net.inner k (-x)=
      2*lin (net.U k) x+∑j,net.W k j*lin (net.A j) x := by
  have hs : (∑ j,net.W k j*relu (lin (net.A j) x))-
      (∑ j,net.W k j*relu (-lin (net.A j) x))=
      ∑ j,net.W k j*lin (net.A j) x := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [←mul_sub,relu_sub_relu_neg]
  simp only [NormalizedNetwork.inner,lin_neg_right]
  linarith only [hs]

/-- The first row is genuinely support four; the second row is a difference. -/
noncomputable def offsetNet : NormalizedNetwork 9 2 1 where
  A := ![![1,-1,1,-1,0,0,0,0,0], ![0,0,1,-1,0,0,0,0,0]]
  U := fun _=>0
  W := fun _=>![1,-1]
  L := ![1,0,0,0,0,0,0,0,0]
  B := fun _=>0
  d := fun _=>1

/-- Seven selected coordinates are literally tied at zero. -/
def selectedSeven : Finset (Fin 9) := (Finset.univ.erase 2).erase 3
noncomputable def qPlus : Point 9 := fun i=>if i=2 then -1 else if i=3 then -3 else 0
noncomputable def qMinus : Point 9 := fun i=>if i=2 then -3 else if i=3 then -1 else 0

lemma offsetNet_inner (x : Point 9) : offsetNet.inner 0 x=
    relu (x 0-x 1+x 2-x 3)-relu (x 2-x 3) := by
  simp [NormalizedNetwork.inner,offsetNet,lin,Fin.sum_univ_succ]
  congr 1 <;> congr 1
  change x 0+(-x 1+(x 2+ -x 3))=x 0-x 1+x 2-x 3
  ring

lemma offsetNet_normalized : offsetNet.TranslationNormalized := by
  constructor
  · intro j
    fin_cases j <;> norm_num [offsetNet,Fin.sum_univ_succ]
  constructor
  · intro k
    simp [offsetNet]
  · norm_num [offsetNet,Fin.sum_univ_succ]

lemma selectedSeven_card : selectedSeven.card=7 := by decide

lemma tied_and_negative :
    (∀i∈selectedSeven,qPlus i=0 ∧ qMinus i=0) ∧
    (∀i∉selectedSeven,qPlus i<0 ∧ qMinus i<0) := by
  constructor
  · intro i hi
    have hi3 := (Finset.mem_erase.mp hi).1
    have hi2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [qPlus,qMinus,hi2,hi3]
  · intro i hi
    have he : i=2 ∨ i=3 := by
      by_contra h
      push_neg at h
      exact hi (by simp [selectedSeven,h.1,h.2])
    rcases he with rfl|rfl
    · change (-1:ℝ)<0 ∧ (-3:ℝ)<0
      norm_num
    · change (-3:ℝ)<0 ∧ (-1:ℝ)<0
      norm_num

lemma no_first_row_internal : ∀j,
    ¬NormalizedNetwork.rowSupport (offsetNet.A j)⊆selectedSeven := by
  intro j hj
  have hz : (2 : Fin 9)∈NormalizedNetwork.rowSupport (offsetNet.A j) := by
    fin_cases j <;> norm_num [NormalizedNetwork.mem_rowSupport,offsetNet]
  have hf := hj hz
  simpa [selectedSeven] using hf

lemma both_actual_survive : offsetNet.inner 0 qPlus=0 ∧ offsetNet.inner 0 qMinus=0 := by
  rw [offsetNet_inner,offsetNet_inner]
  change (relu (0-0+(-1:ℝ)- -3)-relu ((-1:ℝ)- -3)=0) ∧
    (relu (0-0+(-3:ℝ)- -1)-relu ((-3:ℝ)- -1)=0)
  norm_num [relu]

/-- The actual active-gate derivative, before any local-model reduction. -/
noncomputable def actualGradient (q : Point 9) : Point 9 := fun i=>
  offsetNet.U 0 i+∑j,offsetNet.W 0 j*
    (if 0<lin (offsetNet.A j) q then offsetNet.A j i else 0)

lemma row0_linear_form (x : Point 9) :
    lin (offsetNet.A 0) x=x 0-x 1+x 2-x 3 := by
  simp [offsetNet,lin,Fin.sum_univ_succ]
  change x 0+(-x 1+(x 2+ -x 3))=x 0-x 1+x 2-x 3
  ring

lemma row1_linear_form (x : Point 9) :
    lin (offsetNet.A 1) x=x 2-x 3 := by
  simp [offsetNet,lin,Fin.sum_univ_succ]
  change x 2+ -x 3=x 2-x 3
  ring

lemma first_forms_plus : ∀j,lin (offsetNet.A j) qPlus=2 := by
  intro j
  fin_cases j
  · change lin (offsetNet.A 0) qPlus=2
    rw [row0_linear_form]
    change (0:ℝ)-0+ -1- -3=2
    norm_num
  · change lin (offsetNet.A 1) qPlus=2
    rw [row1_linear_form]
    change (-1:ℝ)- -3=2
    norm_num

lemma first_forms_minus : ∀j,lin (offsetNet.A j) qMinus= -2 := by
  intro j
  fin_cases j
  · change lin (offsetNet.A 0) qMinus= -2
    rw [row0_linear_form]
    change (0:ℝ)-0+ -3- -1= -2
    norm_num
  · change lin (offsetNet.A 1) qMinus= -2
    rw [row1_linear_form]
    change (-3:ℝ)- -1= -2
    norm_num

lemma actual_gradient_plus : actualGradient qPlus=![1,-1,0,0,0,0,0,0,0] := by
  funext i
  simp only [actualGradient,first_forms_plus]
  norm_num
  fin_cases i <;> norm_num [offsetNet,Fin.sum_univ_succ]

lemma actual_gradient_minus : actualGradient qMinus=0 := by
  funext i
  simp only [actualGradient,first_forms_minus]
  norm_num [offsetNet]

/-- Every actual tail derivative vanishes in both tail orders. -/
lemma every_tail_derivative_zero (i : Fin 9) (hi : i∉selectedSeven) :
    actualGradient qPlus i=0 ∧ actualGradient qMinus i=0 := by
  have he : i=2 ∨ i=3 := by
    by_contra h
    push_neg at h
    exact hi (by simp [selectedSeven,h.1,h.2])
  rw [actual_gradient_plus,actual_gradient_minus]
  rcases he with rfl|rfl <;> constructor <;> rfl

/-- In particular every prefix equation, and indeed every tail subset equation,
is exactly zero; it cannot force a fixed selected modular offset. -/
lemma every_tail_subset_sum_zero (T : Finset (Fin 9))
    (hT : ∀i∈T,i∉selectedSeven) :
    (∑i in T,actualGradient qPlus i)=0 ∧
    (∑i in T,actualGradient qMinus i)=0 := by
  constructor
  · exact Finset.sum_eq_zero (fun i hi=>(every_tail_derivative_zero i (hT i hi)).1)
  · exact Finset.sum_eq_zero (fun i hi=>(every_tail_derivative_zero i (hT i hi)).2)

/-- This is an actual neighborhood identity, not an assumed local model. -/
lemma local_plus (u v : ℝ) (h : |u-v|<2) :
    offsetNet.inner 0 ![u,v,-1,-3,0,0,0,0,0]=u-v := by
  rw [offsetNet_inner]
  change relu (u-v+ -1- -3)-relu ((-1:ℝ)- -3)=u-v
  have hpos : 0≤u-v+ -1- -3 := by have hh := (abs_lt.mp h).1; linarith
  rw [relu_of_nonneg hpos]
  norm_num [relu]
  ring

lemma local_minus (u v : ℝ) (h : |u-v|<2) :
    offsetNet.inner 0 ![u,v,-3,-1,0,0,0,0,0]=0 := by
  rw [offsetNet_inner]
  change relu (u-v+ -3- -1)-relu ((-3:ℝ)- -1)=0
  have hneg : u-v+ -3- -1≤0 := by have hh := (abs_lt.mp h).2; linarith
  rw [relu_of_nonpos hneg]
  norm_num [relu]

/-- Both actual localized preactivations have zero tail coefficients, but their
modular offsets differ on the selected coordinates. -/
lemma localized_offsets_differ :
    (∃u v : ℝ,|u-v|<2 ∧
      offsetNet.inner 0 ![u,v,-1,-3,0,0,0,0,0]≠
      offsetNet.inner 0 ![u,v,-3,-1,0,0,0,0,0]) := by
  refine ⟨1,0,by norm_num,?_⟩
  rw [local_plus 1 0 (by norm_num),local_minus 1 0 (by norm_num)]
  norm_num

#print axioms original_inner_odd_part
#print axioms offsetNet_normalized
#print axioms no_first_row_internal
#print axioms both_actual_survive
#print axioms actual_gradient_plus
#print axioms actual_gradient_minus
#print axioms every_tail_subset_sum_zero
#print axioms local_plus
#print axioms local_minus
#print axioms localized_offsets_differ
end MaxCaterpillar.Frontier.RandomRestriction.ExponentialPush
