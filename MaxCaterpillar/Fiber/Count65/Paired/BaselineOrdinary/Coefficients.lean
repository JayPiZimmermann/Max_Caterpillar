import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary.Domain

/-! # Safe coefficient substitutions for ordinary baselines

The first substitution combines two nonnegative increments. The second folds
positive anchor parts into the retained increment. A code coordinate whose
target coefficient is zero is suppressed on both sign half-lines.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold
variable {m : ℕ}

def combineRow (A B t : ℝ) (W : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![W 0,(1-t)*W 1+t*(B/A)*W 0,W 2,W 3,W 4,W 5]

lemma combineRow_dot (A B t : ℝ) (W : Fin 6 → ℝ) (q r u v : ℝ) :
    (∑ j, combineRow A B t W j*features q r u v j)=
      ∑ j, W j*features (q+t*(B/A)*r) ((1-t)*r) u v j := by
  rw [dot_features,dot_features]
  change W 0*q+((1-t)*W 1+t*(B/A)*W 0)*r+W 2*relu u+W 3*relu (-u)+
      W 4*relu v+W 5*relu (-v)=_
  ring

@[simp] lemma combineRow_zero (A B : ℝ) (W : Fin 6 → ℝ) : combineRow A B 0 W=W := by
  funext j
  fin_cases j <;> simp [combineRow] <;> rfl

lemma continuous_combineRow (A B : ℝ) (W : Fin 6 → ℝ) :
    Continuous (fun t : ℝ => combineRow A B t W) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [combineRow,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] <;> continuity

theorem combineRow_fit (A B c d : ℝ) (hA : 0<A) (hB : 0≤B)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : DomainFit C bias weights θ A B c d) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    DomainFit (fun k => combineRow A B t (C k)) bias weights θ A B c d := by
  intro q r u v hq hr
  simp_rw [combineRow_dot]
  rw [hfit _ _ u v (add_nonneg hq (mul_nonneg
    (mul_nonneg ht0 (div_nonneg hB hA.le)) hr))
    (mul_nonneg (sub_nonneg.mpr ht1) hr)]
  field_simp [ne_of_gt hA]
  ring

def positiveScale (c t : ℝ) : ℝ := if c=0 then 1-t else if 0<c then 1-t else 1
def negativeScale (c t : ℝ) : ℝ := if c=0 then 1-t else if 0<c then 1 else 1-t

lemma positiveScale_nonneg (c t : ℝ) (ht : t≤1) : 0≤positiveScale c t := by
  unfold positiveScale
  split_ifs <;> linarith

lemma negativeScale_nonneg (c t : ℝ) (ht : t≤1) : 0≤negativeScale c t := by
  unfold negativeScale
  split_ifs <;> linarith

@[simp] lemma positiveScale_zero (c : ℝ) : positiveScale c 0=1 := by
  unfold positiveScale
  split_ifs <;> ring

@[simp] lemma negativeScale_zero (c : ℝ) : negativeScale c 0=1 := by
  unfold negativeScale
  split_ifs <;> ring

lemma continuous_positiveScale (c : ℝ) : Continuous (fun t : ℝ => positiveScale c t) := by
  unfold positiveScale
  split_ifs <;> continuity

lemma continuous_negativeScale (c : ℝ) : Continuous (fun t : ℝ => negativeScale c t) := by
  unfold negativeScale
  split_ifs <;> continuity

def foldCoordinate (c t u : ℝ) : ℝ := positiveScale c t*relu u-negativeScale c t*relu (-u)

lemma foldCoordinate_relu (c t u : ℝ) (ht : t≤1) :
    relu (foldCoordinate c t u)=positiveScale c t*relu u ∧
      relu (-foldCoordinate c t u)=negativeScale c t*relu (-u) := by
  have hp := positiveScale_nonneg c t ht
  have hn := negativeScale_nonneg c t ht
  rcases le_total 0 u with hu|hu
  · have hu' : -u≤0 := neg_nonpos.mpr hu
    simp only [foldCoordinate,relu_of_nonneg hu,relu_of_nonpos hu',mul_zero,sub_zero]
    rw [relu_of_nonneg (mul_nonneg hp hu),relu_of_nonpos (neg_nonpos.mpr (mul_nonneg hp hu))]
    exact ⟨rfl,rfl⟩
  · have hu' : 0≤-u := neg_nonneg.mpr hu
    simp only [foldCoordinate,relu_of_nonpos hu,relu_of_nonneg hu',mul_zero,zero_sub]
    rw [relu_of_nonpos (neg_nonpos.mpr (mul_nonneg hn hu')),neg_neg,
      relu_of_nonneg (mul_nonneg hn hu')]
    exact ⟨rfl,rfl⟩

lemma foldCoordinate_target (c t u : ℝ) :
    c*foldCoordinate c t u=c*u-t*(relu c*relu u+relu (-c)*relu (-u)) := by
  by_cases hc : c=0
  · subst c
    simp [relu]
  · by_cases hp : 0<c
    · simp only [foldCoordinate,positiveScale,negativeScale,hc,if_false,hp,if_true,
        relu_of_nonneg hp.le,relu_of_nonpos (neg_nonpos.mpr hp.le),zero_mul,add_zero]
      linear_combination c*(relu_sub_relu_neg u)
    · have hn : c<0 := lt_of_le_of_ne (le_of_not_gt hp) hc
      simp only [foldCoordinate,positiveScale,negativeScale,hc,if_false,hp,
        relu_of_nonpos hn.le,relu_of_nonneg (neg_nonneg.mpr hn.le),zero_mul,zero_add]
      linear_combination c*(relu_sub_relu_neg u)

def positiveFoldRow (A c d t : ℝ) (W : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![W 0,W 1,
    positiveScale c t*W 2+t/A*W 0*relu c,
    negativeScale c t*W 3+t/A*W 0*relu (-c),
    positiveScale d t*W 4+t/A*W 0*relu d,
    negativeScale d t*W 5+t/A*W 0*relu (-d)]

lemma positiveFoldRow_dot (A c d t : ℝ) (ht : t≤1) (W : Fin 6 → ℝ)
    (q r u v : ℝ) :
    (∑ j, positiveFoldRow A c d t W j*features q r u v j)=
      ∑ j, W j*features (q+t/A*positiveAnchor c d u v) r
        (foldCoordinate c t u) (foldCoordinate d t v) j := by
  rw [dot_features,dot_features]
  change W 0*q+W 1*r+(positiveScale c t*W 2+t/A*W 0*relu c)*relu u+
    (negativeScale c t*W 3+t/A*W 0*relu (-c))*relu (-u)+
    (positiveScale d t*W 4+t/A*W 0*relu d)*relu v+
    (negativeScale d t*W 5+t/A*W 0*relu (-d))*relu (-v)=_
  rw [(foldCoordinate_relu c t u ht).1,(foldCoordinate_relu c t u ht).2,
    (foldCoordinate_relu d t v ht).1,(foldCoordinate_relu d t v ht).2]
  unfold positiveAnchor
  ring

@[simp] lemma positiveFoldRow_zero (A c d : ℝ) (W : Fin 6 → ℝ) :
    positiveFoldRow A c d 0 W=W := by
  funext j
  fin_cases j <;> simp [positiveFoldRow] <;> rfl

lemma continuous_positiveFoldRow (A c d : ℝ) (W : Fin 6 → ℝ) :
    Continuous (fun t : ℝ => positiveFoldRow A c d t W) := by
  apply continuous_pi
  intro j
  have hpc := continuous_positiveScale c
  have hnc := continuous_negativeScale c
  have hpd := continuous_positiveScale d
  have hnd := continuous_negativeScale d
  fin_cases j <;> simp only [positiveFoldRow,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons] <;> continuity

theorem positiveFoldRow_fit (A B c d : ℝ) (hA : 0<A)
    (C : Fin m → Fin 6 → ℝ) (bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : DomainFit C bias weights θ A B c d) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    DomainFit (fun k => positiveFoldRow A c d t (C k)) bias weights θ A B c d := by
  intro q r u v hq hr
  simp_rw [positiveFoldRow_dot A c d t ht1]
  rw [hfit _ r _ _ (add_nonneg hq (mul_nonneg (div_nonneg ht0 hA.le)
    (positiveAnchor_nonneg _ _ _ _))) hr]
  rw [foldCoordinate_target,foldCoordinate_target]
  unfold positiveAnchor
  field_simp [ne_of_gt hA]
  ring

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
