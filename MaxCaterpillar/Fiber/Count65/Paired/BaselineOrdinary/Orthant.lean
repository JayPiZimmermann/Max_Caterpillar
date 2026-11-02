import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary.Coefficients

/-! # The ordinary fold endpoint and its genuine nonnegative coordinates

Zero anchor coefficients are explicitly suppressed. Surjectivity is first
stated on the corresponding restricted orthant, so no nonexistent coordinate
ray is silently introduced.
-/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold
variable {m : ℕ}

def positivePiece (c u : ℝ) : ℝ := relu c*relu u+relu (-c)*relu (-u)
def negativePiece (c u : ℝ) : ℝ := positivePiece (-c) u

lemma positivePiece_eq_relu (c u : ℝ) : positivePiece c u=relu (c*u) := by
  by_cases hc : c=0
  · subst c
    simp [positivePiece,relu]
  · by_cases hp : 0<c
    · simp only [positivePiece,relu_of_nonneg hp.le,
        relu_of_nonpos (neg_nonpos.mpr hp.le),zero_mul,add_zero]
      exact (relu_mul_pos hp u).symm
    · have hn : c<0 := lt_of_le_of_ne (le_of_not_gt hp) hc
      simp only [positivePiece,relu_of_nonpos hn.le,
        relu_of_nonneg (neg_nonneg.mpr hn.le),zero_mul,zero_add]
      rw [← relu_mul_pos (neg_pos.mpr hn),neg_mul_neg]

lemma negativePiece_eq_relu (c u : ℝ) : negativePiece c u=relu (-(c*u)) := by
  rw [negativePiece,positivePiece_eq_relu,neg_mul]

lemma negativePiece_formula (c u : ℝ) :
    negativePiece c u=relu (-c)*relu u+relu c*relu (-u) := by
  simp only [negativePiece,positivePiece,neg_neg]

lemma positivePiece_nonneg (c u : ℝ) : 0≤positivePiece c u := by
  rw [positivePiece_eq_relu]
  exact relu_nonneg _

lemma negativePiece_nonneg (c u : ℝ) : 0≤negativePiece c u := by
  rw [negativePiece_eq_relu]
  exact relu_nonneg _

lemma piece_difference (c u : ℝ) : positivePiece c u-negativePiece c u=c*u := by
  rw [positivePiece_eq_relu,negativePiece_eq_relu,relu_sub_relu_neg]

def negativeCoefficient (c x y : ℝ) : ℝ := if c=0 then 0 else if 0<c then y/c else x/(-c)

lemma negativeCoefficient_endpoint (c x y : ℝ) :
    positiveScale c 1*x=negativeCoefficient c x y*relu (-c) ∧
      negativeScale c 1*y=negativeCoefficient c x y*relu c := by
  by_cases hc : c=0
  · subst c
    simp [positiveScale,negativeScale,negativeCoefficient,relu]
  · by_cases hp : 0<c
    · simp [positiveScale,negativeScale,negativeCoefficient,hc,hp,
        relu_of_nonneg hp.le,relu_of_nonpos (neg_nonpos.mpr hp.le)]
    · have hn : c<0 := lt_of_le_of_ne (le_of_not_gt hp) hc
      simp [positiveScale,negativeScale,negativeCoefficient,hc,hp,
        relu_of_nonpos hn.le,relu_of_nonneg (neg_nonneg.mpr hn.le)]
      field_simp [hc]

def liftThreeRow (A B c d a b e : ℝ) : Fin 6 → ℝ :=
  ![a*A,a*B,a*relu c+b*relu (-c),a*relu (-c)+b*relu c,
    a*relu d+e*relu (-d),a*relu (-d)+e*relu d]

theorem positive_fold_endpoint (A B c d : ℝ) (hA : A≠0) (W : Fin 6 → ℝ) :
    positiveFoldRow A c d 1 (combineRow A B 1 W)=
      liftThreeRow A B c d (W 0/A) (negativeCoefficient c (W 2) (W 3))
        (negativeCoefficient d (W 4) (W 5)) := by
  funext j
  fin_cases j
  · change W 0=(W 0/A)*A
    field_simp [hA]
  · change (1-1)*W 1+1*(B/A)*W 0=(W 0/A)*B
    ring
  · change positiveScale c 1*W 2+1/A*W 0*relu c=
      (W 0/A)*relu c+negativeCoefficient c (W 2) (W 3)*relu (-c)
    rw [(negativeCoefficient_endpoint c (W 2) (W 3)).1]
    ring
  · change negativeScale c 1*W 3+1/A*W 0*relu (-c)=
      (W 0/A)*relu (-c)+negativeCoefficient c (W 2) (W 3)*relu c
    rw [(negativeCoefficient_endpoint c (W 2) (W 3)).2]
    ring
  · change positiveScale d 1*W 4+1/A*W 0*relu d=
      (W 0/A)*relu d+negativeCoefficient d (W 4) (W 5)*relu (-d)
    rw [(negativeCoefficient_endpoint d (W 4) (W 5)).1]
    ring
  · change negativeScale d 1*W 5+1/A*W 0*relu (-d)=
      (W 0/A)*relu (-d)+negativeCoefficient d (W 4) (W 5)*relu d
    rw [(negativeCoefficient_endpoint d (W 4) (W 5)).2]
    ring

def totalPositive (A B c d q r u v : ℝ) : ℝ :=
  A*q+B*r+positivePiece c u+positivePiece d v

lemma liftThreeRow_dot (A B c d a b e q r u v : ℝ) :
    (∑ j, liftThreeRow A B c d a b e j*features q r u v j)=
      a*totalPositive A B c d q r u v+b*negativePiece c u+e*negativePiece d v := by
  rw [dot_features]
  change a*A*q+a*B*r+(a*relu c+b*relu (-c))*relu u+
    (a*relu (-c)+b*relu c)*relu (-u)+(a*relu d+e*relu (-d))*relu v+
      (a*relu (-d)+e*relu d)*relu (-v)=_
  simp only [totalPositive,positivePiece,negativePiece_formula]
  ring

lemma totalPositive_nonneg (A B c d q r u v : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hq : 0≤q) (hr : 0≤r) :
    0≤totalPositive A B c d q r u v :=
  add_nonneg (add_nonneg (add_nonneg (mul_nonneg hA hq) (mul_nonneg hB hr))
    (positivePiece_nonneg _ _)) (positivePiece_nonneg _ _)

lemma target_three_coordinates (A B c d q r u v : ℝ) :
    A*q+B*r+c*u+d*v=totalPositive A B c d q r u v-negativePiece c u-negativePiece d v := by
  unfold totalPositive
  linarith only [piece_difference c u,piece_difference d v]

/-- The target vanishes in every missing negative-coordinate direction. -/
def RestrictedOrthant (c d R N M : ℝ) : Prop :=
  0≤R ∧ 0≤N ∧ 0≤M ∧ (c=0 → N=0) ∧ (d=0 → M=0)

def ThreeFit (a b e bias weights : Fin m → ℝ) (θ c d : ℝ) : Prop :=
  ∀ R N M : ℝ, RestrictedOrthant c d R N M →
    (∑ k, weights k*relu (a k*R+b k*N+e k*M+bias k))+θ=R-N-M

lemma pieces_negative_realization (c N : ℝ) (hN : 0≤N) (hz : c=0 → N=0) :
    positivePiece c (-N/c)=0 ∧ negativePiece c (-N/c)=N := by
  have hp : c*(-N/c)= -N := by
    by_cases hc : c=0
    · rw [hc,hz hc]
      simp
    · field_simp [hc]
      ring
  rw [positivePiece_eq_relu,negativePiece_eq_relu,hp,neg_neg,
    relu_of_nonpos (neg_nonpos.mpr hN),relu_of_nonneg hN]
  exact ⟨rfl,rfl⟩

theorem threeFit_of_domainFit (A B c d : ℝ) (hA : 0<A)
    (a b e bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : DomainFit (fun k => liftThreeRow A B c d (a k) (b k) (e k))
      bias weights θ A B c d) : ThreeFit a b e bias weights θ c d := by
  intro R N M h
  rcases h with ⟨hR,hN,hM,hc,hd⟩
  have hn := pieces_negative_realization c N hN hc
  have hm := pieces_negative_realization d M hM hd
  have hh := hfit (R/A) 0 (-N/c) (-M/d) (div_nonneg hR hA.le) le_rfl
  simp_rw [liftThreeRow_dot] at hh
  have hQ : totalPositive A B c d (R/A) 0 (-N/c) (-M/d)=R := by
    simp only [totalPositive,hn.1,hm.1,mul_zero,add_zero]
    field_simp [ne_of_gt hA]
    ring
  rw [target_three_coordinates,hQ,hn.2,hm.2] at hh
  exact hh

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
