import MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary.Orthant

/-! # Safe aggregation of the surviving negative anchor coordinates -/
set_option autoImplicit false
noncomputable section

namespace MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
open BigOperators Frontier BaselineFold
variable {m : ℕ}

def aggregateLeft (c t b e : ℝ) : ℝ := if c=0 then (1-t)*b+t*e else b
def aggregateRight (c t b e : ℝ) : ℝ := if c=0 then e else (1-t)*e+t*b
def retainedCoefficient (c b e : ℝ) : ℝ := if c=0 then e else b

@[simp] lemma aggregateLeft_zero (c b e : ℝ) : aggregateLeft c 0 b e=b := by
  unfold aggregateLeft
  split_ifs <;> ring

@[simp] lemma aggregateRight_zero (c b e : ℝ) : aggregateRight c 0 b e=e := by
  unfold aggregateRight
  split_ifs <;> ring

@[simp] lemma aggregateLeft_one (c b e : ℝ) :
    aggregateLeft c 1 b e=retainedCoefficient c b e := by
  unfold aggregateLeft retainedCoefficient
  split_ifs <;> ring

@[simp] lemma aggregateRight_one (c b e : ℝ) :
    aggregateRight c 1 b e=retainedCoefficient c b e := by
  unfold aggregateRight retainedCoefficient
  split_ifs <;> ring

lemma continuous_aggregateLeft (c b e : ℝ) :
    Continuous (fun t : ℝ => aggregateLeft c t b e) := by
  unfold aggregateLeft
  split_ifs <;> continuity

lemma continuous_aggregateRight (c b e : ℝ) :
    Continuous (fun t : ℝ => aggregateRight c t b e) := by
  unfold aggregateRight
  split_ifs <;> continuity

theorem aggregate_fit (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (a b e bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ThreeFit a b e bias weights θ c d) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    ThreeFit a (fun k => aggregateLeft c t (b k) (e k))
      (fun k => aggregateRight c t (b k) (e k)) bias weights θ c d := by
  intro R N M h
  rcases h with ⟨hR,hN,hM,hc,hd⟩
  by_cases hcz : c=0
  · have hdz : d≠0 := hcd.resolve_left (by intro hn; exact hn hcz)
    have hN0 := hc hcz
    have harg : ∀ k,
        a k*R+aggregateLeft c t (b k) (e k)*N+aggregateRight c t (b k) (e k)*M+bias k=
          a k*R+b k*((1-t)*N)+e k*(M+t*N)+bias k := by
      intro k
      simp only [aggregateLeft,aggregateRight,hcz,if_true]
      ring
    simp_rw [harg]
    rw [hfit R ((1-t)*N) (M+t*N)
      ⟨hR,mul_nonneg (sub_nonneg.mpr ht1) hN,
        add_nonneg hM (mul_nonneg ht0 hN),
        fun _ => by rw [hN0]; ring,fun hdz' => (hdz hdz').elim⟩]
    ring
  · have harg : ∀ k,
        a k*R+aggregateLeft c t (b k) (e k)*N+aggregateRight c t (b k) (e k)*M+bias k=
          a k*R+b k*(N+t*M)+e k*((1-t)*M)+bias k := by
      intro k
      simp only [aggregateLeft,aggregateRight,hcz,if_false]
      ring
    simp_rw [harg]
    rw [hfit R (N+t*M) ((1-t)*M)
      ⟨hR,add_nonneg hN (mul_nonneg ht0 hM),mul_nonneg (sub_nonneg.mpr ht1) hM,
        fun hcz' => (hcz hcz').elim,fun hd0 => by rw [hd hd0]; ring⟩]
    ring

theorem domainFit_of_threeFit (A B c d : ℝ) (hA : 0≤A) (hB : 0≤B)
    (a b e bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ThreeFit a b e bias weights θ c d) :
    DomainFit (fun k => liftThreeRow A B c d (a k) (b k) (e k))
      bias weights θ A B c d := by
  intro q r u v hq hr
  simp_rw [liftThreeRow_dot]
  rw [hfit _ _ _ ⟨totalPositive_nonneg A B c d q r u v hA hB hq hr,
    negativePiece_nonneg c u,negativePiece_nonneg d v,
    fun hc => by simp [negativePiece_eq_relu,hc,relu],
    fun hd => by simp [negativePiece_eq_relu,hd,relu]⟩]
  exact (target_three_coordinates A B c d q r u v).symm

def aggregateRows (A B c d : ℝ) (a b e : Fin m → ℝ) (t : ℝ) : Fin m → Fin 6 → ℝ :=
  fun k => liftThreeRow A B c d (a k) (aggregateLeft c t (b k) (e k))
    (aggregateRight c t (b k) (e k))

@[simp] lemma aggregateRows_zero (A B c d : ℝ) (a b e : Fin m → ℝ) :
    aggregateRows A B c d a b e 0=(fun k => liftThreeRow A B c d (a k) (b k) (e k)) := by
  funext k
  change liftThreeRow A B c d (a k) (aggregateLeft c 0 (b k) (e k))
    (aggregateRight c 0 (b k) (e k))=_
  rw [aggregateLeft_zero,aggregateRight_zero]

lemma continuous_aggregateRows (A B c d : ℝ) (a b e : Fin m → ℝ) :
    Continuous (aggregateRows A B c d a b e) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  have hl := continuous_aggregateLeft c (b k) (e k)
  have hr := continuous_aggregateRight c (b k) (e k)
  fin_cases j <;> simp only [aggregateRows,liftThreeRow,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] <;> continuity

def liftTwoRow (A B c d a b : ℝ) : Fin 6 → ℝ := liftThreeRow A B c d a b b

lemma liftTwoRow_dot (A B c d a b q r u v : ℝ) :
    (∑ j, liftTwoRow A B c d a b j*features q r u v j)=
      a*totalPositive A B c d q r u v+b*(negativePiece c u+negativePiece d v) := by
  rw [liftTwoRow,liftThreeRow_dot]
  ring

@[simp] lemma aggregateRows_one (A B c d : ℝ) (a b e : Fin m → ℝ) :
    aggregateRows A B c d a b e 1=
      (fun k => liftTwoRow A B c d (a k) (retainedCoefficient c (b k) (e k))) := by
  funext k
  change liftThreeRow A B c d (a k) (aggregateLeft c 1 (b k) (e k))
    (aggregateRight c 1 (b k) (e k))=liftThreeRow A B c d (a k)
      (retainedCoefficient c (b k) (e k)) (retainedCoefficient c (b k) (e k))
  rw [aggregateLeft_one,aggregateRight_one]

/-- At least one anchor coordinate survives. The endpoint therefore fits the
entire genuine quadrant, including both axes and the origin. -/
theorem quadrantFit_of_threeFit (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (a b bias weights : Fin m → ℝ) (θ : ℝ)
    (hfit : ThreeFit a b b bias weights θ c d)
    (R N : ℝ) (hR : 0≤R) (hN : 0≤N) :
    (∑ k, weights k*relu (a k*R+b k*N+bias k))+θ=R-N := by
  by_cases hc : c=0
  · have hd : d≠0 := hcd.resolve_left (by intro hn; exact hn hc)
    have hh := hfit R 0 N ⟨hR,le_rfl,hN,fun _ => rfl,fun hd' => (hd hd').elim⟩
    simpa only [mul_zero,add_zero,sub_zero] using hh
  · have hh := hfit R N 0 ⟨hR,hN,le_rfl,fun hc' => (hc hc').elim,fun _ => rfl⟩
    simpa only [mul_zero,add_zero,sub_zero] using hh

end MaxCaterpillar.Fiber.Count65.Paired.BaselineOrdinary
